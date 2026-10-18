#!/usr/bin/env python3
"""C.U.R.E. vault self-repair: link availability check & retirement.

Walks every platform page under CURE/CURE/Creators/<Name>/<Platform>.md and
checks every media link (table rows and ## Compilation bullets) against its
portal. Links that are dead (invalid URL, HTTP 404/410, portal reports the
media as removed) or private (exists but not viewable without authorization)
are MOVED out of the main table into a `## Retired` section below it:

    ## Retired

    | Link | TS | Reason   |
    | ---- | -- | -------- |
    | ...  |    | (dead)   |
    | ...  |    | (private)|

Compilation bullets get the same treatment via a `(dead)`/`(private)`
annotation inside the Retired section. If a link that was retired earlier is
available again, it is automatically moved back (TS preserved).

Safety: nothing is ever downloaded. The script only requests small page/
oEmbed/API endpoints, caps every response body at ~300 KB and uses HEAD for
anything that looks like a media file. Transient network errors NEVER retire a
link — only definitive portal answers do; unverifiable links stay untouched
and are listed as "unknown" in the report.

Results are cached in .linkcheck_cache.json next to this script, so repeated
runs are cheap (available: 30 d, unavailable: 3 d, unknown: 12 h).

Usage:
    python3 self_repair.py [--dry-run] [--force] [--workers N] [--verbose]
"""
import argparse
import concurrent.futures as cf
import http.client
import json
import os
import re
import socket
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

# ----------------------------------------------------------------- constants

SCRIPT_DIR = Path(__file__).resolve().parent
VAULT = SCRIPT_DIR.parent / "CURE" / "Creators"
CACHE_FILE = SCRIPT_DIR / ".linkcheck_cache.json"

UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")
MAX_BYTES = 300_000
TIMEOUT = 12

AVAILABLE, PRIVATE, GONE, UNKNOWN = "available", "private", "gone", "unknown"
REASON = {PRIVATE: "(private)", GONE: "(dead)", "invalid": "(invalid)"}
MEDIA_EXT = re.compile(
    r"\.(mp4|m4v|mov|webm|mkv|avi|ts|m3u8|flv|wmv|mpd|mp3|m4a)$", re.I)

VERBOSE = [False]

URL_RE = re.compile(r"https?://[^\s|]+")
TABLE_ROW_RE = re.compile(r"^\|(.+)\|\s*$")

# ---- TS / dedupe helpers (semantics identical to bff/fill_cure.py) ---------

TS_TOKEN_RE = re.compile(r"(\d{1,2}:\d{2}(?::\d{2})?)")


def ts_seconds(tok):
    m = TS_TOKEN_RE.search(tok)
    if not m:
        return None
    s = 0
    for p in [int(x) for x in m.group(1).split(":")]:
        s = s * 60 + p
    return s


def split_ts(ts):
    if not ts:
        return []
    return [t.strip() for t in ts.split(",") if t.strip()]


def sort_ts(ts):
    toks = split_ts(ts)
    return ", ".join(sorted(toks, key=lambda t: (ts_seconds(t) if ts_seconds(t) is not None else 10**9, t)))


def merge_ts(existing, add, tolerance=2):
    toks = split_ts(existing)
    for t in split_ts(add):
        if t in toks:
            continue
        sec = ts_seconds(t)
        dup = any(ts_seconds(e) is not None and sec is not None
                  and abs(ts_seconds(e) - sec) <= tolerance for e in toks)
        if not dup:
            toks.append(t)
    return sort_ts(", ".join(toks))


def _clean_qs(url, keep=()):
    try:
        parts = urllib.parse.urlparse(url)
    except ValueError:
        return url
    qs = urllib.parse.parse_qs(parts.query, keep_blank_values=True)
    kept = {k: v for k, v in qs.items() if k in keep}
    new_q = "&".join(f"{k}={v[0]}" for k, v in kept.items())
    netloc = re.sub(r"^(www|m|mobile)\.", "", parts.netloc.lower())
    return f"{parts.scheme}://{netloc}{parts.path}{'?' + new_q if new_q else ''}"


def media_key(url):
    """Stable identity key of a media link (same semantics as fill_cure.link_key)."""
    try:
        parts = urllib.parse.urlparse(url)
    except ValueError:
        return None
    host = parts.netloc.lower().replace("www.", "").replace("m.", "")
    path = urllib.parse.unquote(parts.path)
    qs = urllib.parse.parse_qs(parts.query)

    def vid():
        if "v" in qs:
            return qs["v"][0]
        m = re.match(r"/(?:embed|shorts|live)?/?([\w-]{6,})", path)
        return m.group(1) if m else None

    if "youtu" in host:
        v = vid()
        return ("yt", v) if v else None
    if "twitch" in host:
        if "clips.twitch.tv" in host:
            return ("twclip", path.strip("/"))
        m2 = re.search(r"clip/([\w\-]+)", path)
        if m2:
            return ("twclip", m2.group(1))
        m3 = re.search(r"videos/(\d+)", path)
        if m3:
            return ("twvod", m3.group(1))
        return ("tw", path.strip("/"))
    if "tiktok" in host:
        m = re.search(r"/video/(\d+)", path)
        if m:
            return ("tt", m.group(1))
        return ("tt", path.strip("/"))
    if "bilibili" in host:
        m = re.search(r"video/(BV\w+)", path)
        if m:
            p = qs.get("p", [None])[0]
            key_p = p if p and p != "1" else None
            return ("bl", m.group(1), key_p)
        return ("bl", path)
    if "twitter" in host or host == "x.com":
        m = re.search(r"/status(?:es)?/(\d+)", path)
        return ("x", m.group(1)) if m else None
    if "instagram" in host:
        m = re.search(r"/(p|reel|tv|s)/([\w]+)", path)
        return ("ig", m.group(1) + "/" + m.group(2)) if m else None
    if "fb.watch" in host:
        return ("fb", path.strip("/"))
    return ("url", _clean_qs(url))


# ----------------------------------------------------------------- transport

class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


_OPENER = urllib.request.build_opener()
_OPENER_NOREDIR = urllib.request.build_opener(_NoRedirect())


def _open(url, method="GET", follow=True, timeout=TIMEOUT, extra=None,
          max_bytes=MAX_BYTES):
    """Return (status, body_bytes, final_url, headers). status None = network error."""
    headers = {"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"}
    if extra:
        headers.update(extra)
    req = urllib.request.Request(url, method=method, headers=headers)
    opener = _OPENER if follow else _OPENER_NOREDIR
    try:
        with opener.open(req, timeout=timeout) as r:
            body = b"" if method == "HEAD" else r.read(max_bytes)
            return r.status, body, r.geturl(), r.headers
    except urllib.error.HTTPError as e:
        body = b"" if method == "HEAD" else e.read(max_bytes)
        return e.code, body, e.geturl() or url, e.headers
    except (urllib.error.URLError, socket.timeout, ConnectionError,
            http.client.HTTPException, OSError):
        return None, b"", url, None


def resolve(url):
    """Follow redirect chain manually (never reads a body) -> final URL.
    Returns None on network failure (caller must not conclude anything)."""
    cur = url
    for _ in range(6):
        code, _, final, headers = _open(cur, "GET", follow=False, timeout=10)
        if code is None:
            return None
        if code in (301, 302, 303, 307, 308):
            loc = headers.get("Location") if headers else None
            if not loc:
                return cur
            cur = urllib.parse.urljoin(cur, loc)
            continue
        return final
    return cur


# ----------------------------------------------------------------- checkers

def _yt_id(url):
    p = urllib.parse.urlparse(url)
    q = urllib.parse.parse_qs(p.query)
    if "youtu" in p.netloc.lower():
        if "v" in q:
            return q["v"][0]
        m = re.match(r"/(?:shorts|live|embed)/([\w-]{6,})", p.path)
        if m:
            return m.group(1)
        # youtu.be/<id> short form
        m = re.match(r"/([\w-]{6,})/?$", p.path)
        if m:
            return m.group(1)
    return None


def _check_youtube(url):
    vid = _yt_id(url)
    if not vid:
        return UNKNOWN
    watch = f"https://www.youtube.com/watch?v={vid}"
    oe = f"https://www.youtube.com/oembed?url={urllib.parse.quote(watch, safe='')}&format=json"
    code, body, _, _ = _open(oe, timeout=10)
    if code == 200:
        return AVAILABLE
    if code is None:
        return UNKNOWN
    # oEmbed says no: private(401) vs embed-disabled(401) vs gone(404).
    # Ask the watch page for a definitive answer; markers sit deep in the
    # page, so allow a larger read cap here (only the rare non-200 path).
    code2, page, _, _ = _open(watch, timeout=20, max_bytes=1_500_000)
    if code2 == 404:
        return GONE
    if code2 is not None and page:
        low = page.lower()
        if b"you're not a bot" in low or b"sign in to confirm you're not" in low:
            return UNKNOWN
        if b"this video is private" in low or b"sign in to confirm your age" in low:
            return PRIVATE
        if b"video unavailable" in low or b"video removed" in low \
                or b"this video is unavailable" in low:
            return GONE
        m = re.search(rb'"playabilityStatus":\{"status":"(\w+)"', page)
        if m:
            st = m.group(1)
            if st == b"OK":
                return AVAILABLE
            if st == b"LOGIN_REQUIRED":
                return PRIVATE
            return GONE
    # page inconclusive -> trust the oEmbed code
    if code == 404:
        return GONE
    if code == 401:
        return PRIVATE
    return UNKNOWN


def _check_tiktok(url):
    low = url.lower()
    if "vm.tiktok.com" in low or "/t/" in low:
        # short links must resolve to a canonical @user/video URL; an expired
        # short link lands on a generic page (= dead link), a network failure
        # resolves to None (= no conclusion).
        final = resolve(url)
        if final is None:
            return UNKNOWN
        m = re.search(r"(@[\w.\-]+/video/\d+)", final, re.I)
        if not m:
            return GONE
        url = f"https://www.tiktok.com/{m.group(1)}"
    else:
        # the portal only serves oEmbed for the canonical www.tiktok.com form
        m = re.search(r"(@[\w.\-]+/video/\d+)", url, re.I)
        if m:
            url = f"https://www.tiktok.com/{m.group(1)}"
        else:
            return UNKNOWN
    code, body, _, _ = _open(
        f"https://www.tiktok.com/oembed?url={urllib.parse.quote(url, safe='')}",
        timeout=10)
    if code == 200:
        return AVAILABLE
    if code is None:
        return UNKNOWN
    if code == 429 or code >= 500:
        return UNKNOWN
    if code in (400, 404):
        return GONE
    return UNKNOWN


def _check_bilibili(url):
    if "b23.tv" in url.lower():
        url = resolve(url)
    p = urllib.parse.urlparse(url)
    m = re.search(r"/video/(BV[\w]+)", p.path, re.I)
    q = "bvid=" + m.group(1) if m else None
    if not q:
        m = re.search(r"/video/av(\d+)", p.path, re.I)
        if m:
            q = "aid=" + m.group(1)
    if not q:
        return UNKNOWN
    code, body, _, _ = _open(f"https://api.bilibili.com/x/web-interface/view?{q}",
                             timeout=10, extra={"Referer": "https://www.bilibili.com/"})
    if code != 200 or not body:
        return UNKNOWN
    try:
        c = json.loads(body).get("code")
    except (ValueError, AttributeError):
        return UNKNOWN
    if c == 0:
        return AVAILABLE
    if c in (-404, 62002, 62004):
        return GONE
    # -403/-412/-352 = portal risk control; plain page is a JS shell with no
    # usable markers, so without a definitive API answer we never retire.
    return UNKNOWN


def _check_twitter(url):
    m = re.search(r"/status(?:es)?/(\d+)", url)
    if not m:
        return UNKNOWN
    code, body, _, _ = _open(
        f"https://cdn.syndication.twimg.com/tweet-result?id={m.group(1)}&lang=en",
        timeout=10)
    if code == 200 and body:
        try:
            data = json.loads(body)
        except ValueError:
            return UNKNOWN
        if isinstance(data, dict) and (data.get("text") or data.get("id_str")):
            return AVAILABLE
        # the endpoint is token-gated these days and answers `{}` for
        # everything -> no conclusion, never conclude "gone" from it
        return UNKNOWN
    if code == 404 and body.strip() == b"Not found":
        return GONE
    return UNKNOWN


_TWITCH_DEAD = (b"this clip is no longer available", b"no longer available",
                b"content is unavailable", b"this video is unavailable",
                b"has been removed", b"video was deleted")


def _check_twitch(url):
    p = urllib.parse.urlparse(url)
    page = f"https://www.twitch.tv{p.path}" if "clips.twitch.tv" in p.netloc.lower() \
        else url
    code, body, final, _ = _open(page)
    if code is None:
        return UNKNOWN
    if code == 404:
        return GONE
    if code != 200:
        return UNKNOWN
    low = body.lower()
    if any(m in low for m in _TWITCH_DEAD):
        return GONE
    if b"twitch" in low and (b"<title" in low or b"__NEXT_DATA__" in low):
        return AVAILABLE
    return UNKNOWN


def _check_instagram(url):
    code, _, final, _ = _open(url)
    if code is None:
        return UNKNOWN
    if code in (404, 410):
        return GONE
    if final and "/accounts/login" in urllib.parse.urlparse(final).path:
        return UNKNOWN
    if code == 200:
        return AVAILABLE
    return UNKNOWN


def _check_nicovideo(url):
    m = re.search(r"/watch/((?:sm|nm|so|user/\d+)?\w*\d+)", url)
    if not m:
        return UNKNOWN
    code, body, _, _ = _open(f"https://ext.nicovideo.jp/api/getthumbinfo/{m.group(1)}",
                             timeout=10)
    if code != 200 or not body:
        return UNKNOWN
    if b"<thumb" in body:
        return AVAILABLE
    if b"<error" in body:
        return GONE
    return UNKNOWN


def _check_drive(url):
    code, body, _, _ = _open(url)
    if code is None:
        return UNKNOWN
    if code in (404, 410):
        return GONE
    if code == 200 and body:
        low = body.lower()
        if b"you need access" in low or b"request access" in low:
            return PRIVATE
        return AVAILABLE
    return UNKNOWN


def _check_facebook(url):
    final = resolve(url) if "fb.watch" in url.lower() else url
    code, body, _, _ = _open(final)
    if code is None:
        return UNKNOWN
    if code in (404, 410):
        return GONE
    if code == 200 and body and b"content isn&#039;t available" in body.lower():
        return GONE
    return UNKNOWN


def _check_generic(url):
    if MEDIA_EXT.search(urllib.parse.urlparse(url).path):
        code, _, _, _ = _open(url, method="HEAD")
    else:
        code, body, _, _ = _open(url)
    if code is None:
        return UNKNOWN
    if code in (404, 410):
        return GONE
    if code == 200:
        return AVAILABLE
    return UNKNOWN


def check_url(url):
    """Classify one URL -> AVAILABLE | PRIVATE | GONE | UNKNOWN. Never downloads."""
    p = urllib.parse.urlparse(url)
    if p.scheme not in ("http", "https") or not p.netloc:
        return "invalid"
    host = p.netloc.lower().removeprefix("www.").removeprefix("m.")
    if "youtu" in host:
        return _check_youtube(url)
    if "tiktok" in host:
        return _check_tiktok(url)
    if "bilibili" in host or "b23.tv" in host:
        return _check_bilibili(url)
    if "twitter" in host or host in ("x.com", "mobile.x.com"):
        return _check_twitter(url)
    if "twitch" in host:
        return _check_twitch(url)
    if "instagram" in host:
        return _check_instagram(url)
    if "nicovideo" in host:
        return _check_nicovideo(url)
    if "drive.google" in host:
        return _check_drive(url)
    if "facebook" in host or "fb.watch" in host:
        return _check_facebook(url)
    return _check_generic(url)


# ----------------------------------------------------------------- cache

TTL = {AVAILABLE: 30 * 86400, PRIVATE: 3 * 86400, GONE: 3 * 86400,
       "invalid": 30 * 86400, UNKNOWN: 12 * 3600}
_cache = {}


def load_cache():
    try:
        _cache.update(json.loads(CACHE_FILE.read_text(encoding="utf-8")))
    except (OSError, ValueError):
        pass


def save_cache():
    tmp_fd, tmp = tempfile.mkstemp(dir=SCRIPT_DIR, prefix=".cache")
    with os.fdopen(tmp_fd, "w", encoding="utf-8") as f:
        json.dump(_cache, f, indent=0, sort_keys=True)
    os.replace(tmp, CACHE_FILE)


def cached_check(url, now, force=False):
    entry = _cache.get(url)
    if entry and not force:
        if now - entry.get("t", 0) < TTL.get(entry.get("s"), 0):
            return entry["s"]
    status = check_url(url)
    _cache[url] = {"s": status, "t": int(now)}
    return status


# ----------------------------------------------------------------- vault I/O

class Page:
    """Line-based model of one platform page."""

    def __init__(self, path):
        self.path = path
        self.text = path.read_text(encoding="utf-8")
        self.lines = self.text.splitlines()
        self.changed = False
        self._parse()

    # -- parsing ---------------------------------------------------------
    def _parse(self):
        self.table_start = self.table_end = None      # header line idx, row end
        self.rows = []                                # [link, ts, line_idx]
        self.comp_bullets = []                        # [url, line_idx]
        self.retired_rows = []                        # [link, ts, reason]
        self.retired_bullets = []                     # [url, annotation]
        self.retired_head = None                      # line idx of '## Retired'
        self.retired_tail = None                      # last line idx of section

        i = 0
        n = len(self.lines)
        while i < n:
            s = self.lines[i].strip()
            if s == "## Compilation":
                j = i + 1
                while j < n:
                    m = re.match(r"^\s*-\s*(\S+)", self.lines[j])
                    if m:
                        self.comp_bullets.append([m.group(1), j])
                    elif self.lines[j].strip().startswith("## "):
                        break
                    j += 1
            elif s == "## Retired":
                self.retired_head = i
                j = i + 1
                while j < n and not self.lines[j].strip().startswith("## "):
                    j += 1
                self.retired_tail = j - 1
                self._parse_retired(i + 1, self.retired_tail)
                i = j
                continue
            elif s.startswith("| Link") and self.table_start is None:
                self._parse_table(i)
                i = self.table_end + 1
                continue
            i += 1

    def _parse_table(self, head_idx):
        self.table_start = head_idx
        i = head_idx + 1
        if i < len(self.lines) and re.fullmatch(r"\|[\s\-|]+\|", self.lines[i].strip()):
            i += 1
        while i < len(self.lines) and self.lines[i].lstrip().startswith("|"):
            cells = [c.strip() for c in self.lines[i].strip().strip("|").split("|")]
            if len(cells) >= 2 and not re.fullmatch(r":?-+:?", cells[0]):
                self.rows.append([cells[0], cells[1], i])
            i += 1
        self.table_end = i - 1

    def _parse_retired(self, lo, hi):
        i = lo
        in_ret_table = False
        while i <= hi:
            s = self.lines[i].strip()
            if s.startswith("| Link"):
                in_ret_table = True
            elif in_ret_table and s.startswith("|"):
                cells = [c.strip() for c in s.strip("|").split("|")]
                if len(cells) >= 3 and not re.fullmatch(r":?-+:?", cells[0]) \
                        and cells[0].lower() != "link":
                    self.retired_rows.append([cells[0], cells[1], cells[2]])
            elif re.match(r"^-\s*(\S+)", s):
                m = re.match(r"^-\s*(\S+)(?:\s+\((private|dead|invalid|gone)\))?\s*$",
                             self.lines[i].strip())
                if m:
                    ann = m.group(2) or ""
                    if ann == "gone":       # legacy annotation from initial pass
                        ann = "dead"
                    self.retired_bullets.append([m.group(1), ann])
            i += 1

    # -- dedupe -----------------------------------------------------------
    def dedupe(self, stats):
        """Remove duplicate rows/bullets within the page and rows that are
        already in ## Retired (a dead link must never re-enter the table)."""
        def keys_of(rows):
            out = []
            for r in rows:
                m = URL_RE.search(r[0])
                k = media_key(m.group(0).rstrip(".,);")) if m else ("raw", r[0])
                out.append(k)
            return out

        retired_keys = {k for k in keys_of(self.retired_rows)}

        # main table: rows whose media key is already retired -> drop
        # (any TS it carries is preserved in the retired row)
        retired_by_key = {}
        for row in self.retired_rows:
            m = URL_RE.search(row[0])
            k = media_key(m.group(0).rstrip(".,);")) if m else ("raw", row[0])
            retired_by_key.setdefault(k, row)
        kept = []
        for row, k in zip(self.rows, keys_of(self.rows)):
            if k in retired_by_key:
                base = retired_by_key[k]
                if row[1] and merge_ts(base[1], row[1]) != base[1]:
                    base[1] = merge_ts(base[1], row[1])
                    self.changed = True
                stats["already_retired"] += 1
                self.changed = True
                if VERBOSE[0]:
                    print(f"    drop (already retired): {row[0]}")
                continue
            kept.append(row)
        self.rows = kept

        # main table: merge rows with the same media key (TS union, first wins)
        seen = {}
        kept = []
        for row in self.rows:
            m = URL_RE.search(row[0])
            k = media_key(m.group(0).rstrip(".,);")) if m else ("raw", row[0])
            if k in seen:
                base = seen[k]
                merged = merge_ts(base[1], row[1]) if (base[1] or row[1]) else ""
                if merged != base[1]:
                    base[1] = merged
                    self.changed = True
                stats["deduped"] += 1
                if VERBOSE[0]:
                    print(f"    dedupe (main): {row[0]}")
                continue
            seen[k] = row
            kept.append(row)
        self.rows = kept

        # retired table: same-key rows collapse (first reason wins)
        seen = {}
        kept = []
        for row in self.retired_rows:
            m = URL_RE.search(row[0])
            k = media_key(m.group(0).rstrip(".,);")) if m else ("raw", row[0])
            if k in seen:
                base = seen[k]
                merged = merge_ts(base[1], row[1]) if (base[1] or row[1]) else ""
                if merged != base[1]:
                    base[1] = merged
                    self.changed = True
                stats["deduped"] += 1
                if VERBOSE[0]:
                    print(f"    dedupe (retired): {row[0]}")
                continue
            seen[k] = row
            kept.append(row)
        self.retired_rows = kept

        # compilation bullets: same media listed twice (any URL spelling)
        seen_keys = set()
        kept = []
        for b in self.comp_bullets:
            m = URL_RE.search(b[0])
            k = media_key(m.group(0).rstrip(".,);")) if m else ("raw", b[0])
            if k in seen_keys:
                stats["deduped"] += 1
                self.changed = True
                continue
            seen_keys.add(k)
            kept.append(b)
        self.comp_bullets = kept

    # -- rebuilding ------------------------------------------------------
    def _table_widths(self):
        links = [len(r[0]) for r in self.rows] + [len(r[0]) for r in self.retired_rows]
        tss = [len(r[1]) for r in self.rows] + [len(r[1]) for r in self.retired_rows]
        return max(links + [60]), max(tss + [20])

    def _main_row_line(self, link, ts, wl, wt):
        return f"| {link.ljust(wl)} | {ts.ljust(wt)} |"

    def retire_row(self, row, status):
        self.rows.remove(row)
        self.retired_rows.append([row[0], row[1], REASON[status]])
        self.changed = True

    def restore_row(self, row):
        self.retired_rows.remove(row)
        self.rows.append([row[0], row[1], None])
        self.changed = True

    def retire_bullet(self, bullet, status):
        self.comp_bullets.remove(bullet)
        self.retired_bullets.append([bullet[0], REASON[status].strip("()")])
        self.changed = True

    def restore_bullet(self, bullet):
        self.retired_bullets.remove(bullet)
        self.comp_bullets.append([bullet[0], None])
        self.changed = True

    def write(self, dry_run):
        if not self.changed:
            return False
        out = []
        # ## Compilation (above the table)
        if self.comp_bullets:
            out.append("## Compilation")
            out.append("")
            for url, _ in self.comp_bullets:
                out.append(f"- {url}")
            out.append("")
        # main table
        if self.rows:
            wl, wt = self._table_widths()
            out.append(f"| {'Link'.ljust(wl)} | {'TS'.ljust(wt)} |")
            out.append(f"| {'-' * wl} | {'-' * wt} |")
            for link, ts, _ in self.rows:
                out.append(self._main_row_line(link, ts, wl, wt))
            out.append("")
        # ## Retired
        if self.retired_rows or self.retired_bullets:
            if out and out[-1] == "":
                out.pop()
            out.append("## Retired")
            out.append("")
            if self.retired_rows:
                links = [len(r[0]) for r in self.retired_rows] + [60]
                tss = [len(r[1]) for r in self.retired_rows] + [20]
                rs = [len(r[2]) for r in self.retired_rows] + [8]
                wl, wt, wr = max(links), max(tss), max(rs)
                out.append(f"| {'Link'.ljust(wl)} | {'TS'.ljust(wt)} | {'Reason'.ljust(wr)} |")
                out.append(f"| {'-' * wl} | {'-' * wt} | {'-' * wr} |")
                for link, ts, reason in self.retired_rows:
                    out.append(f"| {link.ljust(wl)} | {ts.ljust(wt)} | {reason.ljust(wr)} |")
                out.append("")
            for url, ann in self.retired_bullets:
                out.append(f"- {url} ({ann})" if ann else f"- {url}")
            out.append("")
        text = "\n".join(out).rstrip("\n") + "\n"
        if text == self.text:
            return False
        if not dry_run:
            self.path.write_text(text, encoding="utf-8")
        return True


# ----------------------------------------------------------------- main pass

def repair_page(md, now, force, dry_run, verbose, stats):
    page = Page(md)
    rel = md.relative_to(VAULT)
    VERBOSE[0] = verbose

    page.dedupe(stats)

    for row in list(page.rows):
        url_m = URL_RE.search(row[0])
        url = url_m.group(0).rstrip(".,);") if url_m else None
        if url is None:
            status = "invalid"
        else:
            # force=False: pre-collection phase just populated the cache
            status = cached_check(url, now, False)
        if status in (GONE, PRIVATE, "invalid"):
            page.retire_row(row, status)
            stats[status] += 1
            if verbose:
                print(f"  retire  {rel}: {url or row[0]} ({status})")
        elif status == AVAILABLE and verbose:
            print(f"  ok      {rel}: {url}")

    for row in list(page.retired_rows):
        url_m = URL_RE.search(row[0])
        if not url_m:
            continue
        status = cached_check(url_m.group(0).rstrip(".,);"), now, False)
        if status == AVAILABLE:
            page.restore_row(row)
            stats["restored"] += 1
            if verbose:
                print(f"  restore {rel}: {row[0]}")

    for bullet in list(page.comp_bullets):
        status = cached_check(bullet[0], now, False)
        if status in (GONE, PRIVATE, "invalid"):
            page.retire_bullet(bullet, status)
            stats[status] += 1
            if verbose:
                print(f"  retire  {rel}: {bullet[0]} ({status})")

    for bullet in list(page.retired_bullets):
        status = cached_check(bullet[0], now, False)
        if status == AVAILABLE:
            page.restore_bullet(bullet)
            stats["restored"] += 1
            if verbose:
                print(f"  restore {rel}: {bullet[0]}")

    if page.changed and page.write(dry_run):
        stats["files"] += 1
        action = "would update" if dry_run else "updated"
        print(f"  ~ {action} {rel}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("--dry-run", action="store_true",
                    help="report planned changes, write nothing")
    ap.add_argument("--force", action="store_true",
                    help="ignore the cache and recheck every link")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--verbose", "-v", action="store_true")
    ap.add_argument("--url", help="check a single URL and exit")
    args = ap.parse_args()

    if args.url:
        print(check_url(args.url))
        return

    load_cache()
    now = time.time()

    # collect every link first so the cache is shared across pages
    jobs = []   # (url, callback)
    pages = []
    for folder in sorted(VAULT.iterdir() if VAULT.exists() else []):
        if not folder.is_dir():
            continue
        for md in sorted(folder.glob("*.md")):
            if md.stem == folder.name:
                continue  # main page: wikilinks only
            page = Page(md)
            pages.append(page)
            for row in page.rows:
                m = URL_RE.search(row[0])
                if m:
                    jobs.append(m.group(0).rstrip(".,);"))
                else:
                    jobs.append(None)
            for row in page.retired_rows:
                m = URL_RE.search(row[0])
                if m:
                    jobs.append(m.group(0).rstrip(".,);"))
            for b in page.comp_bullets + page.retired_bullets:
                jobs.append(b[0])

    unique = [u for u in set(jobs) if u]
    todo = []
    for u in unique:
        entry = _cache.get(u)
        if not args.force and entry and now - entry.get("t", 0) < TTL.get(entry.get("s"), 0):
            continue
        todo.append(u)
    print(f"[self-repair] {len(pages)} pages, {len(unique)} unique links, "
          f"{len(todo)} to check (cache: {len(unique) - len(todo)})")

    if todo:
        with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
            futures = {ex.submit(cached_check, u, now, args.force): u for u in todo}
            done = 0
            for fut in cf.as_completed(futures):
                try:
                    fut.result()
                except Exception as e:  # defensive: never abort the run
                    print(f"  !! checker error {futures[fut]}: {e}", file=sys.stderr)
                done += 1
                if done % 100 == 0:
                    print(f"    checked {done}/{len(todo)}")

    stats = {"gone": 0, "private": 0, "invalid": 0, "restored": 0, "files": 0,
             "deduped": 0, "already_retired": 0}
    for page in pages:
        repair_page(page.path, now, args.force, args.dry_run, args.verbose, stats)

    # persist results even on dry-run: the cache reflects the portals, not the vault
    save_cache()

    print(f"\n[summary] retired: {stats['gone']} dead, {stats['private']} private, "
          f"{stats['invalid']} invalid | restored: {stats['restored']} | "
          f"deduped: {stats['deduped']} | dropped (already retired): "
          f"{stats['already_retired']} | "
          f"files {'to update' if args.dry_run else 'updated'}: {stats['files']}")

    unknown = sorted(u for u, e in _cache.items() if e["s"] == UNKNOWN)
    if unknown:
        print(f"[note] {len(unknown)} links could not be verified and were left "
              f"in place (they will be rechecked next run).")
        if args.verbose:
            for u in unknown:
                print(f"  ? {u}")


if __name__ == "__main__":
    main()
