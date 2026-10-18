# C.U.R.E.

Welcome to the C.U.R.E. project (the Curated Universe of Recorded Eructations).

It is a markdown based database and can be used and searched as an e.g. Obsidian vault locally.

## Rules for Contributions

See the example folder in the CURE directory for the format of the entries.

Only add links and metadata (no other media like images, videos or sound recordings) and make sure they are "generally accessible" (meaning no privated videos or sources that require authentication or registration).

After every import or manual edit, run `python3 scripts/self_repair.py` — it checks all links, retires dead ones and dedupes the tables.

Then simply create a PR for your contribution.
