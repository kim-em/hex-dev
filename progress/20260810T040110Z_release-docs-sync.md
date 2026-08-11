# Release documentation sync

## Accomplished

Three hand-maintained lists of Hex libraries had all drifted behind
`scripts/release/released.yml`. Each is now either derived from the
manifest or checked against it.

- `AGENTS.md` listed 12 released repos out of 35. It now points at
  `released.yml` instead of restating the set, and describes the two
  structural cases (`hex-test-kit`, the `pins_only` aggregate).
- The root `README.md` now leads with `leanprover/hex` (the aggregate a
  user should depend on) and the manual, and says plainly that this repo
  is where development happens and released repos are published mirrors.
- The `leanprover/hex` README is generated. Prose lives in
  `scripts/release/hex-README.md`; `scripts/release/aggregate_readme.py`
  renders the library table from the manifest's new `component:` labels;
  `sync_released.py` publishes the result for the `readme_template` entry.
  The published table goes from 9 rows to 19.
- `check_released_manifest.py` requires a `component:` label on every
  aggregated computational library and rejects one anywhere else, so a
  release cannot skip the table.
- `HexManual.lean` had 6 chapters in the released body and 21 under
  "Draft sections for unreleased libraries", though 19 chapters document
  released libraries. Corrected, and `scripts/release/check_manual_split.py`
  (new, wired into `ci.yml`) now derives the split from `released.yml` and
  fails on drift, duplicate includes, wrong include level, or a chapter
  that is never included.
- The `kim-em/hex-dev` GitHub About box now names the aggregate and sets
  its homepage to `https://github.com/leanprover/hex`.

## Current frontier

Everything above is on `docs/release-docs-sync`. `lake build HexManual`
is the one expensive verification: the reorganized manual has to still
elaborate with 18 chapters moved from include level 2 to level 0.

## Next step

Publish the regenerated aggregate README by dispatching
`.github/workflows/sync-released.yml`, dry run first.

## Blockers

The released repos are on `leanprover/lean4:v4.32.2`; `hex-dev` is on
`v4.33.0-rc1`. A full sync is therefore a toolchain-bumping release of
all 35 repos, not a documentation-only publish, and `--only hex` is worse:
it would bump the aggregate's toolchain while its pinned libraries stay
on the old one. Publishing the README needs a decision about running the
full release.
