# HexManual render executable + GitHub Pages publishing

## Accomplished

- Added `Main.lean` + a `hexmanual` `lean_exe` that render the HexManual
  Verso document to static HTML (`manualMain (%doc HexManual)`,
  multi-page, htmlDepth 2). `lake exe hexmanual --output _out` produces
  the browsable site under `_out/html-multi` (verified locally: index +
  one page per chapter, recipes included).
- Added `.github/workflows/pages.yml`: builds, renders, and deploys the
  manual to GitHub Pages on push to `main` (+ `workflow_dispatch`).
  Push-to-main only by design -- a publish step, not a PR gate; documented
  in the workflow header and SPEC-aligned (concurrency, single job,
  Mathlib cache fetch like ci.yml).
- Documented the render-and-publish flow in `PLAN/Releases.md` and a new
  `HexManual/README.md` (local render command + Pages URL).
- Removed 9 stray `HexManual/Phase*Checkpoint-*.md` development-checkpoint
  files (merge-history notes that don't belong in the manual source dir
  and cut against the no-progress-notes-in-files rule).
- `_out/` added to `.gitignore`.

## Current frontier

PR up against `main`. GitHub Pages must be set to the "GitHub Actions"
source once in repo settings before the first deploy can publish.

## Next step

After this lands: replicate the recipe template across the remaining
chapters; PLAN/Phase7 + SPEC/recipes (PR 3). Optionally add `HexManual`
to ci.yml's build list if PR-time manual validation is wanted.

## Blockers

Pages publishing is blocked until the repo's Pages source is set to
GitHub Actions (one-time settings change).
