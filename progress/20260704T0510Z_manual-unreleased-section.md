# Manual: Draft section for unreleased libraries; aggregator HexAll → Hex

## Accomplished

Interactive request spanning two repos.

**`hex-dev` (this repo), branch `doc/manual-unreleased-section` off main:**
- `HexManual.lean`: moved the eleven unreleased-library reference chapters
  (HexArith … HexGFq) out of the top-level TOC into a new part
  "Draft sections for unreleased libraries" at the end, nesting each with
  `{include 2 ...}`. Fixed the Coppersmith tutorial from `{include 1 ...}`
  (which rendered it as a sibling of Tutorials) to `{include 2 ...}` so it
  is a child of Tutorials.
- Verified: `lake build HexManual` green, then rendered with
  `lake exe hexmanual --output _out`. Rendered TOC confirms part 7
  "Tutorials" has child 7.1 "LLL in cryptanalysis" and part 8
  "Draft sections for unreleased libraries" has children 8.1–8.11.
  Top-level parts are now exactly the 6 released chapters + Tutorials +
  Draft section.

Verso `{include N X}` semantics (from `closePartsUntil` in
`verso/.../Elab/Monad.lean`): after a literal `#` header (level 1),
`{include 1 X}` closes back to root and adds X as a level-1 sibling;
`{include 2 X}` adds X as a level-2 child. To nest under the immediately
preceding `#` part, use `{include 2 ...}`.

**`leanprover/hex` aggregator (cloned to `/tmp/hex-agg`, branch
`rename-hexall-and-readme`, committed locally, NOT pushed):**
- Renamed the umbrella `HexAll.lean` → `Hex.lean` (git mv), updated
  `lakefile.toml` (`defaultTargets`, `lean_lib` name) and the module
  docstring, so downstream code writes `import Hex`.
- Reworked `README.md`: folded the separate Mathlib-free / Mathlib tables
  into one three-column table (Component | Computational | Mathlib layer);
  added a Quickstart section with the `require` snippet and a short worked
  example (exact integer determinant + LLL short vector); linked the
  manual (<https://kim-em.github.io/hex-dev/>); corrected released-repo
  links from `kim-em/` to their real `leanprover/` homes.

## Current frontier

Both changes approved for merge. The `hex-dev` manual change is this PR
(branch `doc/manual-unreleased-section`, rebased on main). The aggregator
rename/README is a separate PR against `leanprover/hex` (that repo is
`pins_only` in the sync manifest, so its README + umbrella are authored
directly in the released repo, not generated from here).

## Next step

Merge both PRs once the required `build` check is green.

## Blockers

None.
