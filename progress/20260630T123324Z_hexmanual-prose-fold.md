# HexManual prose overhaul + fold *Mathlib chapters in-page

## Accomplished

- Rewrote the HexMatrix chapter in plain language (dropped "core of the
  stack", "doubles as both", "reads them into", representation claims now
  that `Matrix` is no longer an `abbrev`). Worked example uses the new
  `#m[...]`/`#v[...]` notation with dot-notation to avoid the Mathlib
  name clash.
- Decided (Kim): the Mathlib half of each library lives in the same
  chapter, clearly delineated. Added a "# The Mathlib correspondence"
  section to HexMatrix and folded the four standalone `*Mathlib` chapters
  (HexModArithMathlib, HexPolyMathlib, HexHenselMathlib, HexGFqMathlib)
  into their executable chapters at "middle" detail (the equivalence /
  correctness headline + round-trip + main transfer lemmas). Deleted the
  standalone chapters; preserved tags so inbound `{ref}`s resolve.
- Fixed HexGFq's cross-reference, which wrongly claimed no paired
  `*Mathlib` layer.
- Plain-language pass on `HexMatrixMathlib` README + docstrings
  (`matrixEquiv`, `matrixEquiv_apply`, `vectorEquiv_apply`): no more
  "a Mathlib reading" / "reads off".
- De-slopped the aggregator top intro (no "computational algebra stack").
- Reordered `HexManual.lean` chapters as a topological sort of the
  dependency DAG, released libraries first.

## Current frontier

Full `lake build HexManual` green (manual now 17 chapters). Branch
`claude/manual-hexmatrix-prose`. Rebasing onto current `main` (which now
has #8442 Matrix-as-structure) before PR.

## Next step

PR, Codex second-opinion review, merge; Pages redeploys on merge.

## Blockers

None.
