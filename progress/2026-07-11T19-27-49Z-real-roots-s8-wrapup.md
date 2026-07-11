# HexRealRootsMathlib S8 wrap-up: root identity, deferred two-circle, companion conformance

## Accomplished

- `HexRealRootsMathlib/SimpleRealRoot.lean`: `theRoot`, `overlaps_iff_same_root`,
  `SimpleRealRoot.toReal`/`toReal_isRoot`/`toReal_injective`, `sameRoot_iff`.
  The forward direction of `overlaps_iff_same_root` is the separation argument
  (both widths `≤ 2^{−sepPrec}`, `sepPrec_separates'`); the backward direction is
  the common-root interval containment. Signatures match the SPEC verbatim: `p ≠ 0`
  is derived internally from the isolation's `count_one` (`degree_pos_of_count_one`),
  so no `hp0` hypothesis is needed (unlike the driver theorems).
- `HexRealRootsMathlib/TwoCircle.lean`: states `isolateDescartes?_isSome` with the
  full deferred-theorem docstring (Obreshkoff two-circle prerequisite, nothing
  depends on it, conformance-deletion obligation). The one intentional `sorry`.
- `conformance/HexRealRootsMathlib/Conformance.lean` (plain file, module
  `HexRealRootsMathlib.Conformance`): cast equalities + independent Mathlib
  root-card theorems + `#guard`ed executable `rootCount`, plus the full formal tie
  on `x − 5` (`rootCount_eq_card_roots` instantiated via `squareFreeRat_iff` +
  irreducibility). Added to the `HexConformance` globs; `conformance_targets.py
  --check` passes.
- M5 renames in `SturmTheorem.lean`: `exists_gap_lt/gt` → `exists_left_gap/right_gap`,
  `head_mem` → `chain_head_mem`, `card_filter_Ioc_split` made `private`.
- `libraries.yml`: `HexRealRootsMathlib` `done_through` 0 → 1.
- Umbrella imports the two new files; docstring refreshed. `check_dag`,
  `check_phase4`, `conformance_targets --check` all green.

## Current frontier

`lake build HexRealRootsMathlib HexConformance` completes (9065 jobs); the only
`sorry` warning in the whole library is `TwoCircle.isolateDescartes?_isSome`.

## Next step

Phase-2 review pass for `HexRealRootsMathlib`, and eventually discharging the
two-circle theorem (which then deletes the conformance Descartes stand-ins).

## Blockers

None.
