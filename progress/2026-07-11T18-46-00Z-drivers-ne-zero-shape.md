# Shape fix: public completeness theorems take p ≠ 0

## Accomplished

Per Codex review of #8748: the public theorems `isolateSturm?_isSome`,
`isolate?_isSome`, and `RealRootIsolations.isolates` now take `p ≠ 0` instead
of `1 ≤ (p.degree?).getD 0`. The driver's nonzero-constant branch genuinely
returns `some` (the empty chain certifies `rootCount = 0` through `assemble?`),
and downstream consumers (hex-rcf after `squareFreeCore`) call isolation on
constants, so the degree form would force artificial case splits.

Implementation:
- Positive-degree proofs kept as private helpers (`isolates_of_degree_pos`,
  `isolateSturm?_isSome_of_degree_pos`).
- New private `isolateSturm?_isSome_of_degree_zero`: the `some 0` branch hands
  `assemble?` the empty array; `sturmChain p = #[]` so
  `sturmVarNegInf − sturmVarPosInf = 0` by `rfl`.
- New public `degree?_ne_none` in Isolations.lean (`p ≠ 0 → degree? ≠ none`,
  via `DensePoly.degree?_eq_none_iff` + `ext_coeff`).
- `isolates` constant case is vacuous: `toPolyℝ p = C c` with `c ≠ 0` has no
  roots (`Polynomial.eq_C_of_natDegree_eq_zero`).

Whole-repo build green, `check_dag` green, still sorry-free.

## Current frontier

Tranche complete; #8748 updated and awaiting merge.

## Next step

`SimpleRealRoot.lean` per the SPEC file organisation.

## Blockers

None.
