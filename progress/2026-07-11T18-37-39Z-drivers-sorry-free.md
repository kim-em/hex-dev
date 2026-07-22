# Driver completeness: sturmVisit_spec closed, tranche sorry-free

## Accomplished

Closed `sturmVisit_spec`, the last `sorry` in the isolation-semantics /
driver-completeness tranche (and, with it, the last `sorry` in the
hex-real-roots companion outside the deferred TwoCircle development).
`HexRealRootsMathlib/Drivers.lean` and `Isolations.lean` are now fully
sorry-free; whole-repo `lake build` green, `check_dag` green.

The proof follows the plan recorded in the previous progress file:

- New helpers: `dle_refl`/`dle_of_lt`/`dle_trans` (core dyadic order via
  `toRat`), `sturmVarAt_le` (variation antitone: counts are nonnegative
  cardinalities), `isRoot_toPolyℂ` (real root → complex root through
  `Polynomial.IsRoot.map`), `sturmCount_le_one` (an interval no wider than
  `2^(−sepPrec p)` has Sturm count ≤ 1, via `sepPrec_separates'` on the real
  pair — two distinct roots in the interval would be closer than a quarter of
  their guaranteed gap).
- `sturmVisit_spec` by structural induction on `depth`, with the `rfl`-typed
  unfolding equations for the private `sturmVisit` (`import all` pattern; the
  `d+1` equation includes the zeta-expanded midpoint recursion so the IH
  equations rewrite syntactically). Leaves: count-0 emits `#[]`, count-1's
  dependent-ifs are discharged with the raw `sturmVarAt`-difference form;
  count ≥ 2 at depth 0 is refuted by `sturmCount_le_one` + `sturmVarAt_le`
  (omega on the Nat/Int mix). Bisection: exact width halving via
  `toReal_midpoint` + `zpow_add_one₀`, telescoped sizes
  `(vlo−vmid)+(vmid−vhi) = vlo−vhi`, and `left ++ right` ordering from the
  containment invariants (`Array.getElem_append_left/right`, `Fin.getElem_fin`).

Notable friction (for future sessions): `#[x].size` is defeq to `1`, so
`i.isLt : ↑i < 1` directly — `simp` does NOT reduce singleton-array sizes in
hypotheses; and `rwa [Array.size_append] at h` fails on `↑i < (a ++ b).size`
(motive: `i`'s type depends on the size) — use `i.isLt.trans_eq
Array.size_append` instead.

## Current frontier

Tranche complete. PR opened from `real-roots-s7-drivers`.

## Next step

Per SPEC file organisation, remaining hex-real-roots-mathlib work:
`SimpleRealRoot.lean` (overlaps_iff_same_root, toReal, sameRoot_iff — consumes
`exists_unique_root` + `refine1_isolates_same` from this tranche) and the
deferred `TwoCircle.lean`.

## Blockers

None.
