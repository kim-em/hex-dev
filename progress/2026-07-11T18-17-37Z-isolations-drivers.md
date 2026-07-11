# Isolation semantics and driver completeness

## Accomplished

Added `HexRealRootsMathlib/Isolations.lean` and `HexRealRootsMathlib/Drivers.lean`
(registered in the umbrella). Whole library builds; `check_dag` green.

`Isolations.lean` (sorry-free):
- `RealRootIsolation.exists_unique_root` — a certified isolation names exactly
  one real root in its half-open interval. Degree-positivity is *derived* from
  `count_one` (via `degree_pos_of_count_one`), so the statement takes only
  `SquareFreeRat p`, matching the SPEC verbatim.
- `RealRootIsolations.isolates` — a complete run names every real root exactly
  once. Injective-map / equal-cardinality bijection between isolations and the
  root finset. **Added hypothesis** `1 ≤ (p.degree?).getD 0`: the SPEC's
  `SquareFreeRat`-only form is unsound (for `p = 0` every real is a root while
  `complete` forces zero isolations). Flagged in the docstring.

`Drivers.lean`:
- `refine1_isolates_same` (sorry-free) — one bisection preserves the isolated
  root (biconditional on root membership) and halves the width; fallback branch
  shown unreachable via `sturmCount_split` (count additivity) + `count_one`.
- `sturmVar_neg_pos_sub` (sorry-free) — the `±rootBound` variation gap equals
  `rootCount p`. This is the formal resolution of the "±R vs ±∞" question: it
  is a statement about `p`'s roots only, so chain-element zeros beyond `R` never
  matter.
- `initial_width_le`, `toReal_le_two_pow_ceilLog2Dyadic` (sorry-free) — the top
  interval's width fits the depth budget `2^(isolationDepth − sepPrec)`.
- `isolateSturm?_isSome`, `isolate?_isSome` — proven **modulo one sorry**
  (`sturmVisit_spec`). All wrapper logic (degree/`SquareFreeRat` dispatch,
  `assemble?` discharge via ordering + `arr.size = rootCount`) is complete.
  Added hypothesis `1 ≤ (p.degree?).getD 0` (again `SquareFreeRat 0` vacuous).

## Current frontier

One `sorry`: `sturmVisit_spec` (Drivers.lean ~line 401) — the structural
induction on `depth` that the DFS worklist drains, ordered, with
`arr.size = vlo − vhi`. Full invariant and proof plan are in its docstring.

## Next step

Discharge `sturmVisit_spec`: (1) drain via `sepPrec_separates'` (real-pair gap)
at `depth = 0`, halving width on bisection; (2) telescoping count via `sturmVarAt`
monotonicity across a split; (3) `left ++ right` ordering from the midpoint
separator. Then `isolate?_isSome` is sorry-free and the PR can land.

## Blockers

None. `sturmVisit_spec` is well-scoped; everything it feeds is already proven.
