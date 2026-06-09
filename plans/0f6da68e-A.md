library: HexBerlekampZassenhaus

## Current state

Sub-issue A of #6584. PR #6583 wired the three-tier combinator
`factor = factorFast → factorSlowModular? → factorSlowTrial` via thin
`Option`-returning shims `factorSlowModular?` /
`factorSlowModularWithBound?` defined alongside the historical total
`factorSlow` / `factorSlowWithBound` (`HexBerlekampZassenhaus/Basic.lean`
lines ~6846, 6859). This sub-issue renames the historical entry
points and rewrites them to `Option`-returning natively, removing the
shim and the now-unreachable Array-returning total form. It is the
pure-rename half of #6584; the silent-fallback removal lives in
sub-issue B.

## Deliverables

Single PR.

1. Rename in `HexBerlekampZassenhaus/Basic.lean`:
   `factorSlow → factorSlowModular`,
   `factorSlowWithBound → factorSlowModularWithBound`,
   `factorSlowFactorsWithBound → factorSlowModularFactorsWithBound`,
   and the companion theorems
   (`factorSlow_product`, `factorSlowWithBound_product`,
   `factorSlowFactorsWithBound_branch`,
   `factorSlowFactorsWithBound?_eq_some_iff_safe_branch`,
   `factorSlowFactorsWithBound_polyProduct`,
   `factorSlowWithBound_product_of_*_branch`,
   `factorSlowFactorsWithBound_branch_of_choosePrimeData?_some`,
   plus any remaining `factorSlow*` identifiers at the existing
   source-order positions).

2. Change the renamed public signatures to `Option`-returning by
   folding the `?` shim into the renamed total form:
   - `factorSlowModularFactorsWithBound : ZPoly → Nat → Option (Array ZPoly)`
     — body is the existing `factorSlowFactorsWithBound?` (drop the
     `?` in the name; keep the `Option` body).
   - `factorSlowModularWithBound : ZPoly → Nat → Option Factorization`.
   - `factorSlowModular : ZPoly → Option Factorization`.
   - Drop the historical Array-returning `factorSlowFactorsWithBound`
     and the now-redundant `?`-suffixed shims
     `factorSlowModular? / factorSlowModularWithBound?` (the renamed
     totals are the canonical `Option` form).

3. Update the three-tier wiring (`factorWithBound` / `factor`) to
   consume `factorSlowModular` / `factorSlowModularWithBound`
   directly. Drop the `factorSlowModular?` shim.

4. Bridge rename in
   `HexBerlekampZassenhausMathlib/Basic.lean` (sites at lines
   ~309/361/585/16285/16308/16341/16361) and any references in
   `HexBerlekampZassenhausMathlib/UFDPartition.lean` and
   `HexBerlekampZassenhausMathlib/IntReductionMod.lean`. Bridge
   umbrellas
   (`factor_entries_primitive_of_chosen_raw_primitive`,
    `factor_headline_contract_core_with_primitive`, etc.) update
   their `factorSlow*` disjunct shape to match the new
   `Option`-returning names.

5. Pivot Conformance / CrossCheck / Bench callers in
   `HexBerlekampZassenhaus/Conformance.lean`,
   `HexBerlekampZassenhaus/CrossCheck.lean`,
   `HexBerlekampZassenhaus/Bench.lean`:
   - Total callers move to `factorSlowTrial` (always-defined) or
     `factor` (three-tier combinator).
   - `Bench.runFactorSlowChecksum` measures `factorSlowTrial`.

## Library placement

- `HexBerlekampZassenhaus/Basic.lean`
- `HexBerlekampZassenhaus/Bench.lean`
- `HexBerlekampZassenhaus/Conformance.lean`
- `HexBerlekampZassenhaus/CrossCheck.lean`
- `HexBerlekampZassenhausMathlib/Basic.lean`
- `HexBerlekampZassenhausMathlib/UFDPartition.lean` (if referenced)
- `HexBerlekampZassenhausMathlib/IntReductionMod.lean` (if referenced)

## Verification

- `lake build HexBerlekampZassenhaus` green.
- `lake build HexBerlekampZassenhausMathlib` green.
- `lake exe hexbz_bench list` and
  `lake exe hexbz_bench verify --filter runFactor` complete within
  budgets.
- No new forbidden tokens (`axiom`, `native_decide`, `TODO`, `FIXME`,
  `sorry`).

## Out of scope

- Removing `choosePrimeDataFallback` and tightening the remaining
  `choosePrimeData` (total) callers — that is sub-issue B (#TBD),
  blocked on this PR. The `Option`-native `factorSlowModular` body
  may still reach `choosePrimeData` (total) during this PR; B
  cleans that up.
- Adding `factorSlowTrial` named entry points (predecessor sub-issue
  already landed in #6583's chain).

depends-on: #6584
