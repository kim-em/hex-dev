# Retire the standalone `factorFast` tier (#8579)

## Accomplished
Part 2 of the BZ factor-path cleanup: deleted the f-level `factorFast`
wrapper surface (the CLD lattice tier without the irreducibility-certifying
cap arm), superseded in production by `factorLattice`. The shared core
stack (`factorFastCore*`, `factorFastPrecisionCap*`, `fastCoreFloor*`) is
kept intact — the lattice tier's proofs and cap reduce to it.

- `HexBerlekampZassenhaus/Basic.lean`: removed 24 f-level decls
  (`factorFast`, `factorFastWithBound`, `factorFastFactorsWithBound` and
  all their lemmas / product privates / `#guard`s), plus the duplicate
  `factorFastFactorsWithBound` cubic `#guard`. Reworded surviving docstrings
  that referenced the bare fast path.
- `HexBerlekampZassenhausMathlib/IntReductionMod.lean`: removed the two raw
  f-level irreducibility lemmas (`_raw_guardedIrreducible_of_smallModSingleton`,
  `_raw_irreducible_of_quadratic`) and the fast-none cluster
  (`factorFast_none_squareFreeCore_degree_ne_zero`,
  `factorSlowTrialFactorsWithBound_factor_irreducible_of_fast_none`, and the
  dead `slowModularRaw_irreducible_of_fast_none` which depended on the deleted
  private and had no consumers). The fast-none-free
  `factorSlowTrialFactorsWithBound_factor_irreducible` survivor is untouched.
- Bench / scripts / conformance: dropped the `factorFast` service entry
  (`bench/HexBench/FactorService.lean`), the four `factorFast` bench drivers
  and their `setup_benchmark` registrations (`bench/HexBerlekampZassenhaus/Bench.lean`,
  keeping the `factorLattice` targets and the `factorFastPrecisionCap` setup
  targets), the `hex-fast` sweep row (`scripts/bench/factor_sweep.py`), the
  standalone `factorFast (linear 3)` conformance `#guard`, and the DEV.md pointer.

## Current frontier
Whole-graph `lake build` green (4088 jobs); `hexbz_bench`,
`hexbz_factor_service`, and `HexConformance` green; `check_benches_mathlib_free`
and `conformance_targets --check` pass. No new `sorry`/`axiom`.
`rg` for bare `factorFast` over source (excluding progress/reports/status)
returns only core-stack names.

## Next step
Post-merge follow-up from the issue: edit #8369's body so its substrate
pointer targets the surviving `factorFastCoreWithBound_ne_none_of_recovery_on_schedule`
instead of the deleted f-level `factorFast_ne_none_of_core_recovery_on_schedule`.

## Blockers
Cactus-chart regeneration (`scripts/plots/hexbz-cactus.py`) could not run:
this environment has no `matplotlib` and no `pip`. Per the issue, this is
non-blocking — the committed SVGs are left as-is (the hex-fast curve would
simply drop on the next regeneration from committed records).
