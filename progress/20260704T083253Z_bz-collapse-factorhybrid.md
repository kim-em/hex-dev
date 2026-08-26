# BZ: collapse factorHybrid* into factor*

## Accomplished
Part 6 of the BZ factor-path cleanup (#8583). Collapsed the
factor -> factorHybrid -> factorHybridTraced indirection now that the
pre-hybrid combinator is gone and factor IS the hybrid. Substring-renamed
factorHybrid -> factor across the repo (cascading factorHybridTraced ->
factorTraced, factorHybridFactors -> factorFactors,
factorHybridFactors_factor_irreducible -> factorFactors_factor_irreducible,
factorHybrid_eq_factorizationOfFactors -> factor_eq_factorizationOfFactors),
then resolved the two resulting duplicates: deleted the circular
def factor := factor f wrapper (keeping the inlined def factor :=
(factorTraced f).1 with the public hybrid-dispatch docstring), and deleted
the self-referential factor_eq_factorizationOfFactors wrapper (keeping the
substantive proof). FactorTrace and its tier/declined fields unchanged.

Files: HexBerlekampZassenhaus/Basic.lean, HexBerlekampZassenhausMathlib/
{FactorSoundness,LatticeTier}.lean, bench/HexBench/LatticeSpike.lean,
conformance/HexBerlekampZassenhaus/EmitFixtures.lean, DEV.md.

Verify: whole-graph lake build green (4088 jobs); hexbz_bench /
HexConformance / hexbz_emit_fixtures / hexbz_factor_service green (452
jobs, conformance #guards pass); factorHybrid grep-clean; zero sorry/axiom
introduced.

## Current frontier
Public API is now factor / factorTraced / factorFactors with no hybrid
indirection. Only F (SPEC/directive consistency pass) remains.

## Next step
Issue F (#8584): confirm SPEC clean; refresh #8369/#8370 directive bodies
to the new names.

## Blockers
None.
