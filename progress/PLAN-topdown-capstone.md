# Top-down capstone structure (#8417) — the connected architecture

Kim's directive: everything top-down from the capstone, no disconnected lemmas
with invented hypotheses. Done — `factor_irreducible_of_nonUnit` is now a real
proof (FactorSoundness.lean), reducing through CONNECTED obligations:

```
factor_irreducible_of_nonUnit                     [FactorSoundness.lean]
  = factorizationOfFactors f (factorHybridFactors f)   (factor_eq_factorizationOfFactors)
  → entry = normalizeFactorSign raw                     (factorizationOfFactors_entry_mem_normalized_raw)
  → Irreducible raw                                     (zpolyIrreducible_normalizeFactorSign_...)
  → factorHybridFactors_raw_irreducible                 [case-split classical/lattice/trial]
      ├─ classical: factorClassicalFactorsWithBound_raw_irreducible   [FILLABLE from #8413]
      ├─ lattice:   factorLatticeFactorsWithBound_raw_irreducible     [#8417 deep content]
      │    → reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
      │    → latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible   [LatticeTier.lean]
      │        ├─ arm 1 (factorsModP.size ≤ 1): PROVED
      │        ├─ arm 2 (fast CLD split): latticeArm2_fastCore_count  [deep, sorry]
      │        └─ arm 3 (all-ones):       latticeArm3_...             [structured → hfalse sorry]
      └─ trial:     factorSlowTrialFactorsWithBound_raw_irreducible   [FILLABLE from existing]
```

## Remaining sorries (all connected, real obligations — not invented)
1. `factor_irreducible_of_nonUnit` f=0 edge case.
2. `factorClassicalFactorsWithBound_raw_irreducible` — mirror the lattice wiring;
   `factorClassicalFactorsWithBound` has identical structure (constant/quadratic/
   toMonicPrimeData?+reassemble); core lemma `classicalCoreFactorsWithBound_
   squareFreeCore_factor_zpolyIrreducible` is PROVEN. Pure assembly.
3. `factorLatticeFactorsWithBound_raw_irreducible`: constant + quadratic sub-cases,
   the `reassemblyExpansionComplete` side condition, and the precision obligation
   `2·bhksBound core < p^k` (dischargeable from `factorFastPrecisionCap f` via a
   `bhksBound core ≤ bhksBound f` monotonicity lemma).
4. `factorSlowTrialFactorsWithBound_raw_irreducible` — from
   `factorSlowTrialFactorsWithBound_factor_irreducible_of_fast_none` (IntReductionMod
   :6749); NOTE the hybrid fires trial on classical-decline, not fast=none — check
   whether an unconditional trial-irreducibility holds or thread the right condition.
5. Lattice arm 2 (`latticeArm2_fastCore_count`) and arm 3 (`latticeArm3` → `hfalse`):
   the genuine van Hoeij CLD geometry. `hfalse` (≥2 factors ⇒ certificate false)
   is the concrete deep lemma; DAG in PLAN-arm3-dag.md. NB: no monic hypothesis is
   available from the real caller, so the suspected non-monic prime-data bug (lattice
   uses choosePrimeData? but lifts (toMonic core).monic) surfaces HONESTLY here —
   Kim: "probably a bug". Fix belongs in the executable (lattice → toMonicPrimeData?)
   once its behaviour is confirmed.

## Proven this session (connected, no invented hyps)
Arm 1; bhksLatticeBasis LLL-independence; LLL short-vector bound applied to the
lattice; the entire top-down capstone architecture.
