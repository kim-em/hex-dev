# Issue 8625 spike: recursive per-remainder re-lift — investigation + plan

## Accomplished

Investigation only, no code yet. Claimed #8625 (assigned). Read the full
#8620 history (premise check, wording clarification, corpus measurement,
close rationale) and the code it cites:

- `bench/HexBench/ClassicalSpike.lean` — the spike precedent: unproven
  executable prototype (`classicalFactorInt`, `classicalFactorIntK`,
  `balancedLift`, `recombInt`), `lean_exe hex_classical_spike` declared in
  the root `lakefile.lean` (srcDir `bench`), timing harness
  (`timePhase`/`factorChecksum`), findings report in
  `reports/bz-classical-spike-findings.md`.
- `HexBerlekampZassenhaus/FactorEntryPoints.lean` —
  `exhaustiveLiftBound core B = max B (defaultFactorCoeffBound
  (toMonic core).monic)`; `factorClassical` feeds `B = defaultFactorCoeffBound
  f` (whole f, the over-lift #8620 measured as marginal).
- `HexPolyZ/Mignotte.lean:427` `defaultFactorCoeffBound`,
  `ReassemblyProofs.lean:170` `precisionForCoeffBound B p = ceilLogP p (2B+1)`.
- `ChoosePrimeData.lean` — `choosePrimeData?` is FIRST-suitable prime
  (Isabelle `find_prime` policy), not min-factor-count;
  `henselLiftData f k pd` lifts `pd.factorsModP` to precision k.
- `SmallModSingleton.lean` — r=1 (mod-p singleton) irreducibility chain
  already exists Mathlib-free; relevant because per-remainder re-selection
  makes r_g = 1 a free (k=0) certificate for the remainder.
- Fixtures: `adv/high_multiplicity` = (x²+1)³(x-3)² (squarefree core
  (x²+1)(x-3), monic); `adv/mignotte_swell` = two height-100 quartics
  (x⁴±100x+1); SD3/SD4/Φ15 defined in `bench/HexBerlekampZassenhaus/
  Bench.lean:176-190`; `splitDegreeHeightInput` family ibid:231.

Key architectural fact (from #8620): classical irreducibility flows through
coverage gated on partition completeness at
`2·defaultFactorCoeffBound (toMonic core).monic < p^k`, inherited by
`liftedFactorSubsetPartition_transport` at the same LiftData. Sub-floor
certification requires a FRESH per-remainder lift/partition — the thing this
spike measures before anyone builds it.

## Current frontier

Plan agreed shape (measurement-first, gating deliverable 1 of the issue):

1. New `bench/HexBench/RecursiveReliftSpike.lean` + `lean_exe
   hex_recursive_relift_spike` (mirroring ClassicalSpike; Mathlib-free;
   not wired into CI). Self-contained copies of the small recomb helpers.
2. Prototype `recursiveCertify g`: deg≤1 → free; choosePrimeData? g,
   r=1 → free (mod-p singleton); else ladder k=1,2,4,…, clamped at
   floor_g = precisionForCoeffBound (defaultFactorCoeffBound (toMonic
   g).monic) p_g; at each rung lift+recombine; split → recurse on pieces,
   no split at floor → certified irreducible. Record per-node
   (deg, p, r, k_stop, outcome).
3. Metrics per input: today's k (exhaustiveLiftBound core (mignotte f)),
   core-local floor k (#8620 rewrite-1 reference), recursive Σk_stop and
   degree-weighted Σ deg²·k_stop; wallclock secondary.
4. Families: high_multiplicity core, mignotte_swell, Φ15, SD3, SD4 (loss
   cases: irreducible), splitDegreeHeightInput grid extended to deg 8–24,
   plus constructed loss case (x-1)·SD3 / (x-1)·SD4 (small factor of large
   core).
5. Report `reports/bz-recursive-relift-findings.md` + measurement comment
   on #8625 with recommendation; deliverable 2 (proof remodel) only if the
   win is robust, likely as a follow-up directive.

Risk to watch: per-rung recombination rescans (SD4: r=16 → C(16,≤8)
subsets per rung × ~7 rungs) may dominate the loss cases; measure it.

## Next step

Implement `RecursiveReliftSpike.lean`, run it, tabulate, write report,
/second-opinion, PR on branch issue-8625.

## Blockers

None.
