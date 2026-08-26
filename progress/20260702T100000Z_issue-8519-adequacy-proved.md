# issue #8519 — van Hoeij L'=W lattice adequacy: BOTH SORRIES DISCHARGED

## Accomplished

The two `LatticeTier.lean` sorries (arm-2 count-equality, arm-3 single-all-ones
adequacy) are proven. `#print axioms` on
`factorHybridFactors_factor_irreducible`, `factor_irreducible_of_nonUnit`,
`Hex.ZPoly.isIrreducible_iff`, and `Hex.ZPoly.instDecidableIrreducible` all
report exactly `[propext, Classical.choice, Quot.sound]` — the decidable
irreducibility chain for integer polynomials is fully verified, no `sorryAx`
in any cone.

### Session commits (branch issue-8519, stacked on PR #8517's issue-8417)

1. **3157b3d3 executable coherence fix**: the lattice tier selected its prime
   on `core` but Hensel-lifted against `(toMonic core).monic` — provably
   incoherent for `lc ≢ 1 (mod p)` (compiled probe: `(2x+1)(x²+x+1)` at `p=5`
   fails the lift invariant and the tier returns `none`). Re-keyed
   `factorLatticeFactorsWithBound` to `toMonicPrimeData?` (classical-tier
   precedent, plan option (c)), built the CLD lattice on the monic transform
   in `bhksRecoverClassified`/`bhksSingleAllOnesPartition`, added cap
   components. Posted the premise correction to the issue.
2. **fb6a5002 LatticeTier re-key** to the `toMonicPrimeData?` witness; new
   dilation-descent lemma for the singleton arm.
3. **729e36e3 fastCoreFloor gate**: acceptance floor now also clears both
   Mignotte bounds, giving the partition machinery at the arm-2 witness
   precision.
4. **15371abf / 7c34f698 / e9116970 / ed93ef12 resurrection** of the
   sorry-free pre-#8411 `W ⊆ L'` machinery (deleted in 6bf20977) from
   `6bf20977^`, adapted to `Matrix.rowReduce`/`vecMul`/`lllNative`:
   SignatureClasses (+RREF column agreement), Lattice (Klüners Lemma 1
   `mem_prefixSubmodule_of_normSq_le`, `CutProjectionHypotheses`,
   `cutProjectionHypotheses_of_shortVectors`), CLDColumnBound (`phi` bound,
   aggregate residue, period carry, `supportShortVectorData_of_recoveredLift`),
   Recovery (class-count = RREF signature partition; `W ⊆ L'` refinement
   bound), PartitionRefinement (partition length = normalizedFactors card).
5. **94fdf715 the adequacy assembly**:
   `normalizedFactors_card_le_bhksEquivalenceClassIndicators_size` — supports
   from the #8413 partition, `RecoveredAtLift → RecoveredLift`
   (`recoveredLiftOfRecoveredAtLift`, centred-lift recovery at floor-certified
   Mignotte precision), per-support short vectors, cut inclusion, count chain.
   Arm-2 = this at the gate-certified witness precision + the proven UFD `≤`;
   arm-3 = this at `B` + reducibility contradiction. `hprec` restated as
   `fastCoreFloor core ≤ B` (+`B ≠ 0`), discharged at the capstone from the
   cap le-lemmas.

## Verification

- `lake build HexBerlekampZassenhausMathlib`: green, zero sorry warnings.
- `lake build HexBerlekampZassenhaus` (full target incl. CrossCheck +
  #guards): green.
- Axiom cones: clean (see above).
- HexConformance build in flight at session end of this note; PR next.

## Next step

/second-opinion review, then PR against `issue-8417` (stacked, like #8528).

## Blockers

None.
