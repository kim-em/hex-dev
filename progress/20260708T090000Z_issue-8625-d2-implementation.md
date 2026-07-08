# Issue 8625 deliverable 2: computational layer implemented and priced

## Accomplished

- `classicalCoreFactorsRecursive` implemented in
  `HexBerlekampZassenhaus/FactorEntryPoints.lean` (NOT yet wired into
  `factorClassicalFactorsWithBound`): same-prime sub-floor escalation
  ladder with greedy per-rung peel over (lifted, seed) pairs
  (`subFloorScan`/`subFloorPeel?`/`subFloorPeelSize`), tracked per-piece
  prime data via monic-dilation transport (`FpPoly.monicDilate`,
  `piecePrimeData?`), `boundedExactQuotient?` (early-abort division with a
  re-multiplication guard on successes, so soundness is one trivial
  lemma), fuel-based recursion, floor fallback to today's
  `classicalCoreFactorsWithBound` at each node's own floor. Sub-floor cap 2.
- Validated in the spike (prod-rec arm): all 18 corpus cases correct
  (product + degree signatures), 108/108 checks across arms.
- Wallclock (deg24 split): today 37.4ms, prod-rec 30.4ms (1.23x win),
  spike-prototype cap2 23.3ms. Wins 1.23-1.29x on all split/high-mult
  families; losses 1.19-1.58x on irreducible/SD families (absolutely
  small; SD4 prod-rec now BEATS the prototype).
- Cost decomposition (new `RELIFT_PROFILE=prodrecsteps`): prime selection
  13.7ms + Mignotte bounds ~13.8ms (2 x 6.9ms) are SHARED additive costs;
  the recursion's algorithmic core is ~2.7ms vs today's floor lift+scan
  ~9.9ms (the true ~3.7x algorithmic win, masked by shared overheads).
- Root-caused the Mignotte cost and filed
  https://github.com/kim-em/hex-dev/issues/8677 (defaultFactorCoeffBound
  recomputes the L2 norm in an O(deg^2) loop; closed form
  `binom n (n/2) * coeffL2NormBound f`). When it lands, deg24 becomes
  today ~23.7 vs prod-rec ~16.6 (~1.43x), loss rows unaffected.
- Design (B) (per-node Berlekamp re-run) refuted by measurement earlier
  in the session (reB-cap2 arm, kept in the spike).

## Current frontier

Computational layer done, unproven. The certification stack (tasks 3-5)
is untouched: fresh per-remainder partition producer (mod-p dilation
transport for the monic transforms of a peel; `factorsModPBerlekampForm`
is literal-Berlekamp-output keyed, so producers re-key at the semantic
layer: `henselSubsetCorrespondenceHypotheses` + partition evidence),
ladder spec + per-remainder irreducibility lemma, downstream re-key of
`factorClassicalFactorsWithBound_factor_irreducible` /
`factorFactors_factor_irreducible`, wiring + trace-fixture regeneration.

Key proof-relevant identity (proved on paper, drives `piecePrimeData?`):
for a peel `t = g * h` with monic transforms `M`,
`M t = D_{lc h}(M g) * D_{lc g}(M h)` over ZZ exactly, where
`D_c(P)(x) = c^(deg P) * P(x/c)`; mod p the undilation unit exists
whenever the piece has degree >= 2 (else the parent image is not
squarefree).

## Next step

Task 3: the fresh partition producer. Start from
`liftedFactorSubsetPartition_of_toMonicPrimeData_complete`
(IntReductionMod.lean:48) and generalize the `hselected` threading to the
three derived properties, discharged for `piecePrimeData?` outputs via the
dilation transport.

## Blockers

None.
