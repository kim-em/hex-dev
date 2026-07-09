# Issue 8625 D2: piece producer complete; task-4 induction underway

## Accomplished (this session)

- Phase-2 re-key COMPLETE: the entire certification cone accepts
  `ModPFactorization` (SubsetCoprimality leaves, ForwardHenselTransport,
  MonicCorrespondent, ToMonicUniqueness chain, Transport producers,
  IntReductionMod roots incl.
  `classicalCoreFactorsWithBound_factor_irreducible_of_validBound`).
  Witness-keyed entry wrappers construct bundles; monorepo green.
- `piecePrimeData?` is now SELF-VERIFYING (unit check `c⁻¹*c == 1`, monic +
  degree-≥1 factor guards, product == piece monic image, isGoodPrime) and
  `@[expose]`d; deg-0 pieces decline in the aux recursion. Spike: 108/0
  correct, wallclock unchanged (1.24-1.28x split-family wins).
- Task 3 COMPLETE: `modPFactorization_of_piecePrimeData`
  (ModPFactorization.lean) — bundle for the piece from the guards +
  `irreducible_toMathlibPolynomial_monicDilate` (unit-substitution
  transport via `algEquivCMulXAddC`), `nodup_of_factorProduct_no_squared`,
  `monic_modP_of_monic`, `natDegree_toPolynomial_liftToZ_pos`,
  `coeff_monicDilate`/`toMathlibPolynomial_monicDilate`. Hypotheses: parent
  primality + per-seed irreducibility (both parent-bundle fields).

## Current frontier (task 4)

The per-remainder irreducibility induction
`classicalCoreFactorsRecursiveAux_factor_irreducible` over fuel. Node
invariant: g ≠ 0, primitive, lc pos, squarefree (toPolynomial), pos degree,
`hval : ModPFactorization (toMonic g).monic pd`. Branches:
- deg = 0: returns none — vacuous.
- deg = 1: `some #[g]` — need "primitive positive-lc linear is irreducible"
  (look near TrialProofs / IntReductionMod linear lemmas).
- r = 1: `some #[g]` — mod-q irreducibility of the monic transform (bundle:
  singleton factor list + product congruence) descends to ℤ; use the
  descent core (`IntReductionMod/Descent`) +
  `zpolyIrreducible_of_toMonicMonic_irreducible` (IntReductionMod:~225).
- ladder-split: per piece, `piecePrimeData? = some` (else none — vacuous);
  child bundle := `modPFactorization_of_piecePrimeData`; child invariant:
  * seeds ⊆ parent factorsModP: NEW scan-spec lemmas (subFloorPeelSize →
    subFloorPeel? → subFloorScan → reliftLadder membership;
    `subsetsOfSizeWithComplement_mem_subsetSplits`
    (RecombinationCandidate.lean:87) + `List.of_mem_zip` discharge the
    per-level side).
  * candidate lc-pos/primitivity: fast path monic (guard in branch
    condition), slow path `normalizeFactorSign (primitivePart ...)`
    (`leadingCoeff_normalizeFactorSign_nonneg` + `primitivePart_primitive`;
    nonzero via product identity).
  * remainder + all pieces: divisibility of the node target via the ladder
    product lemma (`reliftLadder_polyProduct`, proved) → primitive/
    squarefree/deg facts descend (zpoly_primitive_of_dvd_primitive_basic,
    Squarefree.squarefree_of_dvd).
  * per-seed irreducibility for the child call: parent bundle
    `.irreducible` per-index → per-mem.
- floor: `classicalCoreFactorsWithBound g B pd` → the (now bundle-keyed)
  validBound root; B-side conditions from the node's own Mignotte
  (B?.getD ...) — mirror the `_of_bound`/natural wrappers' discharge.

Then task 5: re-key `classicalCoreFactorsRecursive` entry (mirror
`factorClassicalFactorsWithBound_factor_irreducible`), flip
`factorClassicalFactorsWithBound` + the traced variant to the recursion,
re-key `factorFactors_factor_irreducible` (LatticeTier:998), regenerate
trace fixtures, run conformance (bz_flint), bench targets, SPEC subsection,
PR (spike file also carries the reB/steps instrumentation to keep).

## Blockers

None.
