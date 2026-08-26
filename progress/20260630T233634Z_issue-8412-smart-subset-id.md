# Issue #8412: identify the executable recombination candidate with its subset

## Accomplished
Added (in `HexBerlekampZassenhausMathlib/Basic.lean`, after the
`liftedRecoveryCandidate` namespace, ~line 5685) the identification of the
size-ordered (smart) recombination enumerator splits with proof-side
`LiftedFactorSubset`s:

- `subsetSplits_nil_left_mem` — `([], xs) ∈ subsetSplits xs`.
- `subsetsOfSizeWithComplement_mem_subsetSplits` — every size-ordered split is
  also a `subsetSplits` member (the two enumerators range over the same
  order-preserving partitions). This is the bridge that lets the smart search
  reuse the existing `subsetSplits` mask machinery.
- `subsetsOfSizeWithComplement_cons_mem_subsetSplitsWithFirst` — the head-forced
  smart split lies in `subsetSplitsWithFirst`.
- `subsetsOfSizeWithComplement_liftedFactors_exists_subset` — THE deliverable:
  for a smart split `(head :: sc_sel, sc_rest)` over the full lifted-factor list,
  there is `S` with `head :: sc_sel = liftedSubsetSelectedList d S`,
  `polyProduct (head :: sc_sel) = liftedFactorProduct d S`, and the executable
  scaled candidate = `liftedRecoveryCandidate core d S`.
- `liftedSubsetSelectedList_injective` — distinctness step (from
  `Function.Injective (liftedFactor d)`).
- `subsetsOfSizeWithComplement_liftedFactors_exists_unique_subset` — packages
  existence + uniqueness, taking injectivity as an explicit hypothesis (the same
  one `RecoveredScaledSearch.covers` carries), per the issue's Care note.

## Key decision
Existence of the identifying subset needs NO injectivity: the mask route
reconstructs the subset from the matched *index* list (intrinsically `Nodup`),
not from factor values. Injectivity is genuinely needed only for *uniqueness*,
which is where the Care-note hypothesis lands. Both forms are provided.

## Verification
`lake build HexBerlekampZassenhausMathlib` completes green (0 errors); no new
warnings in the added range; no sorry/axiom/native_decide in added lines.

## Next step
#8413 consumes these to walk the `scaledRecombinationSmart*` recursion (the
soundness side already has `scaledRecombinationSmart*_product`).
