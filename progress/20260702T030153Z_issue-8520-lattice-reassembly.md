# Lattice-tier reassembly completeness (#8520)

## Accomplished

Discharged the `reassemblyExpansionComplete` sorry in the lattice branch of
`factorLatticeFactorsWithBound_factor_irreducible`
(`HexBerlekampZassenhausMathlib/LatticeTier.lean`), stacked on the #8417
lattice-tier PR (#8517) which introduced it. Three pieces:

- **`HexBerlekampZassenhaus/Basic.lean`**: `latticeCoreFactorsWithBound_spec`
  (private structural case-split: every `some cf` is the singleton `#[core]`
  — small-mod and all-ones certification arms — or a `factorFastCoreWithBound`
  success) plus the trio
  `latticeCoreFactorsWithBound_{polyProduct,normalizeFactorSign,degree_pos}`,
  mirroring the classical companions. The CLD-split arm reuses
  `factorFastCoreWithBound_product` / `_some_normalizeFactorSign` /
  `_some_degree_pos`, all already in-tree.
- **`HexBerlekampZassenhausMathlib/IntReductionMod.lean`**: extracted the
  shared tail of `reassemblyExpansionComplete_classicalCore_of_ne_zero`
  (per-factor positive-leading-coefficient derivation + fuel bound) into
  `reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm`
  (callers supply only the irreducible, sign-normalized, positive-degree
  cover), and rewired the classical proof through it — the classical theorem
  shrank from ~120 lines to a 4-argument composition.
- **`HexBerlekampZassenhausMathlib/LatticeTier.lean`**:
  `reassemblyExpansionComplete_latticeCore_of_ne_zero` (thin composition of
  the `LatticeTier` core irreducibility lemma + the structural trio + the new
  `_of_norm` surface) and the sorry discharge at the general-lattice arm,
  supplying precision via
  `two_mul_bhksBound_squareFreeCore_lt_pow_cap_of_choosePrimeData`.

## Current frontier

LatticeTier.lean is down to the two deep BHKS obligations
(`latticeArm2_fastCore_count`, `latticeArm3_bhksSingleAllOnes_irreducible` —
the arm-3 `hclasses` sorry), which are #8417's remaining content and out of
scope here.

## Next step

The deep van Hoeij adequacy content (#8417): the L5–L10 chain for arm 3 and
the CLD count-equality for arm 2.

## Blockers

PR is stacked on #8517 (branch `issue-8417`), which is green and mergeable but
not yet merged; this PR targets that branch (or rebases onto main once #8517
lands).
