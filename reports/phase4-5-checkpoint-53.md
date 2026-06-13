# Phase 4/5/6 checkpoint 53

Scope: checkpoint for merged work after summarize issue #6123, covering the
current HO-1 / HexBerlekampZassenhaus dilation recovery, BHKS / Resultant
substrate, HexPolyFp SquareFree provider, HexLLL steering, and Phase 6 polish
frontiers.

## Landed work

### HO-1 and HexBerlekampZassenhaus dilation recovery

The BZ front moved from fallback cleanup into the non-monic recombination
repair: the executable slow path now recovers candidates by dilating the lifted
product back out of the `toMonic` coordinate system, while the Mathlib proof
model is being migrated to that same shape.

- #6595 rewired `factor` as `factorFast -> factorSlowModular ->
  factorSlowTrial`, and #6602/#6605/#6606 made the slow modular path
  option-native instead of falling through silently.
- #6731, #6733, #6734, #6739, #6747, #6749, and #6761 closed the residual
  slow-trial / Hensel descent / raw irreducibility substrate.
- #6802 fixed the executable non-monic slow-path recombination bug by replacing
  scalar scaling with `ZPoly.dilate`.
- #6808 and #6813 added the `ZPoly.dilate` Mathlib correspondence, the
  `toMonic` inverse-factor keystone, and Gauss/content bridges needed by the
  proof-side migration.
- #6821, #6838/#6860, and #6854 added the recovered lifted-candidate surface and
  precision-gated equality bridge.
- #6797, #6825, #6831, and #6833 finished the mod-`p` cover substrate through
  `modPFactor_index_cover`.

Current blocking point: `HexBerlekampZassenhausMathlib.Basic` is red on main at
the old scale-to-dilate recombination-coverage seam. The direct repair chain is
#6839 -> #6840 -> #6855; downstream lifted partition and fast-BHKS work should
stay blocked until that seam is green.

### BHKS support and Resultant common-factor substrate

The BHKS proof front kept separating genuine mathematical obligations from
setup plumbing. The CLD / bad-vector side now has more of the bridge data
named, while the missing p-adic resultant exponent has been decomposed into
Sylvester-column mathematics.

- #6270, #6274, #6275, #6296, #6332, #6347, #6349, #6357/#6358, #6362, and
  #6388 built the bad-vector bridge data, cap separation, and resultant field
  infrastructure.
- #6400 through #6506 packaged the corrected BHKS cap inputs, recovery-tail
  inputs, paper-threshold comparisons, and HO-4 theorem-name surfaces.
- #6651, #6679, #6793, #6820, #6823, and #6852 added the later D1/D2 and van
  Hoeij-facing bridge surfaces.
- #6850 and #6853 added determinant divisibility and integer-witness extraction
  substrate for common-factor resultant divisibility.
- #6856/#6859 is the open PR adding the first Sylvester common-factor syzygy
  identities; #6857, #6858, and #6849 are the planned column-transform and
  public p-adic wrapper chain afterward.

The main BHKS Lemma 3.2 composition issue #6844 is correctly blocked on #6849.
It should not be attacked directly by assuming the old "shared factor mod
`p^k` therefore `p^(k*d)` resultant divisibility" shortcut.

### HexPolyFp SquareFree provider work

SquareFree work narrowed from raw normalized-tail cleanup to the real remaining
raw executable-state obligation in the Yun recursion.

- #6232, #6245, #6287, #6298, #6312, #6318, #6331, #6373, and #6426 built the
  normalized provider and tail-product substrate.
- #6662, #6667, #6681, #6689, #6697, #6698, #6702, #6703, #6707, #6721, and
  #6728 added the scalar-synchronization and normalized Yun completion chain.
- #6812, #6826, #6830, #6832, and #6841 bridged raw Yun tails to normalized
  derivative-active providers and removed stale raw-tail induction assumptions
  from several consumers.
- #6837 packaged the single raw-state provider and refactored weighted-product
  consumers to derive the older level/raw-tail providers internally.

The current ready issue is #6862: prove a closed raw-state provider strong
enough for the initial square-free decomposition path, then remove the explicit
public `hrawState` argument from `squareFree_weightedProduct`. The older
packaging issue #6376 is blocked until #6862 lands.

### HexLLL steering, certified dispatch, and performance

The LLL front moved from comparator evidence to a certified external-provider
and approximation-steered default reducer, while keeping the harsh-cubic
performance question evidence-driven.

- #6638, #6640/#6646, #6647, #6652, #6657, and #6666 established the five-curve
  comparator plot and Isabelle-certified/fpLLL comparator path.
- #6604, #6620, #6622, #6624, #6627, #6629, #6633, and #6634 added the
  eta-parameterized reducedness, same-lattice bridge, provider hook,
  `certCheck`, and public dispatch surface.
- #6752, #6755, #6762, #6763, #6765, #6766, #6784, #6809, and #6822 refined the
  interval and approximation-steered dispatch, including the unified `n >= 30`
  routing and float-drift margin fix.
- #6775 extended the certified harsh-cubic ladder to `n = 60` and `65`, and the
  accompanying report/spec PRs refreshed the comparator evidence.

Fresh LLL work should continue from measured evidence. The steered path is now
the default dispatch for the large-rung regime; broad redesign issues are less
useful than narrow fixes tied to a specific comparator regression.

### Matrix, Gram-Schmidt, and Phase 6 API polish

The matrix/Gram-Schmidt and API-polish streams kept closing targeted proof and
public-surface gaps while the BZ/BHKS fronts consumed the results.

- #6247, #6235, #6313, #6317, #6325, #6356, #6516, #6524, #6528, #6531,
  #6539/#6540/#6544/#6545, #6548, #6553/#6554/#6555, and #6561 advanced the
  no-pivot Gram/Bareiss/Schur bridge and initial Gram row-entry theorem chain.
- #6277, #6278, #6289, #6293, #6328, and related Phase 6 Matrix work clarified
  determinant/Bareiss public surfaces and conformance examples.
- #6256, #6320/#6324, #6352, #6061/#6063/#6082/#6083/#6102/#6109, and related
  GFq/GF2/GFqField work kept finite-field APIs in small polish slices.
- #6295, #6306/#6308/#6309, #6327, #6343, #6367, and #6248 added conservative
  proof-mode automation and wrapper coverage across HexArith, HexModArith, and
  lower arithmetic libraries.

This work is mostly substrate/polish now. New issues should stay narrow and
consumer-driven.

## Current frontier

Open PRs:

- #6865, `feat: expose bad-vector forward coprimality`, closing #6846.
- #6860, `BZ recovery: prove precision-gated liftedRecoveryCandidate equality`,
  closing #6838.
- #6859, `feat: add Sylvester common-factor syzygy`, closing #6856.
- #2656, draft SPEC PR for real roots and Sturm.

Ready or claimed work:

- #6862 is claimed for the closed raw-state SquareFree provider needed before
  #6376 can package the remaining public proof wrappers.
- This checkpoint issue #6863 is claimed for the current summary report.

Blocked fronts:

- The top directive #2564 remains dependency-blocked, not abandoned.
- `HexBerlekampZassenhausMathlib.Basic` build repair is blocked through
  #6838/#6839/#6840 into #6855; #6804, #6819, #6773, #6786, and the fast-BHKS
  coverage chain remain downstream of that dilation migration.
- Resultant public divisibility is #6856 -> #6857 -> #6858 -> #6849; BHKS Lemma
  3.2 composition #6844 waits behind #6849.
- Fast-BHKS separation and coverage remain blocked behind #6844, #6846, #6783,
  #6779, #6777, #6786, and #6774 before the HO-1 capstone #6672 can close.
- HexPolyFp public SquareFree packaging #6376 and #6079 wait for #6862.

## Recommended next actions

1. Let #6860 land, then work #6839 before #6840/#6855; the Basic build failure
   is a real scale-to-dilate proof-model mismatch, not a local rewrite typo.
2. Let #6859 land before dispatching #6857; the resultant chain is deliberately
   staged so the determinant-column theorem can consume named syzygy directions.
3. Keep #6844 blocked until #6849 supplies the public `ZMod (p^k)` wrapper with
   exponent `k * d`.
4. Finish #6862 before reopening #6376 or #6079; normalized SquareFree providers
   alone do not close the raw executable-tail facts.
5. Continue LLL performance work only from fresh comparator evidence and small
   implementation hypotheses; the certified/steered dispatch surface is now in
   place.
