# Phase 4/5/6 checkpoint 54

Scope: checkpoint for merged work after summarize issue #6863, covering the
current HO-1 / HexBerlekampZassenhaus recovery front, BHKS / Resultant
divisibility chain, HexPolyFp SquareFree normalized-provider rework, Phase 5
library bumps, and Phase 6 polish stream.

## Landed work

### BHKS and Resultant common-factor substrate

The resultant chain advanced from named Sylvester syzygies to a public
map-to-`ZMod (p^k)` wrapper. The useful theorem is now in the Mathlib layer, but
the concrete BHKS Lemma 3.2 composition still has to connect the CLD auxiliary
polynomial to that wrapper.

- #6885 added the first Sylvester common-factor column-reduction step.
- #6899 assembled the common-factor Sylvester column reduction.
- #6917 packaged explicit-witness common-factor resultant divisibility.
- #6927 added the public map-to-`ZMod` resultant divisibility wrapper.
- #6900 recorded the current heartbeat-timeout debugging convention for heavy
  Mathlib-layer proofs.
- #6916, #6921, and #6928/#6931 reviewed the Sylvester/resultant PRs.

Current frontier: #6844 is claimed for the BHKS Lemma 3.2 composition over the
concrete CLD auxiliary polynomial. It should consume #6927's public wrapper,
not reintroduce the old shortcut from "shared factor modulo `p^k`" directly to
`p^(k*d)` resultant divisibility.

### BZ recovery and HO-1 support chain

The BZ proof model kept moving away from stale scaled-recombination assumptions
toward recovered-coordinate data.

- #6891 added the recovered lift representation carrier.
- #6920 decoupled stale scaled-recovery lemmas from the recovered
  representation predicate.
- #6924 reviewed the recovery decoupling.
- #6932 replanned the next BZ recovery step around a recovered-coordinate Prop
  carrier.

Current frontier: #6938 is the open PR for #6932. Downstream issues #6890 and
#6840 are blocked on that carrier work, and the larger scale-to-dilate migration
still gates #6819, #6804, #6773, #6786, and the fast-BHKS coverage path.

### HexPolyFp SquareFree normalized-provider rework

The SquareFree front clarified an important negative fact: the raw Yun
level-state provider is false because executable `DensePoly.gcd` can return a
non-one scalar. The sound direction is the normalized-provider route already
available in-tree.

- #6875 added constant-tail support for the SquareFree implementation.
- #6908 proved the derivative-split quotient base case needed by the attempted
  raw-c reachability chain.
- #6915 reviewed that derivative-split base.
- #6904 was then closed as unsound: the raw `YunDerivativeActiveLevelStateProvider`
  premise fails on concrete finite-field examples.
- #6902 has been returned to replan because it depended on that false direct
  level provider. The remaining route is #6889 -> #6883, using the existing
  normalized provider instead of proving raw reachability.

Current frontier: #6889 is blocked by the stale #6902 dependency until a
planner rebases it onto the normalized provider. #6883 and #6376 remain behind
that chain.

### Phase 5 completions and Phase 6 polish

Several mature libraries moved through Phase 5 and into the broad Phase 6
polish queue, while narrow doc/API cleanup continued.

- #6909 completed HexLLL Phase 5.
- #6910 completed HexPolyZ Phase 5 and bumped `done_through` to 5.
- #6926 completed HexGramSchmidt Phase 5 and bumped it to Phase 6 readiness.
- #6876 polished HexMatrix determinant docs and annotations.
- #6879 polished HexPoly Euclid docs and annotations.
- #6884 polished HexPolyFp quotient docs and annotations.
- #6892 polished HexGF2 field and irreducibility docs.
- #6905, #6919, #6922, and #6929/#6934 reviewed or recorded review metadata for
  the Phase 5/6 polish stream.

Current `scripts/status.py` state: HexGramSchmidt, HexPolyZ, HexLLL, HexPolyFp,
HexGF2, HexPoly, HexMatrix, HexArith, HexModArith, HexHensel, HexConway,
HexGFq, HexGFqField, and HexPolyMathlib are ready for Phase 6. The Mathlib-side
Phase 4/5 queues remain split by dependencies: HexMatrixMathlib and
HexModArithMathlib are ready for Phase 5; HexGramSchmidtMathlib,
HexPolyZMathlib, HexHenselMathlib, and HexGF2Mathlib are ready for Phase 4;
HexLLLMathlib, HexBerlekampMathlib, HexGFqMathlib, and
HexBerlekampZassenhausMathlib are still blocked by their prerequisite
libraries.

## Current frontier

Open PRs:

- #6938, `feat: switch BZ lift predicate carrier`, closing #6932.
- #6937, `feat: polish HexConway wrapper automation`, closing #6933.
- #6934, `review: PR 6926 HexGramSchmidt Phase 5 bump`, closing #6929.
- #6931, `review PR #6927 resultant wrapper`, closing #6928.
- #2656, draft SPEC PR for real roots and Sturm.

Claimed work:

- #6844, BHKS Lemma 3.2 composition over the CLD auxiliary polynomial.
- #6930, this checkpoint report.

Blocked or replan fronts:

- Directive #2564 remains the top blocked target, with the HO-1 capstone #6672
  waiting behind fast-BHKS coverage #6771 and slow-modular irreducibility #6774.
- The BZ recovered-coordinate carrier work #6932/#6938 gates #6890 and #6840,
  which in turn gate the scale-to-dilate migration chain.
- #6855, the `HexBerlekampZassenhausMathlib.Basic` build repair, remains blocked
  behind #6840.
- #6844 is the live resultant consumer; downstream fast-BHKS separation
  issues #6779, #6783, #6777, and #6786 remain blocked until their respective
  BZ/BHKS prerequisites close.
- #6902 needs planner rebase or retirement after #6904's unsoundness finding;
  #6889/#6883 should be expressed directly in terms of the normalized
  SquareFree provider.

## Recommended next actions

1. Let #6938 land, then unblock #6890 and #6840 before retrying #6855.
2. Continue #6844 only through #6927's map-to-`ZMod` resultant theorem and the
   concrete CLD coefficient/divisibility facts.
3. Replan #6902/#6889 so the SquareFree weighted-product route no longer
   depends on the false raw level-state provider.
4. Keep Phase 6 polish issues narrow and library-local; the status queue is now
   broad enough that small, reviewable slices matter more than large sweeps.
