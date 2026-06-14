# Phase 4/5/6 checkpoint 55

Scope: checkpoint for merged work after summarize issue #6930, covering the
CLD / resultant valuation substrate for BHKS Lemma 3.2, the BZ recovered-
coordinate recovery front, the HexPolyFp SquareFree / Yun / monicGcd repair,
and the broad Phase 6 docstring-polish stream. The frontier remains
directive #2564 and its HO-1 support chain.

## Landed work

Thirty-three PRs merged after checkpoint 54. Grouped by topic rather than
listed one-by-one.

### CLD / resultant valuation chain (BHKS Lemma 3.2 substrate)

The resultant chain advanced from the map-to-`ZMod` wrapper landed in
checkpoint 54 toward the concrete CLD (coefficient-of-logarithmic-derivative)
auxiliary-polynomial composition that BHKS Lemma 3.2 needs.

- #6952 added executable CLD cut decomposition lemmas.
- #6961 proved the abstract CLD Sylvester valuation lemma.
- #6967 added the Mathlib-facing CLD auxiliary coefficient decomposition.
- #6995 proved monic Euclidean reconstruction for `cldQuotientMod`.
- #7011 connected `cldQuotientMod` to the logarithmic-derivative congruence.
- #6966 and #7019 recorded reviews of the CLD PRs.

Current frontier: #6978 (relate the BHKS auxiliary polynomial to the CLD
quotient cuts) is claimed and is the live consumer that has to close the
gap between the CLD substrate and the resultant divisibility wrapper.

### BZ recovery and recovered-coordinate carrier

The BZ proof model continued migrating recovery onto monic, recovered-
coordinate data and away from stale scaled-recombination framing.

- #6951 repaired multiplicative closure for the recovered lifted predicate.
- #6968 aligned the lifted representation `mul` wrapper.
- #6969 migrated the early recovery package to monic coordinates.
- #6974 recovered the Hensel lift transport.
- #6980 added the recovered support partition field.
- #7017 added a non-monic recovered-candidate guard fixture.
- #6962 recorded the review of the multiplicative-closure repair.

Current frontier: the recovered-candidate carrier work is now consolidated on
#7024 (enrich `RecoveredAtLift` with a bounded monic field, re-thread `toMonic`
precision, then migrate search to `liftedRecoveryCandidate`). Two source-
verified premise checks converged here: the competing #7030 was closed as
superseded, and #7024 is the single owner of the `RecoveredAtLift` structure
and its consumer sites. #7039 (`BZ recovery: add lifted candidate equality
evidence`) is the open PR on this front.

### HexPolyFp SquareFree / Yun / monicGcd repair

The SquareFree repair followed the normalized-provider route identified in
checkpoint 54 as the only sound direction (the raw Yun level-state provider is
false because executable `DensePoly.gcd` can return a non-one scalar).

- #6946 rewired the Yun weighted product to the normalized invariant.
- #7003 added the verified `monicGcd` API for the square-free scalar-leak fix.

Current frontier: #7040 (`fix: swap Yun square-free gcd sites to monicGcd and
re-ground providers`) is the open residual PR.

### Phase 6 docstring polish

The Phase 6 polish queue is broad; nine library-local docstring slices landed,
each narrow and reviewable.

- #6985 HexLLL `Basic.lean` public API.
- #6992 HexGramSchmidt `Update.lean`; #6994 HexGramSchmidt `Int.lean`.
- #7007 HexArith `ExtGcd` Bezout projection theorems.
- #7020 HexMatrix RREF singleton row combination.
- #7025 HexPolyZ `Mignotte.lean` bound theorems; #7028 HexPolyZ `Basic.lean`.
- #7031 HexModArith `ZMod64` theorem API.
- #7032 HexPoly `Euclid.lean` and `Operations.lean` theorems.
- #6997, #6998, and #7006 recorded reviews of the polish PRs.

### Process and tooling

- #6957 recorded the `/work` triage of #6779, #6883, #6954.
- #7008 warned that `tee` masks the `lake build` exit code in the baseline
  check (a real false-green hazard for Mathlib-layer verification).
- #6950 and #6970 recorded review metadata.

## Phase state

`scripts/status.py` reports the dispatch front largely in Phase 6
proof-polishing: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt,
HexGF2, HexPolyZ, HexLLL, HexPolyFp, HexGFqField, HexHensel, HexConway,
HexGFq, and HexPolyMathlib are all Phase-6 ready. `HexBerlekamp` is at Phase 4.
`HexBerlekampZassenhaus` remains at Phase 1 (library scaffolding).

Mathlib-side queues stay split by dependency:

- Phase 5 ready: HexMatrixMathlib, HexModArithMathlib.
- Phase 4 ready: HexGramSchmidtMathlib, HexPolyZMathlib, HexHenselMathlib,
  HexGF2Mathlib.
- Blocked: HexLLLMathlib (waits on HexGramSchmidtMathlib >= 4),
  HexBerlekampMathlib (waits on HexBerlekamp >= 4), HexGFqMathlib (waits on
  HexGF2Mathlib >= 4), and HexBerlekampZassenhausMathlib (Phase 3, waits on
  `HexBerlekampZassenhaus.done_through >= 3`).

HexGFqRing is fully done. HexRoots/HexResultant/HexNumberField and their
Mathlib counterparts remain SPEC-ready but implementation-deferred.

## Quality metrics

Repository-wide Lean grep (excluding `.lake/`):

- `sorry`: 68, all confined to the non-CI-built Mathlib-side layers:
  HexGF2Mathlib 23, HexBerlekampMathlib 19, HexGFqMathlib 15,
  HexHenselMathlib 6, HexBerlekampZassenhausMathlib 4, HexMatrixMathlib 1.
  No `sorry` exists in any CI-built executable library.
- `axiom`: 0 real declarations. The 9 grep hits from planning time and the 7
  seen this session are all docstring/comment mentions (e.g. `Lean.Grind`
  axiom-field witnesses in `HexGFqRing/Operations.lean` and a checklist line in
  `HexBerlekampZassenhausMathlib/IntReductionMod.lean`), not `axiom`
  declarations.
- `native_decide`: 0 real tactic uses. The 2 grep hits are both comment text
  (one a checklist line, one in `HexArith/Nat/Prime.lean` stating the code does
  *not* depend on `native_decide`).
- `TODO`/`FIXME`: 1, a comment match, not an open work marker on a proof.

The headline gap between goals and current state is unchanged: every remaining
`sorry` sits in the Mathlib boundary layers, which CI does not build, so a
whole-library `lake build` of those targets is expected to surface them. The
executable Mathlib-free stack carries no proof debt.

## Current frontier

Open PRs:

- #7039 `BZ recovery: add lifted candidate equality evidence`.
- #7040 `fix: swap Yun square-free gcd sites to monicGcd and re-ground
  providers` (residual of #6983).
- #7041 `doc: record #6824 premise check and harden Mathlib-build baseline
  guidance`.
- #7038 `chore: record review of PR 7032`.
- #7018 `feat: measure the Isabelle-certified comparator floor instead of
  hardcoding it`.
- #2656 draft SPEC PR for real roots and Sturm.

Claimed work:

- #7024 BZ recovery `RecoveredAtLift` enrichment and `liftedRecoveryCandidate`
  migration (single owner of the recovered-carrier region).
- #6978 relate the BHKS auxiliary polynomial to the CLD quotient cuts.
- #6866 CI required-check for HO-1 on the `HexBerlekampZassenhausMathlib`
  build.

Blocking structure for directive #2564:

- The HO-1 capstone #6672 and the FactorSoundness headline packaging
  (#6867, #6868) remain blocked behind the recovered-coordinate and CLD/
  resultant chains.
- The recovered-carrier migration (#7024, with #7039 in flight) blocks the
  downstream scale-to-dilate consumers, including #6773 (slow-modular initial
  lifted partition evidence), which is explicitly not worker-ready until its
  dilation-recovery dependency closes.
- The CLD/resultant valuation chain (#6978, plus #6979 and #6949) must connect
  the CLD substrate landed this cycle to the map-to-`ZMod` resultant wrapper.
- The HO-1 CI required-check #6866 stays blocked until
  `HexBerlekampZassenhausMathlib` builds green, currently impossible while its
  4 `sorry`s and the upstream Mathlib-layer debt remain.

## Recommended next actions

1. Land #7039, then drive #7024's carrier enrichment so the
   `liftedRecoveryCandidate` migration can unblock the downstream
   scale-to-dilate consumers.
2. Continue #6978 strictly through the CLD substrate (#6952/#6961/#6967/#6995/
   #7011) into the existing map-to-`ZMod` resultant wrapper; do not reintroduce
   a direct shortcut from "shared factor mod `p^k`" to `p^(k*d)` divisibility.
3. Keep #6866 parked until `HexBerlekampZassenhausMathlib` is `sorry`-free and
   builds; requiring HO-1 before then would wedge CI.
4. Keep Phase 6 polish slices narrow and library-local; the queue is broad
   enough that small reviewable slices remain the right granularity.
