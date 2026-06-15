# Phase 4/5/6 checkpoint 57

Scope: checkpoint for the 157 PRs merged after summarize issue #7127 (closed
2026-06-14T10:53:04Z) through PR #7483 (2026-06-15T14:05). Two threads dominate,
as in checkpoint 56: the directive #2564 HO-1 substrate (now centred on the
monic `toMonicLiftData` lift-transport chain and the BHKS §5 analytic bound
chain) and the continuing broad Phase 6 docstring stream across the executable
libraries. The frontier remains directive #2564 and its HO-1 support chain.

## Landed work

157 PRs merged after checkpoint 56. Of these, ~130 are Phase 6 docstring
batches (plus a handful mislabeled `feat:` — #7131/#7132/#7136/#7137 — that are
also docstring-only). The remaining ~25 carry the substrate. Grouped by topic.

### Scale→dilate / monic-lift corrections (honest reverts)

Several PRs corrected unsound or mis-shaped bridges from the prior model rather
than patching them, continuing the scale→dilate migration flagged in checkpoint
56:

- #7157 reverted #7100's bad-vector resultant bridge to an honest assumption
  (the previously-"landed" bridge was not actually proved).
- #7196 rebuilt `bhksIndicatorCandidate?_representsIntegerFactorAtLift` as a
  genuine `RecoveredAtLift` witness.
- #7244 rerouted the `productCongruence` recovery chain to the
  `primitivePart`-of-`dilate` model (`scale c p` ≠ `dilate c p`; the congruence
  was unsound as previously stated).
- #7124 / #7126 landed the dilated-centered-lift reconstruction and the
  `factorFast` schedule-recovery transport from `henselLiftData` to
  `toMonicLiftData`.

### Monic `toMonicLiftData` lift-transport chain

The live HO-1 substrate. The forward monic correspondent (a monic factor of
`(toMonic core)` recovered from an integer factor of `core`, inverting
`primitivePart∘dilate`) and the existential lift-transport producer were
assembled across a sequence of small, non-circular steps:

- #7373 forward monic correspondent.
- #7414 `representsModP_correspondent` (mod-p representation of the monic
  correspondent `g ∣ M` from `toMonicPrimeData?`).
- #7462 transfer `RecoveredAtLift` along the monic correspondent recovery.
- #7466 instantiate monic Hensel lift transport for `toMonicLiftData`
  correspondents.
- #7468 assemble the existential `toMonicLiftData` lift-transport producer
  (this is issue #7455).
- #7463 thread the prime witness through the exhaustive branch lemmas.
- #7465 / #7467 forward `W⊆L'` refinement count core for fast-core
  irreducibility, rerouting off `lattice_eq_indicators`.
- #7472 / #7473 / #7481 / #7483 lifted-subset transport, sign-normalization
  bridge + mod-p disjointness from `choosePrimeData?`, and the non-circular
  lift-stage subset clean-half core (#7474).

### BHKS §5 analytic bound chain

- #7333 BHKS D1 final composition: `factorFast_terminates` from
  `ForwardRecoveryInputs` and closed canonical packages.
- #7340 scaled-lattice shortness certificate for corrected auxiliary
  coefficients.
- #7442 BHKS §5 analytic building blocks: strict l2-norm lower bound and
  auxiliary-factor positivity.
- #7454 reachable square-free core has nonzero constant term
  (`squareFreeCore.coeff 0 ≠ 0`).
- #7460 bridge the BHKS l2 support lower bound.

### CI

- #7334 added the `HexBerlekampZassenhausMathlib` build as the HO-1 required
  check.

### Phase 6 docstring and linter cleanup

~130 narrow, library-local docstring slices landed, covering (non-exhaustively)
HexPolyFp, HexGF2, HexGramSchmidt, HexLLL, HexPolyZ, HexHensel, HexGFq,
HexPolyMathlib, HexConway, HexArith, HexMatrix (Bareiss/Determinant/RREF/
RowEchelon), HexModArith, HexBerlekamp DistinctDegree/Factor, HexGFqField, and
HexGFqRing. The HexConway batch closed out the Lübeck/Rabin Conway-polynomial
certificate tables (`luebeckConwayPolynomialOfCoeffs_{p}_n_{monic,irreducible}`
for p in {2,3,5,7,11,13}). #7449 documented the BZ prime-scoring helpers.

## Phase state

`scripts/status.py` reports the executable dispatch front largely in Phase 6
proof-polishing: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt,
HexGF2, HexPolyZ, HexLLL, HexPolyFp, HexGFqField, HexHensel, HexConway, HexGFq,
and HexPolyMathlib are all Phase-6 ready. `HexBerlekamp` is at Phase 4.
`HexBerlekampZassenhaus` remains at Phase 1 (library scaffolding).

Mathlib-side queues stay split by dependency:

- Phase 5 ready: HexMatrixMathlib, HexModArithMathlib.
- Phase 4 ready: HexGramSchmidtMathlib, HexPolyZMathlib, HexHenselMathlib,
  HexGF2Mathlib.
- Blocked: HexLLLMathlib (waits on HexGramSchmidtMathlib ≥ 4),
  HexBerlekampMathlib (waits on HexBerlekamp ≥ 4), HexGFqMathlib (waits on
  HexGF2Mathlib ≥ 4), and HexBerlekampZassenhausMathlib (Phase 3, waits on
  `HexBerlekampZassenhaus.done_through ≥ 3`).

HexGFqRing is fully done. HexRoots/HexResultant/HexNumberField and their
Mathlib counterparts remain SPEC-ready but implementation-deferred.

## Quality metrics

Repository-wide Lean grep (excluding `.lake/`), unchanged from checkpoint 56:

- `sorry`: 68, all confined to the non-CI-built Mathlib-side layers:
  HexGF2Mathlib 23 (Field.lean 12, Basic.lean 11), HexBerlekampMathlib 19
  (Basic.lean), HexGFqMathlib 15 (GF2q.lean 8, Basic.lean 7), HexHenselMathlib 6
  (Correctness.lean), HexBerlekampZassenhausMathlib 4 (Basic.lean 2,
  IntReductionMod.lean 1, FactorSoundness.lean 1), HexMatrixMathlib 1
  (Determinant.lean). No `sorry` exists in any CI-built executable library.
- `axiom`: 0 real declarations (no line begins with `axiom`).
- `native_decide`: 0 real tactic uses. The 2 grep hits are both comment text
  (a checklist line in `HexBerlekampZassenhausMathlib/IntReductionMod.lean` and
  a line in `HexArith/Nat/Prime.lean` stating the code does *not* depend on
  `native_decide`).
- `TODO`/`FIXME`: 1 comment match, not an open proof marker.

The headline gap between goals and current state is unchanged: every remaining
`sorry` sits in the Mathlib boundary layers, which CI does not build, so a
whole-library `lake build` of those targets is expected to surface them. The
executable Mathlib-free stack carries no proof debt.

## Current frontier

Open PRs:

- #7485 `feat: BHKS §5 — reachable-core facts for the l2 bridge` (closes #7476).
- #7484 `feat: non-circular lifted representation disjointness for
  non-associated factors` (closes #7480).
- #2656 draft SPEC PR for real roots and Sturm.

Claimed / in-flight: #7477 (non-circular lifted product divisor implies support
subset).

Unclaimed work queue (excluding this summarize issue):

- #7361 descent-hypotheses producer (`HenselLiftDescentHypotheses … True True`).
  Its `depends-on: #7470` (lifted-subset uniqueness) is still **open**, so the
  short assembly it describes is not yet dischargeable.
- #7487 BHKS §5 auxiliary l2 bound via van Hoeij CLD log-bound. This is the
  corrected-shape successor to the abandoned #7440 certificate, and its body
  explicitly defers the exact statement and sub-lemma decomposition to a
  **planner** before any worker attempt. See the next section.

## Honest limitation: the BHKS §5 auxiliary domination is mis-scoped

#7440's gating feasibility analysis (Codex-confirmed) established that the
auxiliary domination `√correctedRHS^n ≤ bhksPaperAuxiliaryFactorReal core 2` is
infeasible from the `√correctedRHS` certificate — a *shape* error, not a
constant error. `cldColumnNormBound` puts coefficient-height (`‖core‖₂`) growth
on the auxiliary/log side, but in the paper split that height belongs entirely
on the coefficient-norm side; the auxiliary side is only
`n·(2C)^(n²)·(log‖core‖₂)^n`. For fixed `n` and `‖core‖₂ → ∞` the gap widens
without bound (the `4^(n²)` factor is `‖core‖₂`-independent and cannot absorb
it). Consequently:

- #7440 was closed (wrong certificate), superseded by #7487.
- #7441 (the capstone domination, currently `blocked`) must be re-pointed at the
  corrected CLD log-bound certificate before it can be discharged.
- #7487 needs a planner to scope the CLD log-bound formalization first.

The landed BHKS analytic building blocks remain valid and reusable
(`bhksPaperAuxiliaryFactorReal_pos`, the strict l2-norm lower bound, the
`1 < ‖core‖₂` reachability facts from #7439/#7454/#7460).

## Blocking structure for directive #2564

The capstone #6672 (`assemble factor_irreducible_of_nonUnit`) and the
FactorSoundness headline packaging (#6867 raw primitive package, #6868
non-associated headline contract) remain blocked behind #6771/#6774 and the
modP→lift / B-builder chains. The HO-1 CI required check #6866-class work stays
parked until `HexBerlekampZassenhausMathlib` builds green, which is impossible
while its 4 `sorry`s and the upstream Mathlib-layer debt remain. Of the live
unblocked HO-1 work, the monic `toMonicLiftData` transport chain
(#7361/#7362/#7470 cluster) and the BHKS §5 analytic chain
(#7441/#7487 cluster) are the two active fronts.

## Recommended next actions

1. Scope #7487 as a planner before any worker attempt: produce the exact CLD
   log-bound statement and a provable sub-lemma decomposition, then re-point
   #7441 at it. Do not attempt the `√correctedRHS` certificate again — it is
   the wrong shape.
2. Land #7470 (lifted-subset uniqueness) to unblock the #7361 descent-hypotheses
   producer; the #7362 partition-evidence producer follows once #7477/#7479/
   #7480 land.
3. Keep merging the non-circular lift-transport PRs (#7484, #7485, and the
   #7477 follow-ups) into the monic substrate without reintroducing the
   circular route through a prebuilt `HenselSubsetCorrespondenceHypotheses`.
4. Keep Phase 6 polish slices narrow and library-local; the executable stack is
   `sorry`-free and the remaining docstring work is the right granularity.
