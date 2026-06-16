# Phase 4/5/6 checkpoint 58

Scope: checkpoint for the 44 PRs merged after summarize issue #7459 (closed
2026-06-15T15:02:49Z) through PR #7595 (2026-06-16T14:31). Two substrate threads
dominate, both feeding directive #2564 (HO-1): the slow-path
toMonic / monic-descent rebuild and the BHKS §5 joint-recovery / CLD-bound
chain. A new fast-path thread opened at the end of the window: the #7590
cut-route decision retired the false first-fail prefix cut and planned the
proof-facing cut-separation chain (#7591–#7594), now the entire live feature
queue. Phase 6 executable-API polish continues as a steady background stream.
The frontier remains directive #2564 and its HO-1 support chains.

## Landed work

44 PRs merged after checkpoint 57. Grouped by topic.

### Slow-path toMonic / monic-descent substrate rebuild

The dominant landed theme. The recombination substrate was re-keyed off the
monic-descent / `toMonicPrimeData` correspondence, and the stale `scale`-based
support fields were retired in favour of the `primitivePart∘dilate` monic
model:

- #7504 `toMonicLiftData` lifted-subset uniqueness
  (`HenselSubsetCorrespondence.unique_subset`) from Hensel-lift injectivity.
- #7522 monic-correspondent lifted descent carrier; #7535
  `associated_of_associated_monicCorrespondent` and #7536 inverse correspondent
  `exists_dvd_core_of_dvd_toMonic` (the #7362 `pairwise_disjoint` / cover
  bridges).
- #7524 rebuild `toMonicPrimeData` correspondence from monic descent; #7529
  update slow-path `toMonic` wrappers to the monic-descent API; #7564 re-key the
  slow modular exhaustive branch to `toMonicPrimeData`.
- #7565 / #7589 produce the `toMonic` (resp. `toMonicPrimeData`) Hensel recovery
  substrate from core facts.
- #7546 produce `InitialLiftedFactorSubsetPartitionEvidence` at `toMonicLiftData`;
  #7543 recovered-candidate support projections for lifted partitions; #7556
  narrow Hensel recovery `exists_subset` to sign-normalized factors.
- Stale-field cleanups: #7511 / #7531 drop the scaled / unscaled
  `recombinationCandidate` support field from initial lift evidence; #7528 retire
  scaled lifted partition support; #7573 replace the `toMonic` unscaled support
  field; #7545 retire the total slow raw-factor helper; #7518 expose
  recovered-coordinate scaled-search proof surfaces.

### BHKS §5 joint recovery + CLD bound chain

The analytic l2/CLD bound chain, now expressed through the joint-recovery
wrappers at `C := 2`:

- #7485 reachable-core facts for the l2 bridge; #7507 CLD column-norm magnitude
  bound (sub-piece 2); #7510 wire `‖aux‖₂² ≤ cldColumnNormBound` (sub-piece 1 of
  #7497).
- #7547 BHKS coefficient log absorption under the log floor; #7553 sharpen it
  from the strict l2 norm; #7562 joint auxiliary paper bound.
- #7523 resolve the BHKS joint-bound small-degree side condition; #7552 joint
  `Recovery` wrappers; #7566 joint recovery threshold surface; #7571 repoint the
  BHKS capstone to the joint `Recovery` wrapper at `C := 2`.
- Non-circular lift-transport bridges: #7490 substitution by a unit reflects
  polynomial divisibility (`X ↦ u·X`); #7491 non-circular lifted product divisor
  implies support subset; #7498 non-circular recovered-candidate equality
  wrapper (#7479).

### Fast-path cut-separation route (new this window)

- #7595 (planner) decided the BHKS cut-separation route. The #7590 worker
  decision rejected the false first-fail prefix cut: it is false on the known
  LLL-reduced witness, and sorting rows by norm would require a fresh
  Gram-Schmidt-coordinate semantic proof. The sound route keeps the per-row
  executable Gram-Schmidt cut in `Hex.bhksProjectedRows` and makes the needed
  prefix behaviour a proof-facing `CutSeparation` / van-Hoeij gap certificate.
  The route was decomposed into #7591 (trace + LLL span bridge, claimed) →
  #7592 (cut-separation prefix certificate) → #7593 (place true-factor CLD
  vectors) → #7594 (produce `CutProjectionHypotheses`).
- #7576 rejected #7575 as an unsound `CutRetention` target (progress note only).

### Phase 6 foundational-API polish

- #7586 HexGF2 Euclid gcd/inverse API; #7587 HexPolyZ unit / rational-cast API;
  #7588 HexModArithMathlib ZMod64 projection simp lemmas; #7567 HexMatrix
  identity simp API (+ its #7567 review verdict); #7493 HexMatrix
  `Determinant.lean` docstrings for the column/row add-and-duplicate cluster.

### Doc / skill gotchas, reviews, chores

- #7557 sharpen the `toPolynomial`-namespace rewrite gotcha and #7576 note the
  stale-`.olean` gotcha, both in the Mathlib-boundary skill; #7554 record the
  unsatisfiable-coverage-quantifier gotcha from the #7550 diagnosis.
- #7501 review verdict for the dilation / unit-substitution reflection cluster;
  #7526 validate the scaled-recovery migration plan; #7548 / #7570 progress
  notes for the #6771 and #7561 premise checks (the latter skipped to replan).

## Phase state

`scripts/status.py` reports the executable dispatch front in Phase 6
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

Repository-wide Lean grep (excluding `.lake/`), unchanged from checkpoint 57:

- `sorry`: 68, all confined to the non-CI-built Mathlib-side layers:
  HexBerlekampMathlib 19 (Basic.lean), HexGF2Mathlib 23 (Field.lean 12,
  Basic.lean 11), HexGFqMathlib 15 (GF2q.lean 8, Basic.lean 7),
  HexHenselMathlib 6 (Correctness.lean), HexBerlekampZassenhausMathlib 4
  (Basic.lean 2, IntReductionMod.lean 1, FactorSoundness.lean 1),
  HexMatrixMathlib 1 (Determinant.lean). No `sorry` exists in any CI-built
  executable library.
- `axiom`: 0 real declarations (no line begins with `axiom`).
- `native_decide`: 0 real tactic uses. The 2 grep hits are both comment text
  (a checklist line in `HexBerlekampZassenhausMathlib/IntReductionMod.lean` and
  a line in `HexArith/Nat/Prime.lean` stating the code does *not* depend on
  `native_decide`).
- `TODO`/`FIXME`: 1 comment match, not an open proof marker.

The headline gap between goals and current state is unchanged: every remaining
`sorry` sits in the Mathlib boundary layers, which CI does not build, so a
whole-library `lake build` of those targets surfaces them. The executable
Mathlib-free stack carries no proof debt. The 44 PRs in this window moved
substrate and API surface without retiring any of these `sorry`s — they are
support work for the directive #2564 capstone, not the capstone itself.

## Current frontier

Open PRs:

- #7600 `feat: re-expose toPolynomial one/neg/sub simp surface at ZPoly bridge`.
- #2656 draft SPEC PR for real roots and Sturm.

Claimed / in-flight: #7591 (BHKS projected-row trace + LLL span bridge), the
head of the fast-path cut-separation chain.

Unclaimed feature queue (excluding this summarize issue): #7599 (FpPoly eval
simp surface) and #7601 (DensePoly eval additive homomorphism simp surface) —
two independent Phase 6 polish items. All other open feature issues are
`blocked`: the cut chain #7592/#7593/#7594 (behind #7591), and the directive
#2564 capstone cluster #6771/#6672/#6867/#6868/#6779/#4818/#4172/#6246.

## Blocking structure for directive #2564

The two headline `sorry`s are the directive #2564 capstone:
`factor_irreducible_of_nonUnit` in
`HexBerlekampZassenhausMathlib/FactorSoundness.lean` and
`Hex.ZPoly.isIrreducible_iff` in `HexBerlekampZassenhausMathlib/Basic.lean`.

Two support fronts feed them, neither yet at the capstone:

1. **Slow path** — the toMonic / monic-descent substrate is now built
   (this window's dominant theme), but its capstone consumers #6771
   (fast-BHKS assembly via forward count) and #6672 (assemble
   `factor_irreducible_of_nonUnit`) remain `blocked`, along with the
   FactorSoundness packaging #6867/#6868.
2. **Fast path** — the #7590 decision opened the cut-separation route as the
   sound replacement for the false prefix cut. The entire unblocked critical
   path is now the #7591 → #7592 → #7593 → #7594 chain feeding #6771.

## Recommended next actions

1. Land #7591 (trace + LLL span bridge) to unblock the cut-separation prefix
   certificate #7592; the #7593/#7594 chain follows, then #6771.
2. Keep the toMonic substrate consumers (#6771, #6672, #6867, #6868) in view as
   the slow-path capstone target once their dependencies clear.
3. Do not re-attempt the first-fail prefix cut or the unsound `CutRetention`
   target (#7575) — both are settled-false; the proof-facing `CutSeparation`
   certificate is the agreed shape.
4. Clear the two unblocked Phase 6 polish items (#7599, #7601) opportunistically;
   the executable stack stays `sorry`-free and these are the right granularity.
