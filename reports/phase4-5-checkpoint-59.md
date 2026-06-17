# Phase 4/5/6 checkpoint 59

Scope: checkpoint for the 28 PRs merged after summarize issue #7596 (closed
2026-06-16T15:09:52Z) through PR #7672 (2026-06-17T04:05:55Z). One thread
dominates this window: the fast-path BHKS van Hoeij CLD recombination chain
(true-factor CLD vectors, the Gram-Schmidt prefix cut, the CLD norm certificate,
and the projection of the prefix survivor span into `CutProjectionHypotheses`).
A secondary slow-path thread re-keyed the exhaustive lift onto
`exhaustiveLiftBound` and proved slow modular raw irreducibility. Phase 6
executable-API polish continues as a steady background stream. The frontier
remains directive #2564 (HO-1) and its two headline `sorry`s; nothing in this
window retired either of them.

## Landed work

28 PRs merged after checkpoint 58. Grouped by topic.

### Fast-path BHKS CLD cut / recovery chain (dominant theme)

The proof-facing van Hoeij CLD route that replaced the retired false first-fail
prefix cut (the #7590 decision recorded in checkpoint 58). This window built the
true-factor vector surface, made the cut a genuine prefix, proved the norm
certificate, and projected the survivor span into the recovery hypotheses:

- #7602 expose the BHKS projected-row trace and the LLL span bridge.
- #7613 add the true-factor CLD lattice vector surface (`TrueFactorCLDVectorData`);
  #7629 review verdict for it.
- #7617 make the BHKS Gram-Schmidt cut a genuine prefix cut.
- #7632 prove the canonical `TrueFactorCLDVectorData` coordinate identities and
  the cut-radius reduction; #7633 expose the prefix row-combination support
  lemmas.
- #7634 reduce the CLD tail bound to per-column bounds; #7642 review verdict;
  #7643 prove the tight true-factor CLD norm certificate; #7659 audit the full
  CLD norm-bound chain.
- #7639 prove the BHKS prefix survivor-span lemma (#7620 deliverable 1); #7658
  project that survivor span into `CutProjectionHypotheses`.
- #7652 add the true-factor lift interface for the CLD bounds; #7670 review
  verdict; #7661 bridge the true-factor CLD rows.
- #7662 specialize the fast-core forward irreducibility statement; #7666
  decouple the scheduled fast-core loop start from the recovery precision; #7672
  add fast-core loop recovery determinism.

### Slow-path exhaustive lift-bound chain

- #7630 add the slow exhaustive lift-bound bridge lemmas; #7657 switch the slow
  exhaustive lift to `exhaustiveLiftBound`; #7669 audit that switch; #7665 prove
  slow modular raw irreducibility.

### FactorSoundness packaging

- #7612 expose the FactorSoundness positive-leading factor contract; #7618
  expose the default-factor uniqueness side-condition package.

### Phase 6 executable-API polish

- #7605 expose the FpPoly evaluation simp surface (`eval_zero`/`eval_one`/
  `eval_neg` and the `@[simp]` family); #7624 expose the DensePoly eval additive
  homomorphism simp surface (`eval_add`/`eval_sub`/`eval_neg`).

### Reviews and docs

- #7606 confirm the toMonic Hensel substrate producers sound; #7609 note the
  executable-layer scratch `#eval` extern gotcha in the Mathlib-boundary skill.
  (The CLD-chain review verdicts #7629/#7642/#7659/#7669/#7670 are listed with
  their proof topics above.)

## Phase state

`scripts/status.py` reports the executable dispatch front in Phase 6
proof-polishing: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt,
HexGF2, HexPolyZ, HexLLL, HexPolyFp, HexGFqField, HexHensel, HexConway, HexGFq,
and HexPolyMathlib are all Phase-6 ready. `HexBerlekamp` is at Phase 4.
`HexBerlekampZassenhaus` remains at Phase 1 (library scaffolding) — unchanged,
consistent with directive #2564's `done_through: 2 → 0` rollback still standing.

Mathlib-side queues stay split by dependency, unchanged from checkpoint 58:

- Phase 5 ready: HexMatrixMathlib, HexModArithMathlib.
- Phase 4 ready: HexGramSchmidtMathlib, HexPolyZMathlib, HexHenselMathlib,
  HexGF2Mathlib.
- Blocked: HexLLLMathlib (waits on HexGramSchmidtMathlib ≥ 4),
  HexBerlekampMathlib (waits on HexBerlekamp ≥ 4), HexGFqMathlib (waits on
  HexGF2Mathlib ≥ 4), and HexBerlekampZassenhausMathlib (Phase 3, waits on
  `HexBerlekampZassenhaus.done_through ≥ 3`).

HexGFqRing is fully done. HexRoots/HexResultant/HexNumberField and their Mathlib
counterparts remain SPEC-ready but implementation-deferred.

## Quality metrics

Repository-wide Lean grep (excluding `.lake/`), unchanged from checkpoints 57
and 58:

- `sorry`: 68 (`rg -n '\bsorry\b' --glob '*.lean'`), all confined to the
  non-CI-built Mathlib-side layers: HexBerlekampMathlib 19 (Basic.lean),
  HexGF2Mathlib 23 (Field.lean 12, Basic.lean 11), HexGFqMathlib 15 (GF2q.lean 8,
  Basic.lean 7), HexHenselMathlib 6 (Correctness.lean),
  HexBerlekampZassenhausMathlib 4 (Basic.lean 2, IntReductionMod.lean 1,
  FactorSoundness.lean 1), HexMatrixMathlib 1 (Determinant.lean). No `sorry`
  exists in any CI-built executable library. Note: within the BZMathlib layer
  the raw count includes comment text (`IntReductionMod.lean:1275` and one of
  the two Basic.lean hits are prose, not tactic markers); the two genuine
  headline `sorry`s are named below.
- `axiom`: 0 real declarations. The 11 `\baxiom\b` grep hits are all comment /
  docstring text — `Lean.Grind.Semiring` / `Field` axiom-*field* references in
  HexGFqRing/Operations.lean and HexPolyFp/Quotient.lean, plus one
  forbidden-token checklist line. No line begins with `axiom`.
- `native_decide`: 0 real tactic uses. The 2 grep hits are both comment text
  (a checklist line in `HexBerlekampZassenhausMathlib/IntReductionMod.lean` and
  a line in `HexArith/Nat/Prime.lean` stating the code does *not* depend on
  `native_decide`).
- `TODO`/`FIXME`: 1 comment match (the same `IntReductionMod.lean:1275`
  forbidden-token checklist line), not an open proof marker.

The headline gap between goals and current state is unchanged: every remaining
`sorry` sits in the Mathlib boundary layers, which CI does not build, so a
whole-library `lake build` of those targets surfaces them. The executable
Mathlib-free stack carries no proof debt. The 28 PRs in this window moved
substrate and API surface for the fast-path CLD chain without retiring either
headline `sorry` — they are support work for the directive #2564 capstone, not
the capstone itself.

## Blocking structure for directive #2564

The two headline `sorry`s remain the directive #2564 capstone:

- `factor_irreducible_of_nonUnit` in
  `HexBerlekampZassenhausMathlib/FactorSoundness.lean:20`.
- `Hex.ZPoly.isIrreducible_iff` in
  `HexBerlekampZassenhausMathlib/Basic.lean:234` (pending the C1 obligation that
  `factor f` is the irreducible factorisation).

Two support fronts feed them, neither yet at the capstone:

1. **Fast path** — the cut-separation route advanced substantially this window
   (true-factor CLD vectors, prefix cut, norm certificate, survivor-span
   projection into `CutProjectionHypotheses`). The composition step #7675
   (compose the true-factor cut stack into fast BHKS irreducibility) is the
   live critical-path issue, currently `blocked` on #7651 (tight psiCut
   aggregation bound) and #7674 (semantic lift facts for TrueFactorLift CLD
   aggregation), both in `replan`. #7620's deliverable-1 survivor span and the
   #6771 forward-count assembly attempt are both now closed/replanned.
2. **Slow path** — the exhaustive lift is re-keyed onto `exhaustiveLiftBound`
   (#7657) with slow modular raw irreducibility proved (#7665). Its capstone
   consumer remains #6672 (assemble `factor_irreducible_of_nonUnit` from branch
   proofs), `blocked` on #7675, along with the FactorSoundness packaging
   #6867/#6868.

## Current frontier

Open PRs at checkpoint time:

- #7679 review: audit BHKS cut projection producer.
- #7678 feat: package true-factor CLD semantics.
- #7676 doc: guard replan triage against concurrent-disposition races.
- #2656 draft SPEC PR for real roots and Sturm.

Issue #7656 (review: audit CutProjectionHypotheses projection producer) carries
an open PR.

Unclaimed (excluding this summarize issue): directive #2564 (the umbrella,
`blocked`, not a single-session unit). All other open feature issues are
`blocked` behind the #7651/#7674 → #7675 → #6672 chain, plus the FactorSoundness
cluster #6867/#6868, the B-builder #6779, and the residual checker theorems
#4818/#4172/#6246.

## Recommended next actions

1. Re-scope the two `replan` blockers #7651 (tight psiCut aggregation bound) and
   #7674 (semantic lift facts for TrueFactorLift CLD aggregation) — they gate
   the entire fast-path composition #7675.
2. Once #7675 lands, #6672 (`factor_irreducible_of_nonUnit` assembly) becomes
   the slow-path capstone target; keep #6867/#6868 in view as its FactorSoundness
   packaging.
3. Do not re-attempt the retired first-fail prefix cut or the unsound
   `CutRetention` target (#7575) — both are settled-false; the proof-facing
   `CutProjectionHypotheses` survivor-span route is the agreed shape.
4. Continue clearing Phase 6 executable-API polish opportunistically; the
   executable stack stays `sorry`-free and these are the right granularity.
