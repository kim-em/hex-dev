# Plan: fast sorry-free executable + proof the fast path always runs

Two tracks Kim asked to plan: (1) what remains to a **fast, sorry-free
executable**; (2) what remains to the **proof that it is always the fast path
that runs** (dead-slow D1+D2). The correctness capstone (`factor_irreducible_of_nonUnit`,
#8068) is a third, separate thing already in flight and is NOT in scope here
except as context.

## Ground truth (audited this session)

- **Executable (`HexBerlekampZassenhaus` and all Mathlib-free libs): sorry-free.**
  Whole-tree grep finds exactly two real `sorry`s, both in the +Mathlib bridge:
  `HexBerlekampZassenhausMathlib/Basic.lean:235` (`isIrreducible_iff`, a C1
  decidable-instance obligation) and `FactorSoundness.lean:20`
  (`factor_irreducible_of_nonUnit`, the HO-1 capstone, #8068).
- Executable correctness: 29/29 on a wide battery after #8066 (first-suitable
  prime selection + plain-remainder gcd), per #8062.
- D1/D2 are leaves: SPEC §"Group D" line 587 — "no other proof obligation,
  public-API contract, Decidable instance, or theorem statement in the bridge
  depends on D1 or D2."

## TRACK 1 — fast, sorry-free executable

"Sorry-free" is already true. "Fast" + "benchmarked" remain. The owning issue is
**#8062** (on branch `fix/factorfast-bpoly-precision-guard`); its items 1-3 and 5
are done (precision fix, all-ones guard removal, first-suitable; the three B=1
sorries are gone from the tree). Remaining is item 4 (F_p perf) + item 6 (bench).

The single dominant cost: `choosePrimeData?` is ~90% of `factorFast` wall time
(split-12 163ms, split-16 646ms, split-20 2084ms), because the single Berlekamp
factorization of `f mod p` is ~10^5x too slow for ZMod64 work (deg-12 over F_13
≈ 160ms). Two independent fronts:

1. **F_p arithmetic substrate (packed UInt64).** Make ZMod64 ops native-speed.
   - #8251 packed monic-division kernel — **LANDED (closed)**.
   - #8248 packed divMod/gcd kernel behind `@[csimp]` — needs replan (its body
     carried a superseded raw-word premise; it was blocked on #8251, now closed),
     then dispatch.
   - #8249 packed multiply + route HexGFq/HexBerlekamp F_p hot paths — blocked
     on #8248.
2. **Berlekamp-mod-p algorithm (#8062 item 4).** Even with native arithmetic,
   deg-12/F_13 at 160ms implies algorithmic waste. Localise (isGoodPrime gcd vs
   the Berlekamp nullspace/matrix; ZMod64 vs big-int paths), ground against a
   reference (FLINT/NTL/Isabelle F_p factorisation), fix, re-bench. May expose
   more van Hoeij-core scaling.
3. **van Hoeij core high-degree scaling (#8064).** split-24 recombination = 30s;
   the floor-skip/hoist landed (#8076); the deeper steep-scaling tail is open.
4. **Benchmark (#8062 item 6).** Re-bench to the SPEC goal `hex/isabelle <= 1x`
   across the scaling ladder. Needs the verified-Isabelle BZ comparator wired
   (HO-5a family) as a prerequisite for the ratio ladder.

Suggested order: replan+dispatch #8248 -> #8249 (substrate); in parallel profile
#8062-item4 to see whether packed arithmetic alone closes the F_p gap or the
Berlekamp algorithm itself needs work; then #8064 tail; then the comparator +
benchmark.

## TRACK 2 — proof the fast path always runs (dead-slow D1 + D2)

Both are leaf theorems in the +Mathlib bridge. They split sharply by difficulty.

### D2 — easy, unblocked. `choosePrimeData?_none_implies_huge`

SPEC line 604-624. Shape: `choosePrimeData? f = none -> |lc(f)*disc(f)| >= ∏ HotPathCandidates`
(≈ 10^203). Proof is a clean divisibility argument with no new mathematical
content: (1) `isGoodPrime f p = false -> p ∣ lc(f)*disc(f)`; (2) `none` means every
HotPathCandidate failed, so every such prime divides `lc*disc`; (3) distinct
primes -> product divides -> magnitude bound. One bridge theorem + a small
`isGoodPrime`-unfolding helper.

Executable precondition (already satisfied, must be preserved): the `none` path
must test all 95 primes in [3,500] before concluding `none`. First-suitable
short-circuits on *success* only; it must NOT short-circuit the `none` walk.

Action: file as a fresh bridge issue, dispatch now (unblocked, self-contained).

### D1 — hard, gated on #2564. `factorFast_terminates_of_choosePrimeData`

SPEC line 589-600. Shape: `choosePrimeData? f != none -> factorFast f != none`
at cap = `bhksBound f`. The unconditional form is false by design (the three-tier
combinator is the safety net, not factorFast). Internal structure: resultant
Hadamard bound + BHKS Lemma 3.2 + BHKS Theorem 5.2 at `bhksBound` +
BHKS-bound-dominates-Mignotte, assembled into the final theorem.

The hard core is BHKS Theorem 5.2 **separation** (the reverse `L' = W`
inclusion). Its B-builder is **#6779**, which is **blocked on #2564**:

- The "resultant on the cut auxiliary" framing #6779 originally tried is
  **mathematically false as typed** (sympy-verified counterexamples: `x^2+1,
  p=5, k=3`; `x^4+1`; the `v_p(Res(input, aux_cut)) = 0` finding). The `k*d`
  exponent lives on the un-cut `N = cldQuotientMod`, not the cut aux. An entire
  A-line lineage (#6949 -> ... -> #7232) closed by supersession without landing.
- Settled disposition: the only viable route is the **van Hoeij CLD lattice
  rollback = #2564**, which restructures the recombination lattice so the false
  cut-aux object is retired by construction rather than proved. After #2564
  lands, re-derive the BadVectorBridge finisher (#6779) against the restructured
  lattice, then assemble D1.
- Rational-coprimality half of Lemma 3.2 already landed
  (`coprime_input_aux_over_rat_of_forward`, merged #6865); the L'-minus-W lift is
  already wired (`bad_setup_of_projected_not_indicator`,
  `capSeparationOfBridgeData`). The single missing analytic clause is the
  modular resultant divisibility, which #2564 makes provable.

So D1's critical path is **#2564 -> #6779 -> D1-assembly**. #2564 is the long
pole and the next thing to drive on this track; per its own progress note its
analytic inputs (Landau, Hadamard, UFD, Hensel, Mignotte) are all available in
Mathlib ("Missing infrastructure: none for HO-1's obligations").

Note: #2564's restructure is about the **proof-side** lattice object used in the
separation argument; the executable already runs van Hoeij CLD. Worth confirming
#2564's scope is the bridge formalisation alignment, not an executable rewrite,
before dispatching.

## What to dispatch now (in order)

1. **D2 issue** — file `choosePrimeData?_none_implies_huge` + executable
   none-walk precondition; `pod once` (unblocked, quick win).
2. **#8248 replan + dispatch**, then **#8249** (perf substrate; #8251 landed).
3. **#2564** — the D1 critical-path directive (also unblocks #6779). Confirm
   scope, then drive.
4. (already running) **#8068** correctness capstone — separate track, in flight.

## Second-opinion corrections (Codex + source re-audit)

The Codex review and a follow-up source audit correct several claims above. The
two-track split holds; the Track-2 detail was stale and pessimistic.

- **D2 is already landed — do NOT file it.** `choosePrimeData?_none_implies_huge`
  is proved sorry-free at `HexBerlekampZassenhausMathlib/HotPathDiscriminant.lean:244`
  (#6509, closed): `choosePrimeData? f = none -> p ∣ lc(f)·Res(f, f')` for every
  prime `p ∈ [3,500]`, which with the hot-path enumeration gives the product
  bound. Track 2's D2 is essentially complete.
- **D1's assembly is already built and sorry-free.**
  `factorFast_terminates_of_choosePrimeData` (`Recovery.lean:7977`) proves the
  SPEC D1 (`choosePrimeData? (normalizeForFactor f).squareFreeCore ≠ none ->
  factorFast f ≠ none`) from four provider packages: `rows_pos`, `trueSupports`,
  `capInputs : FactorFastCapSeparationInputs`, `recoveryInputs :
  CanonicalRecoveryTailInputs`. The whole `factorFast_ne_none_of_*` cascade
  (`Recovery.lean:2431-7600+`) and the `FactorFastCapSeparationInputs.ofBridgeData*`
  reduction constructors (`Recovery.lean:8033+`) are present. So D1 is NOT a
  "full rollback with nothing built"; it is "produce four packages atop a
  complete assembly."
- **D1's single deep open piece is `BadVectorBridgeData` (#6779).** The
  `ofBridgeData*` constructors reduce `FactorFastCapSeparationInputs` to
  `BadVectorBridgeData` + analytic pointwise bounds + the BHKS paper threshold
  (eq 5.3). Its forward `cut` field is the same `CutProjectionHypotheses` the
  correctness capstone (#8068) produces via `cutProjectionHypotheses_of_trueFactors`
  — shared work. The reverse-separation `BadVectorBridgeData` is the gated piece
  (#6779, which says the cut-aux resultant clause is false-as-typed and routes
  through #2564).
- **#2564 scope is genuinely ambiguous and must be resolved before dispatch.**
  Its title is "rollback and rewrite to van Hoeij CLD," but the executable AND
  the forward-cut bridge already implement van Hoeij CLD (29/29 correct, forward
  cut + CLD certificates built). #2564 may be largely done, with only the D1
  reverse-separation `BadVectorBridgeData` producer remaining against the
  already-restructured lattice. Re-scope #2564 to its actual remaining delta
  before driving it as the headline rollback.
- D1 must be stated on `(normalizeForFactor f).squareFreeCore` and threads
  `factorFastPrecisionCap f` + the `cldCoeffFloor ≤ cap` floor — already done in
  the code (`Recovery.lean:7977-8027`), not missing.
- Minor: the hot-path list is **94** primes (`[3,500]` excludes 2), not 95
  (`HexBerlekampZassenhaus/Basic.lean:601`).
- "Executable done" = conformance/sorry-free, NOT correctness-done (the capstone
  sorry remains, separately). Packed F_p kernels are **correctness-sensitive**:
  install only by proved / `@[csimp]`-equivalent replacement, CI-gated.

### Corrected dispatch

1. **#8248** replan + dispatch (Track-1 perf substrate; #8251 landed). Then #8249.
2. **#2564 re-scope audit** (`replan`): pin its actual remaining delta against the
   already-built forward-CLD lattice + the complete D1 assembly, so the headline
   directive is not driven on a stale "rewrite everything" premise. This is the
   Track-2 long-pole's correct next step — not blind implementation.
3. D2: nothing to do (landed).

## Risks / open questions

- Does packed arithmetic alone close the F_p gap, or is the Berlekamp-mod-p
  algorithm itself the bottleneck? Profile before committing #8249's routing.
- #2564 scope ambiguity (proof-side vs executable). Confirm before dispatch.
- The benchmark `<= 1x` goal needs the Isabelle comparator wired first (HO-5a).
- D1 is the genuine multi-step long pole; everything else is comparatively small.
