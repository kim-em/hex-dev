## Current state

`#4880` (the `hcore_monic` Gap 1 drop from
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData`) is
blocked on substrate sub-issues for five upstream helpers that
currently consume `hcore_monic`. The audit re-confirmed by six sessions
(see `#4880`'s status block) lists them; substrate for helper 1
(`factorsModP_polyProduct_congr_of_factorsModPBerlekampForm`) is filed
as `#4939`, and helper 2 (`henselLiftData_liftedFactor_monic_of_choosePrimeData`)
as `#4940`. This issue files the substrate investigation for
**helper 5**:

* `reassemblyExpansionComplete_exhaustive_of_ne_zero`
  (`HexBerlekampZassenhausMathlib/IntReductionMod.lean:3438`).

Unlike helpers 3 and 4 — which route through helper 2's per-output
monicness fact and therefore defer until helper 2's recommendation is
documented — helper 5's substrate dependency is independent of the
Hensel-lift design choice. Its leaf substrate is

* `Hex.exhaustiveCoreFactorsWithBound_monic`
  (`HexBerlekampZassenhaus/Basic.lean:9156`),
* `Hex.exhaustiveCoreFactorsWithBound_degree_pos`
  (`HexBerlekampZassenhaus/Basic.lean:9204`),

both of which produce conclusions about emitted factors of
`exhaustiveCoreFactorsWithBound` (the unscaled recombination wrapper)
on the assumption that the input `core` is monic. These leaf lemmas
sit in `HexBerlekampZassenhaus/Basic.lean`, not the Hensel-lift
substrate.

The audit observation for helper 5:

> emitted factors of `recombineScaledExhaustive` are not generally
> monic for non-monic core.

(The audit names `recombineScaledExhaustive`, but the actual code
path uses `exhaustiveCoreFactorsWithBound` — the unscaled variant.
The substrate question is the same: monicness of emitted factors
fails when input is non-monic.)

For a primitive non-monic core with positive leading coefficient
`c = leadingCoeff core`, the product chain
(`exhaustiveCoreFactorsWithBound_product`: `polyProduct emitted = core`)
combined with the executable `normalizeFactorSign` / `shouldRecord`
invariants forces emitted factors' leading coefficients to be
positive divisors of `c`. They are not all `1`, so the conclusion
`∀ q, Monic q` is **false** for non-monic primitive core. A thin
sibling that swaps `hcore_monic` for `(hcore_primitive, hcore_lc_pos)`
without changing the conclusion is therefore not feasible at the
existing API surface.

Helper 5 also depends on
`exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData`
(`HexBerlekampZassenhausMathlib/IntReductionMod.lean:3183`), which is
itself an upstream consumer of helpers 1–4 (it threads
`hcore_monic` into `factorsModP_polyProduct_congr_*`,
`henselLiftData_liftedFactor_monic_*`,
`henselLiftData_liftedFactor_natDegree_pos_*`,
`henselLiftData_liftedFactor_injective_*`). That dependency is
handled by helpers 1–4's substrate issues; this issue's scope is
specifically the leaf monic/degree-pos facts plus the umbrella
re-architecture question.

The umbrella's downstream consumer of helper 5 needs:
1. `Hex.shouldRecord` on every emitted factor (used to discharge
   per-factor `Irreducibility` and the reassembly correctness chain).
2. `normalizeFactorSign q = q` on every emitted factor (sign
   normalisation invariant).
3. `0 < q.degree?.getD 0` on every emitted factor (positive
   degree, needed for fuel bounds in the reassembly induction).

Only conclusion (3) depends directly on monicness via the leaf
`exhaustiveCoreFactorsWithBound_degree_pos` (which currently uses
`hq_monic` to argue `degree? = 0 → q = 1`, contradicting `shouldRecord`).
Conclusions (1) and (2) come from
`exhaustiveCoreFactorsWithBound_shouldRecord` /
`_normalizeFactorSign`, neither of which requires `hcore_monic`.

## Deliverables

This is a **design-investigation** sub-issue, not a thin-sibling
relaxation. The deliverables are:

1. **Confirm the audit's "not feasible at the existing API surface"
   claim** for the conclusion `∀ q, Monic q`. Specifically, re-read
   `exhaustiveCoreFactorsWithBound_monic`
   (`HexBerlekampZassenhaus/Basic.lean:9156`) and
   `exhaustiveCoreFactorsWithBound_degree_pos`
   (`HexBerlekampZassenhaus/Basic.lean:9204`) and state explicitly
   in the PR description whether any path exists to a *direct*
   primitive + pos-lc sibling with conclusion `∀ q, Monic q`. (The
   audit predicts no, because `polyProduct emitted = core` and
   `core` is non-monic, but a fresh read can confirm.)

2. **Identify what the umbrella actually needs.** Re-read
   `reassemblyExpansionComplete_exhaustive_of_ne_zero` lines
   3438–3700 and document precisely which downstream lemmas consume
   `hmonic` / `hdegree`. For each consumer, determine whether the
   monicness conclusion can be weakened to a property provable for
   non-monic primitive core (e.g. `leadingCoeff q ∣ c`, or
   `normalizeFactorSign q = q ∧ 0 < leadingCoeff q`).

3. **Survey the three architectural options** for relaxing helper 5
   in the umbrella's context:

   * **Option A (weakened-conclusion sibling).** Define a primitive
     + pos-lc sibling of
     `exhaustiveCoreFactorsWithBound_degree_pos` whose conclusion
     is `0 < q.degree?.getD 0`. The current proof routes through
     `hq_monic` to argue `degree? = 0 → q = 1`, but the actual
     contradiction can be obtained from `shouldRecord` directly:
     a polynomial with `degree? = 0` and `shouldRecord = true` is
     a non-unit constant, and the recombination invariants exclude
     such constants. Determine whether this weakened proof path is
     viable without `hcore_monic`. If so, this is a thin-substrate
     relaxation that closes helper 5.

   * **Option B (umbrella-internal scaling shim).** Have the
     umbrella scale the core to a monic representative before
     invoking the substrate, then translate the conclusion back.
     The recombination side already implements scaling via
     `recombineScaledExhaustive`
     (`HexBerlekampZassenhaus/Basic.lean:5186`); determine whether
     a parallel `scaledReassemblyExpansionComplete_*` (or
     in-umbrella scaling) is feasible without rewriting the
     `reassemblyExpansionComplete` predicate signature.

   * **Option C (file as architectural blocker).** Conclude that
     dropping `hcore_monic` from the umbrella requires a substantial
     architectural change to either the umbrella's recombination
     entry-point (switch from `exhaustiveCoreFactorsWithBound` to
     `recombineScaledExhaustive`) or the
     `reassemblyExpansionComplete` predicate itself, and recommend
     `#4880` proceed with the residual gap documented.

4. **Pick a recommendation and document it** in the PR description.
   No code change is required if the recommendation is Option C; if
   Option A, prototype the weakened-conclusion sibling in this PR;
   if Option B, file a follow-up substrate issue (or, if scope
   permits, prototype the scaling shim in this PR).

5. If the worker concludes after investigation that no productive
   progress is achievable in this issue's scope, **invoke
   `coordination skip --replan` with the audit findings**; the
   replan loop will surface the recommendation to a future planner
   cycle.

No new `sorry`, `axiom`, `native_decide`, `TODO`, or `FIXME`.

## Context

* Umbrella issue: `#4880`.
* Wrapper relaxation prerequisite: `#4879` (landed).
* Helper 1 substrate: `#4939` (filed, not yet landed).
* Helper 2 substrate: `#4940` (filed, not yet landed).
* Helpers 3, 4 substrate: not yet filed; depend on helper 2's
  recommendation.
* Leaf substrate to relax:
  - `Hex.exhaustiveCoreFactorsWithBound_monic`
    (`HexBerlekampZassenhaus/Basic.lean:9156`)
  - `Hex.exhaustiveCoreFactorsWithBound_degree_pos`
    (`HexBerlekampZassenhaus/Basic.lean:9204`)
* Mid-layer consumer of the leaf substrate:
  `exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData`
  (`HexBerlekampZassenhausMathlib/IntReductionMod.lean:3183`) — itself
  uses helpers 1–4 and so is independently blocked on their substrate.
* Scaled-side recombination machinery:
  `HexBerlekampZassenhaus/Basic.lean:5186`
  (`recombineScaledExhaustive`) — already implements the scaling
  trick at the recombination layer for non-monic core.
* Useful supporting lemmas if Option A is pursued:
  - `Hex.exhaustiveCoreFactorsWithBound_shouldRecord`
    (`HexBerlekampZassenhaus/Basic.lean:8728`)
  - `Hex.shouldRecordPolynomialFactor` definition (excludes `0`,
    `1`, `-1` — so a constant emitted factor must have absolute
    value ≥ 2, which contradicts `degree?.getD 0 = 0` only for
    non-monic primitive core if we additionally know the constant
    has degree `0` in the polynomial-degree sense).

## Library placement

* **SPEC §:** `SPEC/Libraries/hex-berlekamp-zassenhaus.md` —
  Mathlib-bridge HO-1 substrate.
* **Mathlib use:** mixed.
  - Leaf substrate relaxation: `HexBerlekampZassenhaus/Basic.lean`
    (Mathlib-free executable layer).
  - Umbrella adjustment, if applicable:
    `HexBerlekampZassenhausMathlib/IntReductionMod.lean` (Mathlib
    bridge).

## Verification

For an investigation-only PR (Option C) or a small prototype PR:

* `lake build HexBerlekampZassenhaus.Basic`
* `lake build HexBerlekampZassenhausMathlib.IntReductionMod`
* `lake build HexBerlekampZassenhausMathlib`
* `python3 scripts/check_dag.py`
* `git diff --check`
* `rg -n "sorry|axiom|native_decide|TODO|FIXME"
   HexBerlekampZassenhaus/Basic.lean
   HexBerlekampZassenhausMathlib/IntReductionMod.lean`
  shows no new entries on the diff against `origin/main`.

For a worker that invokes `coordination skip --replan`: the audit
findings are the deliverable; no build verification required beyond
the explanation comment posted to the issue.

## Out of scope

* Filing helper-3 and helper-4 substrate sub-issues (defer to a
  future planner cycle once helper 2's recommendation is documented).
* Implementing the umbrella drop in `#4880` itself.
* Relaxing the helpers 1–4 dependencies of
  `exhaustiveCoreFactorsWithBound_expansion_preconditions_of_choosePrimeData`
  — those are tracked by `#4939`, `#4940`, and the pending helper
  3/4 issues.
* Editing `SPEC/`, top-level `PLAN.md`, or `AGENTS.md`.
* BHKS Theorem 5.2 / directive `#2567`.
