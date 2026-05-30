# Draft issue: rollback BZ Phase-4 bench scaffolding pending new SPEC clauses

**Purpose of this draft.** Captures the rollback work that the SPEC
update PR ([reports/bz-spec-comparator-pr-draft.md](bz-spec-comparator-pr-draft.md))
dispatches. The Phase-4 bench scaffolding shipped under HO-3
([#2566](https://github.com/kim-em/hex/issues/2566)) does not satisfy
the new SPEC clauses (no comparator, no headline correctness theorem,
unaudited fallbacks), so the scaffolding must be re-executed against
the new rules before any future Phase-4 work on BZ proceeds.

Four related but separable worker issues follow this one (HO-5a/b/c/d).
They are filed once the SPEC PR merges; this issue is the orchestrator's
coordination point.

---

## Title

```
HO-5: rollback BZ Phase-4 bench scaffolding, re-run against verified Isabelle BZ comparator
```

## Labels

`directive`

(The SPEC PR's `blocked` state resolves on merge. By the time this
issue is filed the dependency is satisfied; it is *open and
dispatchable*, not blocked.)

## Body

### Current state

After merging the SPEC update PR
([drafted at reports/bz-spec-comparator-pr-draft.md](../reports/bz-spec-comparator-pr-draft.md)),
the existing BZ Phase-4 bench scaffolding shipped under HO-3
([#2566](https://github.com/kim-em/hex/issues/2566)) no longer
satisfies the SPEC. Specifically:

1. `phase4.comparators` is empty for `HexBerlekampZassenhaus` in
   [libraries.yml](../blob/main/libraries.yml). The new SPEC clause
   `## External comparators` requires a `verified Isabelle BZ` entry
   classified `gating` with goal `hex/isabelle ≤ 1×`.
2. [reports/hex-berlekamp-zassenhaus-performance.md](../blob/main/reports/hex-berlekamp-zassenhaus-performance.md)
   records Phase-4 verdicts against an internal complexity model only,
   with no external-comparator ratio. Without the ratio there is no
   way to distinguish "schedule too short" from "algorithm doing wrong
   work", which is exactly the failure mode that masked the
   `isGoodPrime` cascade documented in
   [reports/bz-vs-isabelle-investigation.md](../blob/main/reports/bz-vs-isabelle-investigation.md).
3. [HexBerlekampZassenhausMathlib/](../blob/main/HexBerlekampZassenhausMathlib/)
   does not state the headline correctness theorem mandated by the new
   SPEC clause `## Headline correctness theorem`. The clause blocks
   `done_through ≥ 4` until the theorem is proved.
4. `fallbackPrimeChoiceData` at
   [HexBerlekampZassenhaus/Basic.lean#L1966](../blob/main/HexBerlekampZassenhaus/Basic.lean#L1966)
   is a total form of a partial helper in the sense of the new
   `SPEC/design-principles.md §"Fallback discipline for total forms of
   partial helpers"` clause. It has neither an
   `unreachable-by-pipeline-invariant` theorem nor an
   `audited-emergency-value` rationale; per the new clause it is a
   SPEC violation and must be either proved unreachable or removed.

### Deliverables

This is a coordination issue. Four child issues do the actual work
and are dispatched alongside this issue:

1. **HO-5a — wire `verified Isabelle BZ` Phase-4 comparator.**
   Add `scripts/oracle/setup_bz_isabelle.sh` mirroring the existing
   [scripts/oracle/setup_lll_isabelle.sh](../blob/main/scripts/oracle/setup_lll_isabelle.sh)
   as the starting template. The worker must satisfy the following
   **acceptance matrix** before the issue closes — without it, the
   comparator's numbers may be incomparable to hex's and the gate
   becomes meaningless:

   1. `isabelle build -b Berlekamp_Zassenhaus` against the pinned AFP
      release completes with the session heap cached on the CI runner.
   2. A wrapper theory under `scripts/oracle/` exports
      `factor_int_poly` (or chosen equivalent) to Haskell via
      `export_code …`; `ghc -O2` produces a runnable binary.
   3. The persistent-subprocess driver accepts polynomials in a
      canonical wire format (e.g. JSON `{"coeffs":[…]}`, leading-
      coefficient convention fixed in the SPEC text) and emits
      factor lists in a matching format.
   4. **Correctness gate before timing.** On a small fixture set whose
      true factorisation is hand-verifiable (e.g. `(x-1)(x-2)`, `Φ₅`,
      `(x²-2)(x²-3)`), hex's `Factorization.factors` and Isabelle's
      output produce the **same factor multiset** under a stated
      canonical ordering (e.g. sort by leading coefficient then lex on
      coefficient vector; monic representatives; positive
      multiplicities). Multiset equality, not list equality.
   5. Per-call process startup overhead is measured separately and
      reported as the "subtracted baseline" of the ratio computation.
      Subprocess startup dominates small-`n` measurements otherwise
      (as observed for the AFP LLL `svp_verified` binary during the
      investigation).
   6. The driver respects persistent-subprocess semantics per
      [SPEC/benchmarking.md §"External comparators — Process call"](../blob/main/SPEC/benchmarking.md):
      the process stays alive across inputs in a measurement window,
      so warm-up does not bleed into the first measurement of each new
      sample.

2. **HO-5b — rewrite [reports/hex-berlekamp-zassenhaus-performance.md](../blob/main/reports/hex-berlekamp-zassenhaus-performance.md)
   against the new comparator.** Re-run every existing scientific
   bench target with the comparator wired. Record `hex/isabelle`
   ratios. Replace internal-model verdicts with ratio-based verdicts
   per the new SPEC clause. Existing inconclusive internal-model
   verdicts become informational appendix entries; the headline
   report runs on the comparator ratios with the 1× gate.

   Label: `feature, directive`. `depends-on: HO-5a`.

3. **HO-5c — extend the bench schedules.** Per the post-mortem
   §"Gap 3", the existing `splitScientificSchedule = #[2, 3, 4, 5]`
   cannot exercise the bug class that the new comparator's existence
   is meant to detect. Extend the schedule to at least `n ∈ [11, 24]`
   on the deterministic split family, and add a `fallback-probe`
   family that constructs inputs known to exercise the prime-search
   cascade. This is *bench-only* — failing-conformance fixtures are
   a separate, bundled-with-fix issue (see the tactical `isGoodPrime`
   fix issue, filed independently).

   Label: `feature, directive`. `depends-on: HO-5a`.

4. **HO-5d — remove `fallbackPrimeChoiceData`.** The new SPEC clause
   `SPEC/design-principles.md §"Fallback discipline for total forms of
   partial helpers"` admits exactly two classifications, and
   `refactor-pending` is not one of them. The fallback must be either
   proved unreachable or removed. Two acceptable resolutions, worker
   chooses:

   - (a) **Prove unreachability.** Add
     `choosePrimeData?_isSome_of_<sf-primitive-input>` to
     `HexBerlekampZassenhausMathlib`, citing the precondition that
     the public `factor` pipeline already establishes via
     `normalizeForFactor`. Reshape `choosePrimeData` to consume the
     theorem at the match site so the `none` branch becomes literally
     dead code. Add the SPEC text citing the theorem and the
     pipeline invariant per Change 4 of the SPEC PR.
   - (b) **Propagate `Option` upward.** Change `choosePrimeData`'s
     return type to `Option PrimeChoiceData` and update every
     production caller (`factorFastFactorsWithBound`,
     `factorSlowWithBound`, …) so the public `factor` itself
     short-circuits on `none`. This option surfaces the question
     "what should `factor` do when no candidate prime works?" rather
     than masking it. The natural long-term answer is to extend the
     prime search à la Isabelle's `find_prime`; the
     prime-search-extension issue is filed as part of HO-5d's
     deliverables regardless of which resolution this issue picks.

   Label: `bug, directive`. `depends-on: HO-5a` (so the comparator
   informs whether the removal regresses performance).

HO-5a is the upstream bottleneck; HO-5b/c/d block on it.

### Out of scope

- The `isGoodPrime` correctness fix itself. It is dispatched as a
  separate tactical issue (bundled with the failing conformance
  fixtures that exercise it, since CI cannot accept failing fixtures
  without the fix landing in the same PR).
- HO-1 ([#2564](https://github.com/kim-em/hex/issues/2564))'s
  architectural rewrite to BHKS van Hoeij CLD. HO-1 is reframed in
  place to name the headline correctness theorem as its deliverable;
  this rollback does not duplicate that work.
- Wider orchestrator changes for other libraries' total-of-`Option`
  helpers. The new `SPEC/design-principles.md` clause applies
  prospectively across the project, but per-library audits land as
  separate issues per library.

### Verification

This issue closes when HO-5a, HO-5b, HO-5c, HO-5d are all closed
*and* `reports/hex-berlekamp-zassenhaus-performance.md` runs verdicts
on `hex/isabelle` ratios per the new SPEC clause. The Phase-3 work
(conformance fixtures, cross-check oracle, JSONL corpus) stays;
only the Phase-4 bench scaffolding is rolled forward against the
new comparator and ratio verdicts.

`status.py HexBerlekampZassenhaus` should report HO-5 as the
critical-path Phase-4 blocker until then. HO-1 (#2564) remains the
critical-path Phase-1 blocker independently.

### Context

- Post-mortem driving this rollback:
  [reports/bz-vs-isabelle-investigation.md](../blob/main/reports/bz-vs-isabelle-investigation.md)
- SPEC PR that dispatches this issue (merged):
  [reports/bz-spec-comparator-pr-draft.md](../blob/main/reports/bz-spec-comparator-pr-draft.md)
- Related (the architectural directive, now reframed): #2564
- Related (the closed Phase-4 bench scaffolding being rolled forward): #2566

🤖 Prepared with Claude Code
