## Current state

The last closed summarize issue is #4512, which closed at
2026-05-16T16:54:32Z. `gh pr list --state merged --search
'merged:>2026-05-16T16:54:32Z'` reports **18 merged PRs** since then,
above the planner summarize trigger (10+ PRs merged since the last
summarize closed).

Recent landings cluster cleanly into one dominant theme — the HO-1
substrate buildout that unblocks `factor_irreducible_of_nonUnit`
(#4170) — plus a small HexGfqRing Phase 7 tail.

- **HO-1 substrate — outer-bound capstone wrappers** (#4537, #4527,
  #4531, #4533, #4535). The exhaustive-branch irreducibility bridge
  was lifted to the outer bound `B = defaultFactorCoeffBound f`
  (#4537), the per-branch `factorWithBound` output theorem assembled
  (#4533), the Mathlib-bridge exhaustive-core factor irreducibility
  proved (#4531), the bundled `exhaustiveCoreFactorsWithBound`
  coverage theorem assembled (#4527), and the Mathlib-free side
  consolidated as `factorWithBound`-entries-are-`ZPoly.Irreducible`
  (#4535).

- **HO-1 substrate — Hensel-lift state constructors at outer B**
  (#4546, #4550, #4548, #4552, #4554). The
  `HenselSubsetCorrespondenceHypotheses` constructor at the outer
  bound landed parametric in `(core, B)` plus an outer-bound
  specialisation (#4546). The `LiftedFactorSubsetPartition` core
  constructor over `Finset.univ` landed with the same parametric +
  outer-bound shape (#4550). The abstract
  `henselLiftData_liftedFactor_natDegree_pos` theorem + a
  `choosePrimeData` umbrella with the per-modular-factor positivity
  premise still explicit landed (#4548). The
  `hfactors_natDegree_pos` discharge from
  `factorsModPBerlekampForm` + Berlekamp factor-degree positivity
  landed in two halves — `berlekampFactor_factors_pos_degree`
  Mathlib-free in `HexBerlekamp/Factor.lean` and
  `factorsModP_natDegree_pos_of_factorsModPBerlekampForm` on the
  Mathlib-bridge side (#4552). The squarefree-over-ℤ bridge for
  `toPolynomial squareFreeCore` from the executable `SquareFreeRat`
  invariant + primitivity (Gauss-style descent) landed in
  `IntReductionMod.lean` and migrated the
  `LiftedFactorSubsetPartition` outer-bound constructor along the
  import direction (#4554).

- **HO-1 substrate — Nodup family** (#4540, #4534, #4526, #4524,
  #4522, #4545). The Mathlib-free `berlekampFactor.factors.Nodup`
  (#4534) and the Mathlib-bridge `Nodup` wrappers (#4540) decomposed
  the earlier #4528 surface; the
  `henselLiftData_liftedFactor_injective_of_choosePrimeData`
  umbrella for the #4301 capstone landed (#4526). The recursive
  rest-search coverage with matching predicate landed (#4524) and
  the `LiftedFactorListMatches.nodup` helper from per-`J`
  injectivity landed (#4522). The small-mod singleton branch
  substrate discharged `hprim` and `hlc_map_ne` (#4545).

- **HexGfqRing Phase 7**: `HexManual` chapter written and
  `done_through` bumped to 7 (#4532).

- **Doc / decision artefacts**: #4541 resolved #4539 with the
  route-3 abstract-bound refactor recommendation (this is the route
  the subsequent #4537 / #4527 / #4531 / #4533 / #4535 chain
  implemented).

In-flight at survey time: PR #4556 (for #4555) — the parallel
`natDegree`-positivity umbrella that drops the
`hfactors_natDegree_pos` premise by composing the abstract
`_natDegree_pos` umbrella with the `_natDegree_pos_of_factorsModPBerlekampForm`
discharge. Still draft; CI mid-run.

Current queue frontier from `coordination orient` (after this
summarize issue is posted):

- Directives: #2564 (HO-1 rewrite), #2567 (HO-4 BHKS Theorem 5.2),
  #2637 (Factorization record API), #3662 (HO-18 perf report),
  #3899 (HO-43), #3900 (HO-44). All six remain open with `replan`
  labels (except #2567 which is `blocked`) and are intentionally
  outside this planner's scope.
- Unclaimed: #3970 (HexBZ Mathlib Factorization capstones, post-
  current-core-successors), #4334 (HexLLL Phase 4 inconclusive
  verdict investigation, gated on quiet hardware).
- Blocked: #4172 (on #4170), #4170 (on #2567), #4053 (on #3899),
  #3977 (on #4053).
- In-flight PR: #4556 (#4555) — natDegree-positivity umbrella from
  `factorsModPBerlekampForm`.

The HO-1 substrate buildout is approaching the assembly point. The
outer-bound substrate constructors landed in #4546 / #4550 / #4548 /
#4552 / #4554 (plus the small-mod singleton substrate in #4545)
together with the exhaustive-branch wrappers in #4537 / #4527 / #4531
form the input shape consumed by `factor_irreducible_of_nonUnit`
(#4170). The remaining gates on #4170 are: the
`natDegree`-positivity umbrella now in flight as #4556, the
parallel `_injective_of_factorsModPBerlekampForm` umbrella (still
unplanned, noted as "out of scope" in #4555), and the BHKS
fast-branch arm tracked by directive #2567.

## Deliverables

1. Read the 18 PRs merged since #4512 closed and the last 10–15
   files under `progress/`, then write one concise checkpoint
   summary covering what changed and what remains blocked. Keep it
   state-oriented, not a per-PR changelog.
2. Update the appropriate project summary / checkpoint artefact, or
   create the next summary artefact following the existing
   summarize-issue pattern from #4512 and earlier closed summarize
   issues (a single new file under `progress/`).
3. Call out the current queue frontier in the summary:
   - HO-1 substrate: the outer-bound constructors landed (#4546 /
     #4550 / #4548 / #4552 / #4554) plus the small-mod singleton
     substrate (#4545) and the exhaustive-branch wrappers (#4537 /
     #4527 / #4531) form the input shape for #4170. Remaining: the
     `_natDegree_pos_of_factorsModPBerlekampForm` umbrella in flight
     as #4556, the parallel `_injective_of_factorsModPBerlekampForm`
     umbrella (unplanned), and the BHKS fast branch (#2567).
   - HexGfqRing Phase 7 closes with #4532.
   - HexLLL Phase 4 (#4334) remains gated on quiet hardware per
     `SPEC/benchmarking.md`.
   - HO-1 executable irreducibility tail (#4170 → #4172) unchanged.
   - HexGramSchmidt chain (#3977 → #4053 → #3899) unchanged.

## Context

Read:

- Closed summarize issue #4512 and `progress/20260516T223158Z_53447e80.md`
  (or whichever progress file contains the previous checkpoint
  artefact).
- Merged PRs since 2026-05-16T16:54:32Z
  (`gh pr list --state merged --limit 30 --search
  'merged:>2026-05-16T16:54:32Z'`).
- The last 10–15 files under `progress/`.
- `coordination orient`.
- `PLAN.md` and `PLAN/Conventions.md`.
- Open `agent-plan` issue bodies for #3970, #4334, #4172, #4170,
  #4053, #3977, #4555.

Do not edit `SPEC/`, top-level `PLAN.md`, or top-level `AGENTS.md`.

## Verification

- `git diff --check` clean.
- `python3 scripts/check_dag.py` exit 0 if any DAG-relevant files
  are touched (a `progress/` summary entry alone is not
  DAG-relevant).

## Out of scope

- Adding new `agent-plan` issues; this is a summarize task only.
- Re-running `python3 scripts/status.py` for Phase bumps; if a
  Phase bump is warranted, it belongs in a separate feature issue.
- Editing `SPEC/`, top-level `PLAN.md`, or top-level `AGENTS.md`.
- Triaging or commenting on directives (#2564, #2567, #2637, #3662,
  #3899, #3900); those carry `replan` labels (or `blocked`) and
  live in `/replan`.
