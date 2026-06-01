# Phase 4/5/6 checkpoint 49

Scope: checkpoint for merged work after summarize issue #5745 closed at
2026-05-21T07:56:21Z, through the claim-time queue snapshot for #5885. The
live merge query at claim time contains 63 PRs.

## Landed work

### HO-5d and Berlekamp-Zassenhaus fallback cleanup

The largest landed stream moved the BZ codebase away from silent total
prime-choice fallbacks and toward explicit `Option` witnesses.

- #5779 fixed good-prime acceptance for unit gcds.
- #5830 added `factor?` and `factorWithBound?` as Option-propagating BZ
  boundary APIs.
- #5840 partially closed #5831 by adding Option-side slow-path raw-factor
  variants and migrating executable guards.
- #5846 extended BZ prime search beyond the fixed `smallPrimeCandidates` list.
- #5850 migrated remaining BZ production callers off total `choosePrimeData`.
- #5861, #5862, #5863, #5864, #5870, #5871, #5872, and #5882 migrated
  proof-facing theorems, bridge wrappers, singleton-prime witnesses,
  conformance guards, and stale comments off total `choosePrimeData`.
- #5880 added cheap in-Lean regression guards for the deterministic split
  prime-selection failures called out by the BZ/Isabelle investigation.

The remaining cleanup is now narrower. #5868 has an open PR for
`HBZMathlib/IntReductionMod.lean`, and #5869 is blocked behind it as the
architectural closer that removes `choosePrimeDataWithFallback`,
`fallbackPrimeChoiceData`, and the total `choosePrimeData` surface from
`HBZ/Basic.lean`.

This stream does not discharge directive #2564. The headline correctness
theorem, CLD fast-path rewrite, and remaining Mathlib bridge obligations are
still the critical BZ directive frontier.

### BZ benchmarking and Isabelle comparator evidence

BZ Phase 4 evidence broadened substantially.

- #5802 added the scheduled BZ Isabelle comparator.
- #5821 extended BZ bench schedules to exercise the prime-search cascade.
- #5822 recorded BZ Isabelle comparator ratios.
- #5826 added a per-rung Isabelle ratio ladder on the split scientific
  schedule.
- #5832, #5833, #5837, #5844, and #5845 extended the ratio surface across
  fast/slow targets, degree/height ladders, HO-2 singleton cases, the fallback
  probe, and the precision-local Isabelle matrix.

These reports and schedules are evidence for current BZ performance state, not
a replacement for the SPEC obligations. Follow-up should continue through the
existing HO/BZ issue chain rather than creating a duplicate BZ umbrella.

### HexLLL Phase 4 benchmarking

HexLLL's benchmark blocker shifted from measurement infrastructure toward a
fresh verdict run.

- #5879 lowered HexLLL parametric scientific registrations'
  `signalFloorMultiplier` to `1.0` and documented the allowed spawn-floor
  exception. This addresses the prior pattern where the shared host's inflated
  spawn floor made rows verdict-ineligible.
- #5876 required comparator-runtime plots for libraries with two or more
  comparators.
- #5881 added the HexLLL comparator-runtime plot and linked it from the public
  HexLLL performance report.

#4334 is claimed and should now retry the affected HexLLL scientific sweep on
current main. If verdicts remain inconclusive, the next diagnosis should be
about the model, schedule, cap, implementation, or remaining host noise rather
than the old 10x spawn-floor filter.

### HexMatrix and HexGramSchmidt Phase 5 substrate

Matrix and Gram work advanced the singular-pivot and Plucker-minor substrate.

- #5761 added an `exactDiv` row-combination helper.
- #5820 refactored `BareissGramRowInvariant` to bundle explicit coefficients.
- #5828 proved the Gram zero-pivot column suffix from the closed row invariant.
- #5834 added a Mathlib-free Gram singular Bareiss helper.
- #5852 added the first Plucker minor substrate: definitions, `colReplace`
  foundations, and basis-vector evaluation.

The current active Plucker successor is #5851, marked `replan`, with #5848
blocked behind it for the universal identity instantiation used by the
Gram-trajectory cofactor proof. The older Gram singular chain is no longer at
#5677; the remaining visible Gram blocker is #5805 behind #5848, with #5655
behind #5805.

### Schmeisser / de Bruijn-Springer source chain

The Schmeisser route gained one concrete source theorem and one downstream
wrapper, but the all-positive-degree source theorem remains absent.

- #5760 proved the degree-one open Schmeisser control theorem.
- #5825 derived closed-radius root-count control from the de
  Bruijn-Springer surface.

#5765 was marked `replan` during this checkpoint because its body already
records two bounded-worker skips and states that the next step belongs to
planner-level decomposition: either port/formalize a Grace apolarity theorem
strong enough for the all-degree source result, or deliberately narrow to a
per-degree result such as `n = 2`. Downstream issues #5735, #5702, #5570,
#5559, #5525, #5506, #5413, #5409, #5401, #5337, #5318, and #5266 remain
blocked behind that source route.

### Phase 4/6 reports, profiling, naming, and conventions

The broad polish stream refreshed reports and tightened project conventions.

- #5800, #5801, #5806, #5807, #5808, #5809, #5811, #5812, #5813, #5814,
  #5815, and #5818 regenerated or refreshed timed-region profile reports
  after the bench-timed-region filtering amendment in #5781.
- #5762 and #5763 closed focused Phase 6 constructor-characterisation reviews
  for HexArith and HexModArith.
- #5799 added HexArith context `grind` coverage.
- #5778, #5780, #5798, #5827, and #5768 cleaned naming and process-jargon
  surfaces across code and docs.
- #5875 renamed `HexGfq*` library identifiers to `HexGFq*` per the acronym
  convention; kebab-case report/SPEC/status filenames intentionally remain
  unchanged.
- #5873 and #5860 trimmed stale planning/process language from project
  convention files, and #5858 forbids repeatedly skipping a previously skipped
  issue without changing the plan.

## Current frontier

### Queue snapshot

At checkpoint time there were no ordinary unclaimed work items.

Claimed work:

- #5885, this checkpoint.
- #4334, HexLLL inconclusive scientific benchmark verdicts.

Issues with PRs:

- #5868, HO-5d-1b-cleanup-D for `HBZMathlib/IntReductionMod.lean`.

Open PRs:

- #5884, `HO-5d-1b-cleanup-D: migrate HBZMathlib/IntReductionMod.lean proof
  bodies off unfold Hex.choosePrimeData`.
- #5883, `feat: add Pluecker mDet expansion helpers`.
- #2656, draft SPEC PR for real roots and Sturm.

Open directives:

- #2564 is claimed and remains the HO-1/BZ headline-correctness directive.
- #2567 is blocked on #2564.
- #2637 is blocked on its prerequisite chain, including #2567.

### Status script

`scripts/status.py` reports ready work across these libraries:

- Phase 6: `HexArith`, `HexPoly`, `HexMatrix`, `HexModArith`, `HexGF2`,
  `HexPolyFp`, `HexGFqField`, `HexHensel`, `HexConway`, `HexGFq`,
  `HexPolyMathlib`.
- Phase 5: `HexGramSchmidt`, `HexPolyZ`, `HexMatrixMathlib`,
  `HexModArithMathlib`.
- Phase 4: `HexLLL`, `HexBerlekamp`, `HexGramSchmidtMathlib`,
  `HexPolyZMathlib`, `HexHenselMathlib`, `HexGF2Mathlib`.
- Phase 1: `HexBerlekampZassenhaus`.

`HexGFqRing` is fully done. The planned-but-deferred libraries remain
`HexRoots`, `HexRootsMathlib`, `HexResultant`, `HexResultantMathlib`,
`HexNumberField`, and `HexNumberFieldMathlib`.

### Blocked chains to respect

- HO-5d/BZ fallback cleanup: let #5868/#5884 settle before #5869.
- HO/BZ headline correctness: #2564 remains the directive; dependent BZ
  bridge issues such as #4170, #4172, #4680, #4818, #4819, #4821, #4825,
  #4830, #4831, #4832, #4880, #5214, and #5215 remain blocked.
- BHKS D1: #5204, #5216, #5223, #5224, #5512, and #5237 remain the existing
  chain, with #2567 still blocked on HO-1.
- HexMatrix/Gram: #5851 is the Plucker proof frontier; #5848, #5805, and
  #5655 wait behind it.
- Schmeisser/de Bruijn-Springer: #5765 needs planner decomposition before
  #5735 and the downstream Schmeisser/Boyd chain can move.

## Recommended next actions

1. Let repair/normal review finish #5884, then claim #5869 as the final
   HO-5d fallback-removal step.
2. Let the Plucker PR #5883 and the #5851 replan state settle before claiming
   #5848 or the blocked Gram consumers.
3. Treat #4334 as the next HexLLL Phase 4 gate now that #5879 and #5881 have
   landed.
4. Replan #5765 into a genuine source-theorem path instead of sending another
   worker at the all-degree umbrella unchanged.
5. Dispatch further Phase 6 work as narrow polish or review items only; avoid
   duplicating the existing HO/BZ, BHKS D1, Plucker/Gram, and Schmeisser chains.
