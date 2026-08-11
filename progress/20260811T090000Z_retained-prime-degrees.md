# Retained-prime degree admissibility (issue #9153)

## Accomplished

**Proof bridge** (all four deliverables the issue asked for, kernel proved, no
`axiom`/`sorry`/`native_decide`):

- `HexBerlekampZassenhausMathlib.directDegreeBits_getElem?_iff` — the
  subset-degree bitset is true at an index exactly when some sub-multiset of
  the recorded modular factor degrees sums to it.
- `Hex.DirectPrimeProbe.Trial` and `Hex.directPrimePlan?_probes_trial` — every
  retained probe, not only the selected one, is the result of its own explicit
  good-prime trial with its degree data computed from that result.
- `directPrimePlan_probes_modPFactorization` / `directPrimePlan_probes_facts` —
  the `ModPFactorization` bundle and the `DirectPrimeFacts` contract for every
  retained probe. The old selected-only theorems are now corollaries at
  `plan.selected`.
- `exists_subMultiset_directFactorDegrees_of_dvd` and `reachableDegrees_of_dvd`
  — no false rejection: a probe that is its own trial marks the degree of every
  genuine integer divisor of the input as reachable.

**Measurement gate**: new `hexbz_factor_service --entry retainedPrimeProbe`
(a three-arm counted mirror of the proposal peel run) plus
`scripts/bench/retained_prime_probe.py`. Full-corpus record committed at
`reports/bench-results/hexbz-retained-prime-probe.json`; analysis in
`reports/hexbz-retained-prime-degrees.md`.

**Verdict: documented no-go**, but not for the reason the first draft gave.
Both halves of the issue's gate are met: `hoeij_M12_f132` loses 77.9% of its
post-degree-check leaves (`legendre_P26` 48.0%), and a predicate-only arm --
a short-circuiting scan that allocates nothing -- has a worst per-row
regression of 0.96% across the corpus, inside the measured floor. What fails is
the acceptance criterion behind those thresholds: every leaf the filter rejects
is one the trailing filter already rejects, so candidate constructions and
exact divisions are unchanged corpus-wide, and the entire saving is 77.5 µs on
a row that takes 960.9 ms end to end (0.008%) and 3.4 µs on one that takes
6.9 ms (0.049%). No sweep could show that. Nothing is installed in production.

An earlier draft of the report blamed an unfavourable cost; that was an
artifact of the counted arm's per-leaf allocation, and the predicate-only arm
was added to price the filter properly.

## Current frontier

The issue closes with the counterfactual report, which is the outcome its own
acceptance criteria name when the gate is not met. The proof bridge stands
independently and is what a future attempt would build on.

## Next step

Nothing follow-on is claimed. If someone revisits this, the report's closing
section names the one thing that would change the answer: the planner retains
at most one other trial and scores it on subset cost, never on whether its
degree pattern is *complementary* to the selected one. `rejectableDegrees` in
the committed record measures that property directly from the two degree
multisets, so a planner change can be evaluated without re-running a traversal.

## Blockers

None.
