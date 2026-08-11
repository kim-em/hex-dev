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

**Verdict: documented no-go.** The rejection half of the gate is met
(`hoeij_M12_f132` loses 77.9% of post-degree-check leaves, `legendre_P26`
48.0%), but only 2 of 392 rows have any degree the selected prime can form and
a retained prime cannot, the removed leaves are exactly the ones the trailing
filter already rejects (candidate constructions and exact divisions are
unchanged corpus-wide), and consulting costs up to 9.5% on the
Swinnerton-Dyer rows. Nothing was installed in production.

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
