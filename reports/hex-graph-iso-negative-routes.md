# HexGraphIso negative-route evidence

## Verdict

The certificate/pairwise cost race is dead weight on the measured corpus.
Among 66 non-isomorphic pairs, 14 passed the root separator and had both
certificate and pairwise proofs available. The pairwise proof fit the race's
allowance in **0 of 14** cases. The certificate route therefore won every
actual race. The implementation now takes a certificate whenever one is
available and retains the full-budget pairwise decision as the fallback for
certificate exhaustion.

This change does not alter the selected kernel route for any measured case: 52
use the root separator and 14 use certificates. It removes the small compiled
pairwise probe that formerly preceded each selected certificate, while leaving
the resulting proof term unchanged. The refreshed end-to-end measurements
below record the new snapshot, but their single-run shifts do not isolate the
cost of that probe. The manual's canonicalization table is unaffected, and its
approximate ten-vertex tactic cost remains accurate.

## Method

Measurements were made on `chungus2` (AMD EPYC 9455), Linux 6.12.100, with
Lean 4.34.0-rc2. The source baseline was `73ac60177`; the route probe was run
before changing `Tactic.lean`. The branch was subsequently merged with `main`
through `71c32dfc9`, which reaches the negative path only through the
uncoloured wrapper of `HexGraphIso/Uncolored.lean` and leaves route selection,
certificate production, and the replay charges below unchanged; the end-to-end
retiming reported here was rerun after that merge.

The observation-only probe mirrored `Pairwise.search` while counting processed
nodes, ran `Nauty.certifyKeyBounded?` on both sides, counted certificate records
and automorphism payloads, evaluated `sepRootG` and `sepDiffG`, and reproduced
the old route-selection condition. It checked certificate availability under
`maxNodes = 10^8`, the normal per-side `maxCertNodes = 10^5`, and
`maxCheckerSteps = 10^9` (the scheduled CFI case used `4 * 10^9` checker
steps). All 66 pairs were confirmed non-isomorphic by the pairwise run.

The old race allowance was `floor(total certificate records / 4)`. A negative
pairwise result needs one more budget unit than the number of processed nodes,
because the final empty worklist is itself observed by the budgeted recursion.
The table therefore compares `pair budget` directly with the allowance used by
the tactic. `cert steps` is the tactic's replay charge, including automorphism
payloads and both fixed checks.

The corpus contains:

- the four negative cases from `HexGraphIso/TacticTests.lean`;
- all 16 negative decision pairs from `bench/HexGraphIso/Cactus.lean`;
- five negative pairings of committed conformance-fixture graphs, including
  the named and two recorded random graphs;
- the scheduled CFI pair, which agrees through every refinement invariant;
- 40 deterministic random pairs at `n = 6, 8, 12, 16, 24, 32, 48, 64`, with
  edge thresholds 0.1, 0.3, 0.5, 0.7, and 0.9.

Some named pairs deliberately occur in more than one corpus slice. They remain
separate observations because the question asked for each corpus to be run.

## Route observations

All 40 random pairs, all five irregular or same-root-distinguishable cactus
pairs, three of the four tactic cases, and four of the five fixture pairings
closed at the root separator. In those 52 cases the pairwise search processed
one node. Certificates were also within budget for every case, but neither
certificate nor pairwise replay entered the route race.

The 14 cases that reached the race were:

| corpus | pair | shape | n | cert records (G + H) | cert steps | pair nodes | pair budget | old allowance | shortfall | selected |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| tactic | Petersen / prism | cubic regular | 10 | 18 + 13 | 6,270 | 11 | 12 | 7 | 5 | certificate |
| cactus | C6 / 2C3 | 2-regular | 6 | 9 + 14 | 1,680 | 7 | 8 | 5 | 3 | certificate |
| cactus | C8 / 2C4 | 2-regular | 8 | 11 + 17 | 3,600 | 9 | 10 | 7 | 3 | certificate |
| cactus | C10 / 2C5 | 2-regular | 10 | 13 + 20 | 6,490 | 11 | 12 | 8 | 4 | certificate |
| cactus | C12 / 2C6 | 2-regular | 12 | 15 + 23 | 10,920 | 13 | 14 | 9 | 5 | certificate |
| cactus | C14 / 2C7 | 2-regular | 14 | 17 + 26 | 16,590 | 15 | 16 | 10 | 6 | certificate |
| cactus | C16 / 2C8 | 2-regular | 16 | 19 + 29 | 24,480 | 17 | 18 | 12 | 6 | certificate |
| cactus | circ(10,{2,5}) / circ(10,{1,5}) | cubic regular | 10 | 13 + 13 | 5,280 | 11 | 12 | 6 | 6 | certificate |
| cactus | Kneser(7,2) / Johnson(7,2) | 10-regular | 21 | 42 + 41 | 72,072 | 22 | 23 | 20 | 3 | certificate |
| cactus | circ48 / 2circ24 | 4-regular | 48 | 51 + 77 | 588,000 | 49 | 50 | 32 | 18 | certificate |
| cactus | circ96 / 2circ48 | 4-regular | 96 | 99 + 149 | 4,562,880 | 97 | 98 | 62 | 36 | certificate |
| cactus | Paley61 / circulant61 | 30-regular | 61 | 92 + 64 | 1,164,856 | 62 | 63 | 39 | 24 | certificate |
| fixture | Petersen / prism | cubic regular | 10 | 18 + 13 | 6,270 | 11 | 12 | 7 | 5 | certificate |
| scheduled | CFI(K4), untwisted / twisted | same refinement | 40 | 48 + 48 | 301,760 | 377 | 378 | 24 | 354 | certificate |

The closest result was Kneser(7,2) / Johnson(7,2): the pairwise proof needed a
budget of 23 against an allowance of 20, 15% over the cutoff. The ordinary
regular families needed 43% to 100% more budget than allowed. The deep CFI pair
needed 15.75 times the allowance. There was no family on which the pairwise
route approached a meaningful win.

Certificate production was available for every negative pair under the stated
limits. This campaign therefore did not exercise the fallback by natural
exhaustion; the existing `maxCertNodes := 0` tactic regression continues to pin
that behavior directly.

## Realized kernel cost

Fresh single-module forced-route profiles used `lean -j1 --profile`, excluding
the separately reported import time. These compare the exact proof routes on
three representative race-eligible shapes:

| pair | certificate type check | pairwise type check | pairwise / certificate |
|---|---:|---:|---:|
| C6 / 2C3 | 0.251 s | 0.370 s | 1.47x |
| Petersen / prism | 1.00 s | 3.36 s | 3.36x |
| Kneser(7,2) / Johnson(7,2) | 8.23 s | 53.9 s | 6.55x |

The measured wall-clock ordering agrees with the cost proxy in every forced
comparison. It also shows that the closest cost-unit margin does not conceal a
wall-clock pairwise win: on Kneser/Johnson, pairwise replay was more than six
times slower.

For full end-to-end context, the prescribed cactus retiming compares the
pre-change `hexgraphiso-tactic-152d306db788-chungus2.json` with the post-change
`hexgraphiso-tactic-822aaa497e13-chungus2.json`. The cycle ladder at
`n = 6, 8, 10, 12, 14, 16` changed from 0.262, 0.503, 0.863, 1.392, 2.043, and
3.019 seconds to 0.263, 0.496, 0.866, 1.549, 1.962, and 2.876 seconds. The
cubic circulant pair changed from 0.690 to 0.652 s, and Kneser/Johnson from
8.268 to 7.879 s. Across the 13 ordinary completed negative cases the
per-case change scattered from -14% to +56% with a median of -0.2%, against a
median of +0.4% over the twelve positive cases, whose route this change does
not touch. The largest single move, +56% on grid3x4/circulant12, is a
root-separator case whose code path is unchanged, so the scatter is run-to-run
noise on a shared host rather than a shift attributable to removing the race.
The long circ48/2circ24 sample exceeded the 120-second tactic frontier in both
runs, as did the 61- and 96-vertex hard negatives. The scheduled CFI
fresh-module median remains 33.899 s.

These end-to-end figures include tactic elaboration as well as kernel checking
and are not substituted for the forced-route type-check measurements above.
They refresh the committed tactic timing artifact and cactus figures. They do
not require edits to the manual's Performance table, which reports
canonicalization rather than tactic replay. The manual's separate approximate
ten-vertex negative range of 0.7 to 0.9 seconds sits at the edge of the
refreshed 0.652 and 0.866 s cases at that size; the ten-vertex cubic circulant
pair has been measured at 0.617, 0.652, and 0.690 s across three consecutive
single runs, so this is the resolution of a single retiming and not an
isolated timing change that requires revising the manual's claim.

## Decision

The old race performed a second compiled search after already producing both
certificates, but it did not select a pairwise proof anywhere in the corpus.
The simpler rule matches every observation and preserves all exhaustion
semantics:

1. use the root separator when it applies;
2. otherwise use certificates when they are available within budget;
3. if not, try the two-code separator;
4. finally run the full-budget pairwise decision, where `none` reports
   exhaustion and never closes the goal.
