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
the resulting proof term unchanged, so the saving is elaboration-side and
small by construction. No end-to-end timing claim is made for it: the tactic
leg of the cactus figures varies by up to a factor of two between sessions on
this host with the executable unchanged, so that leg is published as `main`
measured it rather than re-measured here. The manual's canonicalization table
is unaffected, and its approximate ten-vertex tactic cost remains accurate.

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
exhaustion, and no pair in it reaches the fallback under the tactic's ordinary
limits.

The `maxCertNodes := 0` regressions do not pin the fallback either, contrary to
what a reading of their names suggests: `sepRootG p3 k3` is `true`, so the
coloured one closes at the root separator, and `sepDiffG` holds for
Petersen/prism, so the uncoloured one closes at the two-code separator. Both
separator legs are charged against `maxNodes` (four nodes for the root
separator, `2 * (n + 1)` for the two-code separator), so a budget in
`[4, 2 * (n + 1))` withdraws the two-code separator while still funding the
pairwise decision. `HexGraphIso/TacticTests.lean` now pins the fallback that
way, on the cubic Petersen/prism pair that the root separator does not take:
`(maxCertNodes := 0) (maxNodes := 21)` closes through `Pairwise.decideIso?` in
12 nodes, and `(maxNodes := 11)` reports pairwise exhaustion rather than
closing the goal.

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

For full end-to-end context, the prescribed cactus sweep was regenerated at
fingerprint `1e41767e7a03`. Its canonicalization leg is a compiled driver that
reports a minimum over repetitions, and it reproduces: against
`hexgraphiso-cactus-152d306db788-chungus2.jsonl` the 98 shared rows move by a
median of -0.3%, with the 10th and 90th percentiles at -1.7% and +1.1%. That
leg is measured here and carries the canonicalization figure.

The tactic leg is not measured here, because it does not reproduce on this
host. It is one `lake env lean` elaboration per case, and the machine is shared
with other build sessions. Across six sessions within two hours, on code whose
executable definitions never changed, `neg-c6-vs-2c3` gave 0.263, 0.263, 0.265,
0.475 and 0.543 s; `neg-c10-vs-2c5` gave 0.847, 0.866, 0.878, 1.435 and
1.546 s; and `neg-c14-vs-2c7` gave 1.891, 1.962, 2.851 and 3.562 s. A minimum
over three consecutive repetitions removes spikes but not a sustained
background load, and the system load average tracks the effect only loosely: a
3.562 s minimum-of-three for `neg-c14-vs-2c7` was recorded at load 11 and a
0.543 s `neg-c6-vs-2c3` at load 4. Some contended runs are not even monotonic
in the cycle length, which no property of the algorithm can explain.

`hexgraphiso-tactic-1e41767e7a03-chungus2.json` is therefore a byte-identical
copy of `hexgraphiso-tactic-04f38e84f6e2-chungus2.json`, the tactic figure
`main` currently publishes, and the meta file records that. The two
fingerprints differ in `HexGraphIso/Tactic.lean` and
`HexGraphIso/TacticTests.lean` only: the tests are not part of the measured
library, and the `Tactic.lean` change deletes a compiled probe while leaving
the emitted proof term identical on every pair in this corpus, so it can only
reduce elaboration time and cannot touch kernel replay. Carrying `main`'s
figure across unchanged states exactly that, where a fresh contended
measurement would have invented a difference.

Two consequences are inherited rather than introduced, and are recorded here
so that the next reader does not attribute them to this change. `main`'s
current tactic figure is itself a contended measurement: its cycle ladder at
`n = 6, 8, 10, 12, 14, 16` reads 0.955, 0.929, 1.595, 2.558, 3.590 and 4.959 s,
against 0.274, 0.493, 0.832, 1.327, 1.934 and 3.010 s at the preceding
graph-iso fingerprint on an executable path that did not change between them,
and it is not monotonic in the cycle length at the short end. Consequently the
manual's approximate ten-vertex negative range of 0.7 to 0.9 seconds no longer
matches the published tactic curve. Both facts are properties of `main` as it
stands; re-measuring the tactic leg on quiet hardware, or moving that leg to
the scheduled timing workflow, would settle them.

This report makes no end-to-end timing claim for this change. The load-bearing
evidence is the forced-route comparison above, whose two profiles were taken in
the same session on the same pair, so the ratio survives whatever the host was
doing. The long circ48/2circ24 sample and the 61- and 96-vertex hard negatives
sit at or beyond the 120-second tactic frontier and land on either side of it
between sessions. The scheduled CFI fresh-module median remains 33.899 s. The
manual's Performance table reports canonicalization rather than tactic replay
and comes from the reproducing compiled leg, so it is unaffected.

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
