# Search comparison, 0250c5e83291

The four `hexgraphiso-search-0250c5e83291-chungus2-*.jsonl` files record
adjacent baseline/candidate arms in AB and BA order on chungus2 CPU 3.
Sibling metadata records executable digests, commands and host load.
All 98 cases retain identical traversal counts in both trials.

The baseline is the executable at `e1e94bf2f0b6fdb1bc513f437ce21abb17406bba`,
using `engine` mode and its `eng_ns` column. No runtime library code changed
between that revision and the tooling PR base `fe7d3432`; the latter changes
the measurement driver. The candidate at `886cf91a0` uses `search` mode and
`search_ns`. Baseline `eng_ns` follows another identical search, whereas the
candidate driver times one search. This difference in warm-up limits a
small timing comparison even though the search operation is the same.

Across all cases, candidate/baseline geometric mean search time is 1.0244
in trial 1 and 1.0023 in trial 2. The unchanged nauty comparator is 1.0083
and 1.0118 respectively. Both arms show timing variation; these observations
do not isolate a small speed change in the Lean search. The largest search
ratio, 1.6652, remains in trial 1. No completed sample is excluded.

The shared production operation bodies and full frozen trace agreement
support operational preservation. The paired times provide shared-host
context without establishing a speed improvement or a 2–3% regression.
For finer comparisons, build both source revisions with the same `search`
driver and use the same adjacent AB/BA schedule.
