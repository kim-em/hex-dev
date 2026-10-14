# Interval comparison inventory

`sort.jsonl` records the actual unsorted assembly entries, finite or infinite
interval endpoints, outer insertion-sort comparison events, and final production
sort indices for the rational and quadratic families. The native replay checks
its complete output against `Root.sortBy`; the Python analyzer independently
checks event order, route selection, and strict order from separating endpoints.
`source.json` binds the raw output and source snapshots to their digests and the
executable used. `launcher.log` retains the enforced memory limits and analyzer
result. This is an untimed diagnostic.

The producer is pinned by the public
[`measurements/10378/interval-sort-source-v1`](https://github.com/kim-em/hex-dev/tree/measurements/10378/interval-sort-source-v1)
tag. The metadata records the repository path and Git blob of each source
snapshot.

Run `python3 -m unittest scripts.bench.test_real_closure_order` to recheck the
retained inventory, source digests, interval orders and summaries.

| Case | Comparisons | Full Thom | Interval | Common product |
| --- | ---: | ---: | ---: | ---: |
| Rational2 | 1 | 0 | 0 | 0 |
| Rational4 | 6 | 0 | 1 | 0 |
| Rational6 | 12 | 0 | 3 | 0 |
| Rational8 | 23 | 0 | 6 | 0 |
| Quadratic2 | 1 | 0 | 1 | 0 |
| Quadratic4 | 6 | 0 | 6 | 0 |
| Quadratic6 | 14 | 1 | 13 | 0 |
| Quadratic8 | 25 | 3 | 22 | 0 |

The remaining rational comparisons are point or mixed comparisons. Counts cover
the actual outer sorter calls. The retained paired Thom-order timing evidence
in `../real-closure-thom-order/` uses its original source and schema.
