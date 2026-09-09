# Graph-isomorphism measurement archive

Current commands, corpus definitions and acceptance criteria are in the
[HexGraphIso SPEC](../HexGraphIso/SPEC/hex-graph-iso.md#benchmarks).
The performance headlines are [HexGraphIso](hex-graph-iso-performance.md)
and [HexGraphIsoMathlib](hex-graph-iso-mathlib-performance.md).

The files under `bench-results/hexgraphiso-*` and
`bench-results/hex-graph-iso-*` retain their original measurements. Source
fingerprints and matching manifests identify the code; sibling metadata
records the source commit, host, command and trial information available
for each observation. Reproduce a historical observation with the harness
from its recorded source revision. Archived `lit_ns` and `eng_ns` columns
are interpreted by `scripts/bench/graphiso_archive.py`; new runs use
`search_ns`. Comparison reports identify the recorded column on each side.

| Evidence | Provenance |
|---|---|
| [Compiled benchmark suite](bench-results/hex-graph-iso-compiled-b5ebc89a0-chungus2.json) | Source `b5ebc89a0`, chungus2; fixed public operations and declared complexity models. |
| [Search measurements, ddc22cf4b645](bench-results/hexgraphiso-engine-ddc22cf4b645-chungus2.meta.json) | Initial structured-search measurements; three trial files, allocation profiles, admission and oracle logs retain this prefix. |
| [Search measurements, 4a7c8747f686](bench-results/hexgraphiso-engine-4a7c8747f686-chungus2.meta.json) | Source `7a536cad3b41`, chungus2 CPU 91; the adopted structured search. |
| [Replay measurements, 7e28eb7ddb6c](bench-results/hexgraphiso-kernel-7e28eb7ddb6c-chungus2.json), [d78dade3633a](bench-results/hexgraphiso-kernel-d78dade3633a-chungus2.json) | Kernel replay observations retain their own source and input metadata. |
| [Mathlib proof probes](bench-results/hexgraphiso-mathlib-20260903-chungus2.json) | Raw samples from the September 3 report; the report's Git blob identifies their provenance. These are shared-host observations without CPU pinning. |
| [Full traversal baseline](../conformance-fixtures/HexGraphIso/trace.meta.json) | 39,032 records from `e1e94bf2f0b6fdb1bc513f437ce21abb17406bba`; input and output digests accompany the compressed records. |

The [120-vertex pruning input](../conformance-fixtures/HexGraphIso/prune.json)
is the relabelled union of untwisted and twisted CFI graphs over the
triangular prism. The observations recorded in
[the locality report at f45ccab8](https://github.com/kim-em/hex-dev/blob/f45ccab8fed20616c89ae5da785b5c63d2bd4bc1/reports/hex-graph-iso-locality.md)
were 168 nodes with the full stored-pair scan and 712 with the newest 32
pairs, with 11 accepted generators and identical canonical rows and path
codes. These are traversal observations, not timing measurements. The
production regression uses the full scan.
