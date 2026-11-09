# Additive monomial hashes

Each coordinate has a fixed 64-bit weight; a monomial's hash is the weighted sum of its exponents. Product degrees, support masks and full-width hashes combine from the factors' cached metadata. Every lookup still compares all exponents, so bases are unchanged; only the charged `work` counter differs, because collision-chain visits change.

A is the frozen main build and B the frozen additive-hash build. Both arms run identical CLI options with `MIMALLOC_ALLOW_THP=0` on one leased CPU, in adjacent AB/BA pairs, on the first primary size of all ten families in all three fields plus Eco-14/Eco-15 over F₂. The first campaign was inconclusive, so the protocol's one unchanged repeat follows it.

| Campaign | Pairs | Candidate B/A | Process B/A | Candidate B/A by field (2 / 32003 / 2³¹−1) |
|---|---:|---:|---:|---|
| first | 64 | 0.9991 | 0.9632 | 0.9933 / 0.9596 / 1.0474 |
| repeat | 64 | 0.9338 | 0.9450 | 0.9120 / 0.9401 / 0.9544 |

Pooled over both campaigns, the candidate ratio is 0.9659 and the process ratio 0.9541. Every pair has identical complete reduced bases and identical logical counters other than `work`. These are descriptive observations on the shared AMD EPYC 9455 host with every completed sample retained; the two campaigns differ materially, so only a modest improvement is supported. Certificate generation, independent certification and kernel checking are excluded. The fastest-open-source milestone remains open under issue #10987.
