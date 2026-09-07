| family | n | nauty (median) | Hex `canonicalize` | IsoGraph `canonical` | IsoGraph / Hex | Hex `runColored` | IsoGraph + build | Hex nodes | IsoGraph nodes |
|---|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.040 ms | 70× | 17.4× | 0.25× | 41× | 19.3× | 1.00× | 1.00× |
| sparse-random | 32–3072 | 0.054 ms | 103× | 17.1× | 0.13× | 39× | 24.0× | 1.00× | 1.00× |
| grid | 9–2304 | 0.067 ms | 35× | 5.2× | 0.16× | 20× | 7.5× | 1.00× | 1.50× |
| paley | 13–1181 | 0.071 ms | 35× | 20.7× | 0.63× | 23× | 21.3× | 1.00× | 1.00× |
| hypercube | 8–2048 | 0.143 ms | 27× | 4.8× | 0.24× | 26× | 5.6× | 1.00× | 1.25× |
| circulant-12 | 8–3072 | 0.166 ms | 33× | 2.8× | 0.10× | 26× | 4.2× | 1.00× | 1.00× |
| tree | 16–3072 | 0.227 ms | 68× | 21.6× | 0.31× | 46× | 25.1× | 1.00× | 1.00× |
| circulant-1248 | 17–2049 | 0.249 ms | 31× | 2.8× | 0.09× | 26× | 4.2× | 1.00× | 1.00× |
| projective-plane | 14–1986 | 0.334 ms | 25× | 46.0× | 1.65× | 16× | 40.9× | 1.00× | 1.87× |
| hadamard | 16–2048 | 1.092 ms | 22× | 9.1× | 0.48× | 21× | 9.1× | 1.00× | 1.13× |
| union | 32–3072 | 1.100 ms | 19× | 7.3× | 0.36× | 15× | 7.5× | 1.00× | 1.00× |
| lattice | 25–1849 | 1.345 ms | 18× | 5.5× | 0.31× | 17× | 5.7× | 1.00× | 0.57× |
| johnson | 10–2016 | 4.759 ms | 17× | 8.0× | 0.48× | 16× | 8.1× | 1.00× | 0.99× |
| latin | 25–2025 | 4.839 ms | 23× | 8.4× | 0.38× | 22× | 9.0× | 1.00× | 0.53× |
| shrunken-multipede | 36–1956 | 5.716 ms | 18× | 30.8× | 1.33× | 17× | 30.0× | 1.00× | 1.72× |
| kneser | 10–2016 | 11.819 ms | 17× | 7.8× | 0.51× | 16× | 7.8× | 1.00× | 1.49× |
| cubic | 16–2048 | 22.941 ms | 11× | 2.1× | 0.26× | 11× | 2.2× | 1.00× | 0.03× |
| steiner | 50–1716 | 44.239 ms | 16× | 8.7× | 0.57× | 17× | 8.8× | 1.00× | 0.27× |
| cfi | 42–1946 | 204.485 ms | 23× | 0.8× | 0.08× | 22× | 0.8× | 1.00× | 1.00× |
| multipede | 66–2046 | 265.921 ms | 18× | 1.1× | 0.09× | 18× | 1.1× | 1.00× | 0.42× |
| **all 333** | 8–3072 | 0.659 ms | 29× | 7.8× | 0.29× | 22× | 8.5× | 1.00× | 1.00× |

Ratios are per-instance medians against standalone nauty 2.9.3 on the same instance; the sixth column is the head-to-head. The last two are search-tree sizes against nauty's: `canonicalize` transcribes nauty's search and visits exactly its nodes on every instance, so its whole distance from nauty is per-node cost, while IsoGraph is a different search and its node count is what varies.

| family | instances | nauty largest n solved | Hex `canonicalize` largest n solved | IsoGraph `canonical` largest n solved |
|---|---|---|---|---|
| random | 30 | 3072 | 3072 | 3072 |
| sparse-random | 8 | 3072 | 3072 | 3072 |
| grid | 16 | 2304 | 2304 | 2304 |
| paley | 20 | 1181 | 1181 | 1181 |
| hypercube | 9 | 2048 | 1024 (of 2048) | 2048 |
| circulant-12 | 29 | 3072 | 3072 | 3072 |
| tree | 9 | 3072 | 2048 (of 3072) | 2048 (of 3072) |
| circulant-1248 | 24 | 2049 | 2049 | 2049 |
| projective-plane | 9 | 1986 | 1986 | 114 (of 1986) |
| hadamard | 8 | 2048 | 1024 (of 2048) | 2048 |
| union | 14 | 3072 | 2048 (of 3072) | 2048 (of 3072) |
| lattice | 21 | 1849 | 1849 | 1849 |
| johnson | 24 | 2016 | 2016 | 2016 |
| latin | 10 | 2025 | 2025 | 2025 |
| shrunken-multipede | 21 | 420 (of 1956) | 420 (of 1956) | 228 (of 1956) |
| kneser | 24 | 2016 | 1326 (of 2016) | 2016 |
| cubic | 12 | 1024 (of 2048) | 512 (of 2048) | 1536 (of 2048) |
| steiner | 8 | 1716 | 1334 (of 1716) | 1334 (of 1716) |
| cfi | 18 | 1946 | 938 (of 1946) | 1946 |
| multipede | 19 | 1056 (of 2046) | 506 (of 2046) | 836 (of 2046) |

Largest instance each implementation canonicalized inside the sweep's per-instance budget; a parenthesised size is the largest the corpus offered, so the family was cut off there.
