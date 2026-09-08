| family | n | nauty (median) | Hex `canonicalize` | IsoGraph `canonical` | IsoGraph / Hex | Hex `runColored` | IsoGraph + build | sparse | Traces | Hex nodes | IsoGraph nodes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 ms | 70× | 16.9× | 0.24× | 41× | 19.2× | 0.46× | 0.32× | 1.00× | 1.00× |
| sparse-random | 32–3072 | 0.067 ms | 98× | 14.3× | 0.13× | 32× | 18.2× | 0.21× | 0.20× | 1.00× | 1.00× |
| paley | 13–1181 | 0.070 ms | 35× | 20.6× | 0.61× | 24× | 21.6× | 0.55× | 1.36× | 1.00× | 1.00× |
| grid | 9–2304 | 0.076 ms | 32× | 4.5× | 0.15× | 18× | 6.7× | 0.15× | 0.24× | 1.00× | 1.50× |
| hypercube | 8–2048 | 0.142 ms | 28× | 4.9× | 0.24× | 26× | 5.6× | 0.23× | 0.54× | 1.00× | 1.25× |
| circulant-12 | 8–3072 | 0.166 ms | 33× | 2.9× | 0.10× | 26× | 4.3× | 0.11× | 0.31× | 1.00× | 1.00× |
| circulant-1248 | 17–2049 | 0.242 ms | 32× | 2.9× | 0.09× | 26× | 4.4× | 0.13× | 0.31× | 1.00× | 1.00× |
| tree | 16–3072 | 0.252 ms | 40× | 15.1× | 0.39× | 28× | 16.3× | 0.52× | 0.04× | 1.00× | 1.00× |
| projective-plane | 14–1986 | 0.354 ms | 24× | 28.8× | 1.00× | 16× | 29.6× | 0.21× | 0.41× | 1.00× | 1.87× |
| hadamard | 16–2048 | 1.103 ms | 21× | 9.2× | 0.47× | 21× | 9.3× | 0.62× | 0.36× | 1.00× | 1.13× |
| union | 32–3072 | 1.173 ms | 19× | 6.8× | 0.35× | 15× | 7.1× | 0.17× | 0.25× | 1.00× | 1.00× |
| lattice | 25–1849 | 1.363 ms | 18× | 5.4× | 0.30× | 17× | 5.7× | 0.35× | 0.26× | 1.00× | 0.57× |
| johnson | 10–2016 | 4.801 ms | 17× | 7.9× | 0.47× | 16× | 8.0× | 0.33× | 0.27× | 1.00× | 0.99× |
| latin | 25–2025 | 4.912 ms | 24× | 8.4× | 0.38× | 21× | 9.0× | 0.42× | 0.18× | 1.00× | 0.53× |
| shrunken-multipede | 36–1956 | 6.107 ms | 17× | 27.8× | 1.29× | 17× | 26.8× | 0.12× | 1.48× | 1.00× | 1.72× |
| kneser | 10–2016 | 11.746 ms | 17× | 7.9× | 0.51× | 16× | 7.9× | 0.70× | 0.27× | 1.00× | 1.49× |
| cubic | 16–2048 | 22.253 ms | 9× | 1.7× | 0.28× | 9× | 1.7× | 0.23× | 0.00× | 1.00× | 0.03× |
| steiner | 50–1716 | 48.744 ms | 15× | 8.3× | 0.57× | 15× | 8.6× | 0.15× | 0.04× | 1.00× | 0.27× |
| cfi | 42–1946 | 213.814 ms | 22× | 0.8× | 0.07× | 23× | 0.8× | 0.03× | 0.02× | 1.00× | 1.00× |
| multipede | 66–2046 | 285.840 ms | 17× | 1.0× | 0.09× | 17× | 1.0× | 0.06× | 0.02× | 1.00× | 0.42× |
| **all 333** | 8–3072 | 0.659 ms | 29× | 7.6× | 0.29× | 23× | 8.3× | 0.36× | 0.27× | 1.00× | 1.00× |

Ratios are per-instance medians against standalone nauty 2.9.3 on the same instance; the sixth column is the head-to-head. The last two are search-tree sizes against nauty's: `canonicalize` transcribes nauty's search and visits exactly its nodes on every instance, so its whole distance from nauty is per-node cost, while IsoGraph is a different search and its node count is what varies.

| family | instances | nauty dense largest n solved | nauty sparse largest n solved | Traces largest n solved | Hex `canonicalize` largest n solved | IsoGraph `canonical` largest n solved |
|---|---|---|---|---|---|---|
| random | 30 | 3072 | 3072 | 3072 | 3072 | 3072 |
| sparse-random | 8 | 3072 | 3072 | 3072 | 3072 | 3072 |
| paley | 20 | 1181 | 1181 | 1181 | 1181 | 1181 |
| grid | 16 | 2304 | 2304 | 2304 | 2304 | 2304 |
| hypercube | 9 | 2048 | 2048 | 2048 | 1024 (of 2048) | 2048 |
| circulant-12 | 29 | 3072 | 3072 | 3072 | 3072 | 3072 |
| circulant-1248 | 24 | 2049 | 2049 | 2049 | 2049 | 2049 |
| tree | 9 | 3072 | 3072 | 3072 | 2048 (of 3072) | 2048 (of 3072) |
| projective-plane | 9 | 1986 | 1986 | 1986 | 1986 | 114 (of 1986) |
| hadamard | 8 | 2048 | 2048 | 2048 | 1024 (of 2048) | 2048 |
| union | 14 | 3072 | 3072 | 3072 | 2048 (of 3072) | 3072 |
| lattice | 21 | 1849 | 1849 | 1849 | 1849 | 1849 |
| johnson | 24 | 2016 | 2016 | 2016 | 2016 | 2016 |
| latin | 10 | 2025 | 2025 | 2025 | 2025 | 2025 |
| shrunken-multipede | 21 | 420 (of 1956) | 804 (of 1956) | 324 (of 1956) | 420 (of 1956) | 228 (of 1956) |
| kneser | 24 | 2016 | 2016 | 2016 | 1326 (of 2016) | 2016 |
| cubic | 12 | 1536 (of 2048) | 2048 | 2048 | 512 (of 2048) | 1536 (of 2048) |
| steiner | 8 | 1716 | 1716 | 1716 | 1334 (of 1716) | 1334 (of 1716) |
| cfi | 18 | 1946 | 1946 | 1946 | 938 (of 1946) | 1946 |
| multipede | 19 | 1056 (of 2046) | 1716 (of 2046) | 1166 (of 2046) | 506 (of 2046) | 836 (of 2046) |

Largest instance each implementation canonicalized inside the sweep's per-instance budget; a parenthesised size is the largest the corpus offered, so the family was cut off there.
