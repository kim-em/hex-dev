| family | n | C dense ms | C sparse ms | Traces ms | Hex dense / C dense | Hex sparse / C sparse | Hex sparse / Hex dense | IsoGraph / Hex sparse |
|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 | 0.019 | 0.010 | 61.39× | 39.71× | 0.26× | 1.03× |
| sparse-random | 32–3072 | 0.067 | 0.013 | 0.011 | 80.33× | 36.10× | 0.09× | 1.93× |
| paley | 13–1181 | 0.070 | 0.037 | 0.088 | 32.21× | 21.31× | 0.44× | 1.59× |
| grid | 9–2304 | 0.076 | 0.012 | 0.018 | 26.91× | 19.99× | 0.12× | 1.48× |
| hypercube | 8–2048 | 0.142 | 0.033 | 0.076 | 22.66× | 17.99× | 0.19× | 1.16× |
| circulant-12 | 8–3072 | 0.166 | 0.018 | 0.051 | 30.06× | 18.80× | 0.08× | 1.38× |
| circulant-1248 | 17–2049 | 0.242 | 0.031 | 0.073 | 29.14× | 19.61× | 0.09× | 1.17× |
| tree | 16–3072 | 0.252 | 0.148 | 0.011 | 30.95× | 13.81× | 0.28× | 1.82× |
| projective-plane | 14–1986 | 0.354 | 0.073 | 0.144 | 20.84× | 17.79× | 0.18× | 2.63× |
| hadamard | 16–2048 | 1.103 | 0.669 | 0.324 | 20.84× | 12.76× | 0.41× | 1.32× |
| union | 32–3072 | 1.173 | 0.189 | 0.267 | 17.56× | 15.64× | 0.18× | 2.40× |
| lattice | 25–1849 | 1.363 | 0.476 | 0.361 | 17.34× | 13.82× | 0.28× | 1.13× |
| johnson | 10–2016 | 4.801 | 1.584 | 1.252 | 16.83× | 11.20× | 0.23× | 2.13× |
| latin | 25–2025 | 4.912 | 2.050 | 0.890 | 22.19× | 6.78× | 0.14× | 2.75× |
| shrunken-multipede | 36–1956 | 6.107 | 37.797 | 1.114 | 16.79× | 17.86× | 0.12× | 7.15× |
| kneser | 10–2016 | 11.746 | 8.103 | 3.109 | 16.65× | 10.83× | 0.54× | 1.04× |
| cubic | 16–2048 | 22.253 | 8.674 | 0.092 | 9.20× | 5.69× | 0.22× | 1.31× |
| steiner | 50–1716 | 48.744 | 4.823 | 1.122 | 14.94× | 5.74× | 0.07× | 8.78× |
| cfi | 42–1946 | 213.814 | 6.467 | 4.032 | 22.99× | 8.97× | 0.04× | 2.90× |
| multipede | 66–2046 | 285.840 | 44.250 | 3.725 | 16.57× | 9.83× | 0.05× | 1.75× |
| all | 8–3072 | 0.659 | 0.138 | 0.155 | 27.06× | 18.05× | 0.25× | 1.27× |

Ratios are medians of per-instance ratios on the intersection of solved cases. C and IsoGraph samples are historical; Hex dense samples are also historical; Hex sparse was refreshed on the same shared host. These observations are not an adjacent before/after experiment.

| family | native sparse build ms | sparse runColored ms | checked canonicalization ms | relabel alone ms |
|---|---|---|---|---|
| random | 1.026 | 0.179 | 0.663 | 0.462 |
| sparse-random | 0.223 | 0.188 | 0.435 | 0.224 |
| paley | 0.561 | 0.442 | 0.866 | 0.397 |
| grid | 0.029 | 0.192 | 0.231 | 0.031 |
| hypercube | 0.043 | 0.539 | 0.596 | 0.043 |
| circulant-12 | 0.034 | 0.293 | 0.338 | 0.034 |
| circulant-1248 | 0.094 | 0.498 | 0.603 | 0.092 |
| tree | 0.025 | 1.870 | 1.898 | 0.026 |
| projective-plane | 0.165 | 1.114 | 1.297 | 0.177 |
| hadamard | 0.649 | 6.684 | 7.137 | 0.432 |
| union | 0.108 | 2.771 | 2.893 | 0.102 |
| lattice | 0.372 | 6.181 | 6.579 | 0.374 |
| johnson | 1.449 | 16.116 | 17.601 | 1.413 |
| latin | 2.382 | 10.846 | 13.604 | 2.749 |
| shrunken-multipede | 0.906 | 10.792 | 11.021 | 0.297 |
| kneser | 11.996 | 85.734 | 87.726 | 2.661 |
| cubic | 0.043 | 49.217 | 49.165 | 0.047 |
| steiner | 0.168 | 25.981 | 26.529 | 0.186 |
| cfi | 0.156 | 55.493 | 55.365 | 0.157 |
| multipede | 0.220 | 184.795 | 183.794 | 0.173 |

Each cost column uses its own solved subset. Build and relabel are measured independently; their medians must not be subtracted from the canonicalization median.

| family | instances | nauty dense largest n solved | nauty sparse largest n solved | Traces largest n solved | Hex dense largest n solved | Hex sparse largest n solved | IsoGraph `canonical` largest n solved |
|---|---|---|---|---|---|---|---|
| random | 30 | 3072 | 3072 | 3072 | 3072 | 3072 | 3072 |
| sparse-random | 8 | 3072 | 3072 | 3072 | 3072 | 3072 | 3072 |
| paley | 20 | 1181 | 1181 | 1181 | 1181 | 1181 | 1181 |
| grid | 16 | 2304 | 2304 | 2304 | 2304 | 2304 | 2304 |
| hypercube | 9 | 2048 | 2048 | 2048 | 2048 | 2048 | 2048 |
| circulant-12 | 29 | 3072 | 3072 | 3072 | 3072 | 3072 | 3072 |
| circulant-1248 | 24 | 2049 | 2049 | 2049 | 2049 | 2049 | 2049 |
| tree | 9 | 3072 | 3072 | 3072 | 2048 (of 3072) | 3072 | 2048 (of 3072) |
| projective-plane | 9 | 1986 | 1986 | 1986 | 1986 | 1986 | 114 (of 1986) |
| hadamard | 8 | 2048 | 2048 | 2048 | 1024 (of 2048) | 2048 | 2048 |
| union | 14 | 3072 | 3072 | 3072 | 2048 (of 3072) | 3072 | 3072 |
| lattice | 21 | 1849 | 1849 | 1849 | 1849 | 1849 | 1849 |
| johnson | 24 | 2016 | 2016 | 2016 | 2016 | 2016 | 2016 |
| latin | 10 | 2025 | 2025 | 2025 | 2025 | 2025 | 2025 |
| shrunken-multipede | 21 | 420 (of 1956) | 804 (of 1956) | 324 (of 1956) | 420 (of 1956) | 420 (of 1956) | 228 (of 1956) |
| kneser | 24 | 2016 | 2016 | 2016 | 1326 (of 2016) | 2016 | 2016 |
| cubic | 12 | 1536 (of 2048) | 2048 | 2048 | 512 (of 2048) | 2048 | 1536 (of 2048) |
| steiner | 8 | 1716 | 1716 | 1716 | 1334 (of 1716) | 1716 | 1334 (of 1716) |
| cfi | 18 | 1946 | 1946 | 1946 | 938 (of 1946) | 1946 | 1946 |
| multipede | 19 | 1056 (of 2046) | 1716 (of 2046) | 1166 (of 2046) | 506 (of 2046) | 1276 (of 2046) | 836 (of 2046) |

Largest instance each implementation canonicalized inside the sweep's per-instance budget; a parenthesised size is the largest the corpus offered, so the family was cut off there.
