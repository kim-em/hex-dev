| family | n | C dense ms | C sparse ms | Traces ms | Hex dense / C dense | Hex sparse / C sparse | Hex sparse / Hex dense | IsoGraph / Hex sparse |
|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 | 0.019 | 0.010 | 69.88× | 106.23× | 0.69× | 0.35× |
| sparse-random | 32–3072 | 0.067 | 0.013 | 0.011 | 98.23× | 170.35× | 0.31× | 0.41× |
| paley | 13–1181 | 0.070 | 0.037 | 0.088 | 35.05× | 35.18× | 0.68× | 0.96× |
| grid | 9–2304 | 0.076 | 0.012 | 0.018 | 31.91× | 59.45× | 0.31× | 0.50× |
| hypercube | 8–2048 | 0.142 | 0.033 | 0.076 | 27.86× | 31.49× | 0.36× | 0.70× |
| circulant-12 | 8–3072 | 0.166 | 0.018 | 0.051 | 33.17× | 51.21× | 0.20× | 0.50× |
| circulant-1248 | 17–2049 | 0.242 | 0.031 | 0.073 | 31.58× | 49.04× | 0.20× | 0.48× |
| tree | 16–3072 | 0.252 | 0.148 | 0.011 | 40.32× | 42.18× | 0.61× | 0.67× |
| projective-plane | 14–1986 | 0.354 | 0.073 | 0.144 | 24.07× | 29.03× | 0.31× | 1.90× |
| hadamard | 16–2048 | 1.103 | 0.669 | 0.324 | 20.61× | 15.54× | 0.47× | 1.12× |
| union | 32–3072 | 1.173 | 0.189 | 0.267 | 19.10× | 38.75× | 0.39× | 0.94× |
| lattice | 25–1849 | 1.363 | 0.476 | 0.361 | 17.92× | 21.37× | 0.42× | 0.73× |
| johnson | 10–2016 | 4.801 | 1.584 | 1.252 | 17.26× | 18.54× | 0.37× | 1.28× |
| latin | 25–2025 | 4.912 | 2.050 | 0.890 | 23.63× | 9.67× | 0.19× | 1.93× |
| shrunken-multipede | 36–1956 | 6.107 | 37.797 | 1.114 | 16.91× | 31.26× | 0.26× | 4.95× |
| kneser | 10–2016 | 11.746 | 8.103 | 3.109 | 16.83× | 11.98× | 0.61× | 0.95× |
| cubic | 16–2048 | 22.253 | 8.674 | 0.092 | 9.39× | 13.85× | 0.37× | 0.67× |
| steiner | 50–1716 | 48.744 | 4.823 | 1.122 | 15.34× | 13.56× | 0.15× | 3.65× |
| cfi | 42–1946 | 213.814 | 6.467 | 4.032 | 22.41× | 29.97× | 0.10× | 0.81× |
| multipede | 66–2046 | 285.840 | 44.250 | 3.725 | 16.54× | 22.36× | 0.10× | 0.74× |
| all | 8–3072 | 0.659 | 0.138 | 0.155 | 28.99× | 30.79× | 0.42× | 0.65× |

Ratios are medians of per-instance ratios on the intersection of solved cases. C and IsoGraph samples are historical; Hex sparse samples were added on the same shared host. These observations are not an adjacent before/after experiment.

| family | native sparse build ms | sparse runColored ms | checked canonicalization ms | relabel alone ms |
|---|---|---|---|---|
| random | 1.044 | 0.201 | 2.008 | 1.467 |
| sparse-random | 0.226 | 0.287 | 2.289 | 0.261 |
| paley | 0.558 | 0.451 | 1.439 | 0.781 |
| grid | 0.029 | 0.345 | 0.700 | 0.036 |
| hypercube | 0.043 | 0.732 | 0.973 | 0.050 |
| circulant-12 | 0.035 | 0.488 | 0.927 | 0.041 |
| circulant-1248 | 0.096 | 0.762 | 1.516 | 0.111 |
| tree | 0.025 | 4.915 | 5.655 | 0.032 |
| projective-plane | 0.167 | 1.521 | 2.490 | 0.209 |
| hadamard | 0.648 | 7.321 | 8.613 | 0.750 |
| union | 0.109 | 6.249 | 7.529 | 0.119 |
| lattice | 0.374 | 9.097 | 10.174 | 0.416 |
| johnson | 1.479 | 26.314 | 29.419 | 1.496 |
| latin | 2.329 | 12.267 | 18.556 | 3.149 |
| shrunken-multipede | 0.922 | 17.724 | 18.314 | 0.337 |
| kneser | 12.069 | 81.647 | 96.505 | 12.008 |
| cubic | 0.043 | 40.813 | 42.542 | 0.057 |
| steiner | 0.168 | 66.894 | 71.049 | 0.217 |
| cfi | 0.158 | 185.090 | 198.862 | 0.195 |
| multipede | 0.221 | 172.646 | 167.547 | 0.183 |

Each cost column uses its own solved subset. Build and relabel are measured independently; their medians must not be subtracted from the canonicalization median.

| family | instances | nauty dense largest n solved | nauty sparse largest n solved | Traces largest n solved | Hex dense largest n solved | Hex sparse largest n solved | IsoGraph `canonical` largest n solved |
|---|---|---|---|---|---|---|---|
| random | 30 | 3072 | 3072 | 3072 | 3072 | 3072 | 3072 |
| sparse-random | 8 | 3072 | 3072 | 3072 | 3072 | 3072 | 3072 |
| paley | 20 | 1181 | 1181 | 1181 | 1181 | 1181 | 1181 |
| grid | 16 | 2304 | 2304 | 2304 | 2304 | 2304 | 2304 |
| hypercube | 9 | 2048 | 2048 | 2048 | 1024 (of 2048) | 2048 | 2048 |
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
| cubic | 12 | 1536 (of 2048) | 2048 | 2048 | 512 (of 2048) | 1024 (of 2048) | 1536 (of 2048) |
| steiner | 8 | 1716 | 1716 | 1716 | 1334 (of 1716) | 1716 | 1334 (of 1716) |
| cfi | 18 | 1946 | 1946 | 1946 | 938 (of 1946) | 1946 | 1946 |
| multipede | 19 | 1056 (of 2046) | 1716 (of 2046) | 1166 (of 2046) | 506 (of 2046) | 946 (of 2046) | 836 (of 2046) |

Largest instance each implementation canonicalized inside the sweep's per-instance budget; a parenthesised size is the largest the corpus offered, so the family was cut off there.
