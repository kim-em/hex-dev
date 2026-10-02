| family | n | C dense ms | C sparse ms | Traces ms | Hex dense / C dense | Hex sparse / C sparse | Hex sparse / Hex dense | IsoGraph / Hex sparse |
|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 | 0.019 | 0.010 | 69.88× | 106.23× | 0.69× | 0.35× |
| sparse-random | 32–3072 | 0.067 | 0.013 | 0.011 | 98.23× | 170.38× | 0.31× | 0.41× |
| paley | 13–1181 | 0.070 | 0.037 | 0.088 | 35.05× | 35.21× | 0.69× | 0.92× |
| grid | 9–2304 | 0.076 | 0.012 | 0.018 | 31.91× | 113.47× | 0.57× | 0.27× |
| hypercube | 8–2048 | 0.142 | 0.033 | 0.076 | 27.86× | 31.70× | 0.36× | 0.70× |
| circulant-12 | 8–3072 | 0.166 | 0.018 | 0.051 | 33.17× | 65.71× | 0.23× | 0.44× |
| circulant-1248 | 17–2049 | 0.242 | 0.031 | 0.073 | 31.58× | 54.05× | 0.21× | 0.44× |
| tree | 16–3072 | 0.252 | 0.148 | 0.011 | 40.32× | 43.59× | 0.62× | 0.66× |
| projective-plane | 14–1986 | 0.354 | 0.073 | 0.144 | 24.07× | 29.10× | 0.31× | 1.90× |
| hadamard | 16–2048 | 1.103 | 0.669 | 0.324 | 20.61× | 23.39× | 0.72× | 0.66× |
| union | 32–3072 | 1.173 | 0.189 | 0.267 | 19.10× | 38.75× | 0.39× | 0.94× |
| lattice | 25–1849 | 1.363 | 0.476 | 0.361 | 17.92× | 21.73× | 0.42× | 0.72× |
| johnson | 10–2016 | 4.801 | 1.584 | 1.252 | 17.26× | 18.86× | 0.37× | 1.26× |
| latin | 25–2025 | 4.912 | 2.050 | 0.890 | 23.63× | 9.67× | 0.19× | 1.90× |
| shrunken-multipede | 36–1956 | 6.107 | 37.797 | 1.114 | 16.91× | 31.26× | 0.26× | 4.95× |
| kneser | 10–2016 | 11.746 | 8.103 | 3.109 | 16.83× | 12.08× | 0.62× | 0.93× |
| cubic | 16–2048 | 22.253 | 8.674 | 0.092 | 9.39× | 13.85× | 0.37× | 0.67× |
| steiner | 50–1716 | 48.744 | 4.823 | 1.122 | 15.34× | 14.11× | 0.15× | 3.40× |
| cfi | 42–1946 | 213.814 | 6.467 | 4.032 | 22.41× | 30.64× | 0.10× | 0.78× |
| multipede | 66–2046 | 285.840 | 44.250 | 3.725 | 16.54× | 22.36× | 0.10× | 0.74× |
| all | 8–3072 | 0.659 | 0.138 | 0.155 | 28.99× | 32.85× | 0.46× | 0.64× |

Ratios are medians of per-instance ratios on the intersection of solved cases. C and IsoGraph samples are historical; Hex sparse samples were added on the same shared host. These observations are not an adjacent before/after experiment.

| family | native sparse build ms | sparse runColored ms | checked canonicalization ms | relabel alone ms |
|---|---|---|---|---|
| random | 1.048 | 0.201 | 2.008 | 1.475 |
| sparse-random | 0.231 | 0.287 | 2.289 | 0.261 |
| paley | 0.559 | 0.453 | 1.446 | 0.781 |
| grid | 0.059 | 0.656 | 1.393 | 0.074 |
| hypercube | 0.043 | 0.732 | 0.973 | 0.050 |
| circulant-12 | 0.040 | 0.562 | 1.054 | 0.047 |
| circulant-1248 | 0.102 | 0.798 | 1.608 | 0.118 |
| tree | 0.025 | 5.167 | 5.774 | 0.032 |
| projective-plane | 0.167 | 1.634 | 2.541 | 0.209 |
| hadamard | 1.373 | 12.706 | 12.736 | 1.435 |
| union | 0.109 | 6.267 | 7.529 | 0.120 |
| lattice | 0.374 | 9.097 | 10.344 | 0.416 |
| johnson | 1.484 | 26.409 | 29.822 | 1.512 |
| latin | 2.343 | 12.272 | 18.683 | 3.151 |
| shrunken-multipede | 0.922 | 17.724 | 18.314 | 0.337 |
| kneser | 12.069 | 81.647 | 97.439 | 12.011 |
| cubic | 0.050 | 40.813 | 42.542 | 0.057 |
| steiner | 0.168 | 66.941 | 71.131 | 0.217 |
| cfi | 0.175 | 188.301 | 203.848 | 0.202 |
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
