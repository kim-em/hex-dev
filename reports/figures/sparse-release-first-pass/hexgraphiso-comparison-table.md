| family | n | C dense ms | C sparse ms | Traces ms | Hex dense / C dense | Hex sparse / C sparse | Hex sparse / Hex dense | IsoGraph / Hex sparse |
|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 | 0.019 | 0.010 | 61.39× | 36.59× | 0.26× | 1.03× |
| sparse-random | 32–3072 | 0.067 | 0.013 | 0.011 | 80.33× | 35.52× | 0.09× | 1.92× |
| paley | 13–1181 | 0.070 | 0.037 | 0.088 | 32.21× | 18.88× | 0.35× | 1.90× |
| grid | 9–2304 | 0.076 | 0.012 | 0.018 | 26.91× | 19.74× | 0.12× | 1.50× |
| hypercube | 8–2048 | 0.142 | 0.033 | 0.076 | 22.66× | 17.87× | 0.18× | 1.17× |
| circulant-12 | 8–3072 | 0.166 | 0.018 | 0.051 | 30.06× | 18.87× | 0.08× | 1.37× |
| circulant-1248 | 17–2049 | 0.242 | 0.031 | 0.073 | 29.14× | 19.64× | 0.09× | 1.16× |
| tree | 16–3072 | 0.252 | 0.148 | 0.011 | 30.95× | 14.08× | 0.29× | 1.81× |
| projective-plane | 14–1986 | 0.354 | 0.073 | 0.144 | 20.84× | 17.66× | 0.18× | 2.64× |
| hadamard | 16–2048 | 1.103 | 0.669 | 0.324 | 20.84× | 12.67× | 0.41× | 1.26× |
| union | 32–3072 | 1.173 | 0.189 | 0.267 | 17.56× | 15.82× | 0.18× | 2.37× |
| lattice | 25–1849 | 1.363 | 0.476 | 0.361 | 17.34× | 13.60× | 0.28× | 1.13× |
| johnson | 10–2016 | 4.801 | 1.584 | 1.252 | 16.83× | 11.12× | 0.23× | 2.15× |
| latin | 25–2025 | 4.912 | 2.050 | 0.890 | 22.19× | 6.79× | 0.14× | 2.76× |
| shrunken-multipede | 36–1956 | 6.107 | 37.797 | 1.114 | 16.79× | 17.49× | 0.12× | 7.28× |
| kneser | 10–2016 | 11.746 | 8.103 | 3.109 | 16.65× | 10.78× | 0.54× | 1.05× |
| cubic | 16–2048 | 22.253 | 8.674 | 0.092 | 9.20× | 5.62× | 0.22× | 1.33× |
| steiner | 50–1716 | 48.744 | 4.823 | 1.122 | 14.94× | 5.70× | 0.07× | 8.91× |
| cfi | 42–1946 | 213.814 | 6.467 | 4.032 | 22.99× | 9.06× | 0.04× | 2.85× |
| multipede | 66–2046 | 285.840 | 44.250 | 3.725 | 16.57× | 9.77× | 0.05× | 1.76× |
| all | 8–3072 | 0.659 | 0.138 | 0.155 | 27.06× | 17.71× | 0.25× | 1.34× |

Ratios are medians of per-instance ratios on the intersection of solved cases. C and IsoGraph samples are historical; Hex dense samples are also historical; Hex sparse was refreshed on the same shared host. These observations are not an adjacent before/after experiment.

| family | native sparse build ms | sparse runColored ms | checked canonicalization ms | relabel alone ms |
|---|---|---|---|---|
| random | 1.036 | 0.183 | 0.663 | 0.469 |
| sparse-random | 0.225 | 0.187 | 0.436 | 0.225 |
| paley | 0.568 | 0.429 | 0.701 | 0.237 |
| grid | 0.029 | 0.190 | 0.229 | 0.030 |
| hypercube | 0.043 | 0.542 | 0.592 | 0.044 |
| circulant-12 | 0.035 | 0.295 | 0.342 | 0.035 |
| circulant-1248 | 0.097 | 0.501 | 0.604 | 0.094 |
| tree | 0.026 | 1.874 | 1.917 | 0.026 |
| projective-plane | 0.166 | 1.094 | 1.287 | 0.176 |
| hadamard | 0.649 | 6.624 | 7.084 | 0.430 |
| union | 0.110 | 2.786 | 2.910 | 0.100 |
| lattice | 0.394 | 6.085 | 6.476 | 0.369 |
| johnson | 1.479 | 15.857 | 17.488 | 1.492 |
| latin | 2.335 | 10.842 | 13.587 | 2.708 |
| shrunken-multipede | 0.987 | 10.656 | 10.886 | 0.298 |
| kneser | 11.907 | 83.952 | 87.025 | 2.721 |
| cubic | 0.044 | 48.435 | 48.675 | 0.048 |
| steiner | 0.187 | 26.026 | 26.185 | 0.188 |
| cfi | 0.159 | 56.064 | 56.257 | 0.159 |
| multipede | 0.225 | 182.843 | 183.142 | 0.175 |

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
