| family | n | C dense ms | C sparse ms | Traces ms | Hex dense / C dense | Hex sparse / C sparse | Hex sparse / Hex dense | IsoGraph / Hex sparse |
|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 | 0.019 | 0.010 | 61.39× | 36.51× | 0.26× | 1.04× |
| sparse-random | 32–3072 | 0.067 | 0.013 | 0.011 | 80.33× | 35.29× | 0.09× | 1.94× |
| paley | 13–1181 | 0.070 | 0.037 | 0.088 | 32.21× | 18.76× | 0.35× | 1.91× |
| grid | 9–2304 | 0.076 | 0.012 | 0.018 | 26.91× | 19.65× | 0.12× | 1.51× |
| hypercube | 8–2048 | 0.142 | 0.033 | 0.076 | 22.66× | 17.68× | 0.18× | 1.18× |
| circulant-12 | 8–3072 | 0.166 | 0.018 | 0.051 | 30.06× | 18.61× | 0.08× | 1.38× |
| circulant-1248 | 17–2049 | 0.242 | 0.031 | 0.073 | 29.14× | 19.54× | 0.09× | 1.17× |
| tree | 16–3072 | 0.252 | 0.148 | 0.011 | 30.95× | 14.08× | 0.29× | 1.81× |
| projective-plane | 14–1986 | 0.354 | 0.073 | 0.144 | 20.84× | 17.56× | 0.18× | 2.66× |
| hadamard | 16–2048 | 1.103 | 0.669 | 0.324 | 20.84× | 12.61× | 0.41× | 1.34× |
| union | 32–3072 | 1.173 | 0.189 | 0.267 | 17.56× | 15.61× | 0.18× | 2.40× |
| lattice | 25–1849 | 1.363 | 0.476 | 0.361 | 17.34× | 13.60× | 0.28× | 1.14× |
| johnson | 10–2016 | 4.801 | 1.584 | 1.252 | 16.83× | 11.05× | 0.23× | 2.16× |
| latin | 25–2025 | 4.912 | 2.050 | 0.890 | 22.19× | 6.77× | 0.14× | 2.77× |
| shrunken-multipede | 36–1956 | 6.107 | 37.797 | 1.114 | 16.79× | 17.49× | 0.12× | 7.28× |
| kneser | 10–2016 | 11.746 | 8.103 | 3.109 | 16.65× | 10.78× | 0.54× | 1.05× |
| cubic | 16–2048 | 22.253 | 8.674 | 0.092 | 9.20× | 5.57× | 0.22× | 1.34× |
| steiner | 50–1716 | 48.744 | 4.823 | 1.122 | 14.94× | 5.68× | 0.07× | 8.91× |
| cfi | 42–1946 | 213.814 | 6.467 | 4.032 | 22.99× | 9.01× | 0.04× | 2.86× |
| multipede | 66–2046 | 285.840 | 44.250 | 3.725 | 16.57× | 9.77× | 0.05× | 1.76× |
| all | 8–3072 | 0.659 | 0.138 | 0.155 | 27.06× | 17.61× | 0.25× | 1.37× |

Ratios are medians of per-instance ratios on the intersection of solved cases. C and IsoGraph samples are historical; Hex dense samples are also historical; Hex sparse was refreshed on the same shared host. These observations are not an adjacent before/after experiment.

| family | native sparse build ms | sparse runColored ms | checked canonicalization ms | relabel alone ms |
|---|---|---|---|---|
| random | 1.036 | 0.183 | 0.662 | 0.464 |
| sparse-random | 0.225 | 0.187 | 0.433 | 0.224 |
| paley | 0.560 | 0.427 | 0.696 | 0.234 |
| grid | 0.029 | 0.187 | 0.228 | 0.030 |
| hypercube | 0.042 | 0.534 | 0.586 | 0.043 |
| circulant-12 | 0.035 | 0.293 | 0.337 | 0.035 |
| circulant-1248 | 0.095 | 0.499 | 0.602 | 0.093 |
| tree | 0.026 | 1.873 | 1.917 | 0.026 |
| projective-plane | 0.165 | 1.087 | 1.280 | 0.176 |
| hadamard | 0.646 | 6.595 | 7.054 | 0.430 |
| union | 0.110 | 2.770 | 2.888 | 0.100 |
| lattice | 0.372 | 6.085 | 6.476 | 0.368 |
| johnson | 1.460 | 15.827 | 17.357 | 1.449 |
| latin | 2.335 | 10.797 | 13.587 | 2.700 |
| shrunken-multipede | 0.917 | 10.656 | 10.886 | 0.298 |
| kneser | 11.907 | 83.952 | 87.005 | 2.721 |
| cubic | 0.044 | 48.012 | 48.274 | 0.048 |
| steiner | 0.169 | 25.941 | 26.185 | 0.186 |
| cfi | 0.159 | 55.789 | 56.127 | 0.158 |
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
