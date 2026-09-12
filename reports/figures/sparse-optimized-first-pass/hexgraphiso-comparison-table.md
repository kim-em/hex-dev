| family | n | C dense ms | C sparse ms | Traces ms | Hex dense / C dense | Hex sparse / C sparse | Hex sparse / Hex dense | IsoGraph / Hex sparse |
|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 | 0.019 | 0.010 | 61.56× | 88.99× | 0.66× | 0.42× |
| sparse-random | 32–3072 | 0.067 | 0.013 | 0.011 | 81.41× | 40.81× | 0.10× | 1.70× |
| paley | 13–1181 | 0.070 | 0.037 | 0.088 | 32.35× | 30.81× | 0.66× | 1.09× |
| grid | 9–2304 | 0.076 | 0.012 | 0.018 | 27.04× | 22.84× | 0.14× | 1.29× |
| hypercube | 8–2048 | 0.142 | 0.033 | 0.076 | 24.88× | 23.64× | 0.34× | 0.76× |
| circulant-12 | 8–3072 | 0.166 | 0.018 | 0.051 | 30.06× | 20.26× | 0.09× | 1.26× |
| circulant-1248 | 17–2049 | 0.242 | 0.031 | 0.073 | 29.17× | 20.77× | 0.09× | 1.10× |
| tree | 16–3072 | 0.252 | 0.148 | 0.011 | 30.95× | 16.53× | 0.35× | 1.46× |
| projective-plane | 14–1986 | 0.354 | 0.073 | 0.144 | 21.11× | 19.90× | 0.20× | 2.31× |
| hadamard | 16–2048 | 1.103 | 0.669 | 0.324 | 20.84× | 13.17× | 0.43× | 1.26× |
| union | 32–3072 | 1.173 | 0.189 | 0.267 | 17.56× | 19.39× | 0.22× | 1.94× |
| lattice | 25–1849 | 1.363 | 0.476 | 0.361 | 17.34× | 15.45× | 0.31× | 1.01× |
| johnson | 10–2016 | 4.801 | 1.584 | 1.252 | 16.96× | 12.18× | 0.25× | 1.96× |
| latin | 25–2025 | 4.912 | 2.050 | 0.890 | 22.51× | 7.22× | 0.15× | 2.60× |
| shrunken-multipede | 36–1956 | 6.107 | 37.797 | 1.114 | 16.79× | 18.72× | 0.13× | 6.94× |
| kneser | 10–2016 | 11.746 | 8.103 | 3.109 | 16.65× | 10.94× | 0.57× | 1.04× |
| cubic | 16–2048 | 22.253 | 8.674 | 0.092 | 9.20× | 6.77× | 0.25× | 1.15× |
| steiner | 50–1716 | 48.744 | 4.823 | 1.122 | 14.94× | 6.48× | 0.07× | 7.79× |
| cfi | 42–1946 | 213.814 | 6.467 | 4.032 | 22.99× | 11.23× | 0.04× | 2.22× |
| multipede | 66–2046 | 285.840 | 44.250 | 3.725 | 16.57× | 10.35× | 0.06× | 1.52× |
| all | 8–3072 | 0.659 | 0.138 | 0.155 | 27.16× | 19.87× | 0.32× | 1.15× |

Ratios are medians of per-instance ratios on the intersection of solved cases. C and IsoGraph samples are historical; both Hex series were refreshed on the same shared host. These observations are not an adjacent before/after experiment.

| family | native sparse build ms | sparse runColored ms | checked canonicalization ms | relabel alone ms |
|---|---|---|---|---|
| random | 1.037 | 0.245 | 1.683 | 1.456 |
| sparse-random | 0.226 | 0.208 | 0.495 | 0.263 |
| paley | 0.557 | 0.457 | 1.245 | 0.769 |
| grid | 0.029 | 0.216 | 0.265 | 0.037 |
| hypercube | 0.089 | 1.206 | 1.186 | 0.059 |
| circulant-12 | 0.034 | 0.316 | 0.369 | 0.042 |
| circulant-1248 | 0.096 | 0.517 | 0.640 | 0.112 |
| tree | 0.025 | 2.326 | 2.444 | 0.031 |
| projective-plane | 0.168 | 1.229 | 1.451 | 0.209 |
| hadamard | 0.666 | 6.456 | 7.245 | 0.745 |
| union | 0.109 | 3.479 | 3.590 | 0.121 |
| lattice | 0.373 | 6.883 | 7.357 | 0.418 |
| johnson | 1.477 | 17.630 | 19.168 | 1.505 |
| latin | 2.354 | 11.033 | 14.275 | 3.119 |
| shrunken-multipede | 0.908 | 11.295 | 11.607 | 0.345 |
| kneser | 12.103 | 76.668 | 88.300 | 11.966 |
| cubic | 0.043 | 56.550 | 56.724 | 0.057 |
| steiner | 0.166 | 29.769 | 30.193 | 0.218 |
| cfi | 0.156 | 71.851 | 72.167 | 0.193 |
| multipede | 0.221 | 88.604 | 88.512 | 0.212 |

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
| multipede | 19 | 1056 (of 2046) | 1716 (of 2046) | 1166 (of 2046) | 506 (of 2046) | 946 (of 2046) | 836 (of 2046) |

Largest instance each implementation canonicalized inside the sweep's per-instance budget; a parenthesised size is the largest the corpus offered, so the family was cut off there.
