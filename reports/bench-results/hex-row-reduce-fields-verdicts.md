# Field inverse and solve scientific verdicts

Every name below is in `Hex.RowReduceBench.Field`. Source: bounded input generator
commit `9c14175b0`; model and ladder are unchanged between the primary run and
the single rerun. All raw rows remain in the linked JSON artifacts.

[Primary run](hex-row-reduce-fields-bounded.json) · [Rerun](hex-row-reduce-fields-rerun.json)

Mode 1 means two-sided parametric. Mode 2 means the documented quadratic
arithmetic upper bound: a negative residual slope is assessed as within the
declared upper bound (observed faster), separately from the harness verdict.
The slope is the residual exponent after dividing by the declared model.

| Target | Model / mode | Primary verdict | Residual slope | C range | Rerun verdict / slope | Assessment |
|---|---|---|---:|---:|---|---|
| `rat8FullSolve` | `n ^ 3` / 1 | consistent | -0.040 | 1003.049–1148.285 | — | consistent |
| `rat8FullOption` | `n ^ 3` / 1 | consistent | -0.063 | 994.578–1134.216 | — | consistent |
| `rat8FullInverse` | `n ^ 3` / 1 | consistent | +0.036 | 1020.167–1112.771 | — | consistent |
| `rat8DeficientSolve` | `n ^ 3` / 1 | consistent | +0.065 | 847.747–987.541 | — | consistent |
| `rat8DeficientOption` | `n ^ 3` / 1 | consistent | +0.035 | 910.598–973.457 | — | consistent |
| `rat8DeficientInverse` | `n ^ 3` / 1 | consistent | +0.097 | 775.763–947.626 | — | consistent |
| `rat8HalfSolve` | `n ^ 3` / 1 | consistent | -0.132 | 384.818–510.141 | — | consistent |
| `rat8HalfOption` | `n ^ 3` / 1 | inconclusive | -0.153 | 363.377–501.833 | inconclusive / -0.157 | inconclusive |
| `rat8HalfInverse` | `n ^ 3` / 1 | consistent | -0.049 | 350.625–388.665 | — | consistent |
| `rat8DeficientErrorSolve` | `n ^ 3` / 1 | consistent | +0.048 | 847.061–934.989 | — | consistent |
| `rat8DeficientErrorOption` | `n ^ 3` / 1 | consistent | +0.061 | 838.133–952.451 | — | consistent |
| `rat8HalfErrorSolve` | `n ^ 3` / 1 | consistent | -0.101 | 359.353–444.401 | — | consistent |
| `rat8HalfErrorOption` | `n ^ 3` / 1 | consistent | -0.090 | 366.358–444.450 | — | consistent |
| `rat8TallSolve` | `n ^ 3` / 1 | consistent | -0.080 | 2122.286–2511.712 | — | consistent |
| `rat8TallOption` | `n ^ 3` / 1 | consistent | -0.091 | 2132.562–2572.345 | — | consistent |
| `rat8WideSolve` | `n ^ 3` / 1 | consistent | -0.057 | 1488.251–1669.136 | — | consistent |
| `rat8WideOption` | `n ^ 3` / 1 | consistent | -0.069 | 1507.301–1747.551 | — | consistent |
| `rat32FullSolve` | `n ^ 3` / 1 | consistent | +0.093 | 2205.161–2654.584 | — | consistent |
| `rat32FullOption` | `n ^ 3` / 1 | consistent | +0.067 | 1997.747–2327.107 | — | consistent |
| `rat32FullInverse` | `n ^ 3` / 1 | consistent | +0.144 | 1667.396–2234.984 | — | consistent |
| `rat32DeficientSolve` | `n ^ 3` / 1 | inconclusive | +0.217 | 1415.073–2194.002 | inconclusive / +0.216 | inconclusive |
| `rat32DeficientOption` | `n ^ 3` / 1 | consistent | +0.124 | 1620.263–2142.009 | — | consistent |
| `rat32DeficientInverse` | `n ^ 3` / 1 | inconclusive | +0.314 | 1364.896–2512.590 | inconclusive / +0.278 | inconclusive |
| `rat32HalfSolve` | `n ^ 3` / 1 | consistent | -0.018 | 654.558–741.976 | — | consistent |
| `rat32HalfOption` | `n ^ 3` / 1 | consistent | -0.019 | 640.428–727.744 | — | consistent |
| `rat32HalfInverse` | `n ^ 3` / 1 | consistent | +0.080 | 586.525–696.674 | — | consistent |
| `rat32DeficientErrorSolve` | `n ^ 3` / 1 | inconclusive | +0.234 | 1349.828–2197.146 | inconclusive / +0.217 | inconclusive |
| `rat32DeficientErrorOption` | `n ^ 3` / 1 | inconclusive | +0.239 | 1343.097–2175.769 | inconclusive / +0.227 | inconclusive |
| `rat32HalfErrorSolve` | `n ^ 3` / 1 | consistent | +0.022 | 614.610–688.774 | — | consistent |
| `rat32HalfErrorOption` | `n ^ 3` / 1 | consistent | -0.048 | 617.267–766.202 | — | consistent |
| `rat32TallSolve` | `n ^ 3` / 1 | consistent | +0.064 | 3786.760–4378.450 | — | consistent |
| `rat32TallOption` | `n ^ 3` / 1 | consistent | +0.070 | 3749.880–4364.974 | — | consistent |
| `rat32WideSolve` | `n ^ 3` / 1 | consistent | +0.102 | 2825.173–3469.354 | — | consistent |
| `rat32WideOption` | `n ^ 3` / 1 | consistent | +0.095 | 2755.898–3324.399 | — | consistent |
| `rat128FullSolve` | `n ^ 3` / 1 | consistent | -0.002 | 3852.018–3952.610 | — | consistent |
| `rat128FullOption` | `n ^ 3` / 1 | consistent | +0.017 | 3848.012–4091.429 | — | consistent |
| `rat128FullInverse` | `n ^ 3` / 1 | consistent | +0.050 | 3537.475–3946.973 | — | consistent |
| `rat128DeficientSolve` | `n ^ 3` / 1 | consistent | +0.127 | 3296.633–4316.526 | — | consistent |
| `rat128DeficientOption` | `n ^ 3` / 1 | consistent | +0.140 | 2945.955–3977.960 | — | consistent |
| `rat128DeficientInverse` | `n ^ 3` / 1 | inconclusive | +0.170 | 2611.343–3766.819 | inconclusive / +0.191 | inconclusive |
| `rat128HalfSolve` | `n ^ 3` / 1 | consistent | -0.045 | 1279.459–1410.418 | — | consistent |
| `rat128HalfOption` | `n ^ 3` / 1 | consistent | -0.051 | 778.574–866.929 | — | consistent |
| `rat128HalfInverse` | `n ^ 3` / 1 | inconclusive | +0.232 | 709.632–1211.731 | consistent / +0.040 | consistent on rerun; first inconclusive |
| `rat128DeficientErrorSolve` | `n ^ 3` / 1 | consistent | +0.120 | 2860.709–3680.404 | — | consistent |
| `rat128DeficientErrorOption` | `n ^ 3` / 1 | consistent | +0.121 | 3234.628–4161.039 | — | consistent |
| `rat128HalfErrorSolve` | `n ^ 3` / 1 | consistent | -0.023 | 1410.979–1487.288 | — | consistent |
| `rat128HalfErrorOption` | `n ^ 3` / 1 | consistent | -0.030 | 1410.124–1507.324 | — | consistent |
| `rat128TallSolve` | `n ^ 3` / 1 | consistent | -0.031 | 7862.784–8386.798 | — | consistent |
| `rat128TallOption` | `n ^ 3` / 1 | consistent | -0.029 | 6929.808–7392.366 | — | consistent |
| `rat128WideSolve` | `n ^ 3` / 1 | consistent | +0.000 | 5648.453–5760.682 | — | consistent |
| `rat128WideOption` | `n ^ 3` / 1 | consistent | -0.003 | 5647.412–5694.826 | — | consistent |
| `modularFullSolve` | `n ^ 3` / 1 | inconclusive | -0.208 | 93.883–145.446 | inconclusive / -0.225 | inconclusive |
| `modularFullOption` | `n ^ 3` / 1 | inconclusive | -0.215 | 93.424–145.966 | inconclusive / -0.229 | inconclusive |
| `modularFullInverse` | `n ^ 3` / 1 | inconclusive | -0.171 | 93.082–132.596 | inconclusive / -0.173 | inconclusive |
| `modularDeficientSolve` | `n ^ 3` / 1 | consistent | -0.129 | 91.391–119.331 | — | consistent |
| `modularDeficientOption` | `n ^ 3` / 1 | consistent | -0.124 | 91.733–118.583 | — | consistent |
| `modularDeficientInverse` | `n ^ 3` / 1 | consistent | -0.062 | 90.733–102.485 | — | consistent |
| `modularHalfSolve` | `n ^ 3` / 1 | inconclusive | -0.336 | 38.010–76.153 | inconclusive / -0.352 | inconclusive |
| `modularHalfOption` | `n ^ 3` / 1 | inconclusive | -0.333 | 37.987–75.802 | inconclusive / -0.355 | inconclusive |
| `modularHalfInverse` | `n ^ 3` / 1 | consistent | -0.101 | 22.290–33.206 | — | consistent |
| `modularDeficientErrorSolve` | `n ^ 3` / 1 | consistent | -0.101 | 53.415–65.309 | — | consistent |
| `modularDeficientErrorOption` | `n ^ 3` / 1 | consistent | -0.103 | 52.400–64.402 | — | consistent |
| `modularHalfErrorSolve` | `n ^ 3` / 1 | inconclusive | -0.259 | 21.087–36.344 | inconclusive / -0.258 | inconclusive |
| `modularHalfErrorOption` | `n ^ 3` / 1 | inconclusive | -0.246 | 36.482–60.940 | inconclusive / -0.253 | inconclusive |
| `modularTallSolve` | `n ^ 3` / 1 | consistent | +0.009 | 141.837–209.260 | — | consistent |
| `modularTallOption` | `n ^ 3` / 1 | inconclusive | -0.184 | 214.805–316.492 | inconclusive / -0.212 | inconclusive |
| `modularWideSolve` | `n ^ 3` / 1 | inconclusive | -0.510 | 82.729–216.019 | inconclusive / -0.229 | inconclusive |
| `modularWideOption` | `n ^ 3` / 1 | inconclusive | -0.231 | 80.147–129.569 | inconclusive / -0.227 | inconclusive |
| `functionsFullSolve` | `n ^ 3` / 1 | inconclusive | +0.152 | 57907.502–71455.845 | consistent / +0.126 | consistent on rerun; first inconclusive |
| `functionsFullOption` | `n ^ 3` / 1 | consistent | +0.124 | 57195.865–67910.014 | — | consistent |
| `functionsFullInverse` | `n ^ 3` / 1 | inconclusive | +0.293 | 65847.494–98833.117 | inconclusive / +0.287 | inconclusive |
| `functionsDeficientSolve` | `n ^ 3` / 1 | inconclusive | +0.653 | 30756.513–76065.750 | inconclusive / +0.662 | inconclusive |
| `functionsDeficientOption` | `n ^ 3` / 1 | inconclusive | +0.655 | 30566.130–75794.371 | inconclusive / +0.664 | inconclusive |
| `functionsDeficientInverse` | `n ^ 3` / 1 | inconclusive | +0.898 | 18952.211–65820.055 | inconclusive / +0.913 | inconclusive |
| `functionsHalfSolve` | `n ^ 3` / 1 | consistent | -0.037 | 26757.240–30678.594 | — | consistent |
| `functionsHalfOption` | `n ^ 3` / 1 | consistent | -0.036 | 26875.438–30688.524 | — | consistent |
| `functionsHalfInverse` | `n ^ 3` / 1 | inconclusive | +0.219 | 18928.218–25625.506 | inconclusive / +0.236 | inconclusive |
| `functionsDeficientErrorSolve` | `n ^ 3` / 1 | inconclusive | +0.672 | 18148.812–46071.479 | inconclusive / +0.694 | inconclusive |
| `functionsDeficientErrorOption` | `n ^ 3` / 1 | inconclusive | +0.669 | 29950.780–75767.582 | inconclusive / +0.690 | inconclusive |
| `functionsHalfErrorSolve` | `n ^ 3` / 1 | consistent | -0.022 | 26568.839–29910.828 | — | consistent |
| `functionsHalfErrorOption` | `n ^ 3` / 1 | consistent | -0.016 | 26446.105–29715.795 | — | consistent |
| `functionsTallSolve` | `n ^ 3` / 1 | consistent | +0.047 | 154307.950–164741.408 | — | consistent |
| `functionsTallOption` | `n ^ 3` / 1 | consistent | +0.051 | 154099.124–165365.861 | — | consistent |
| `functionsWideSolve` | `n ^ 3` / 1 | inconclusive | +0.174 | 125861.400–160147.224 | inconclusive / +0.174 | inconclusive |
| `functionsWideOption` | `n ^ 3` / 1 | inconclusive | +0.175 | 125520.347–159994.252 | inconclusive / +0.171 | inconclusive |
| `height8FullSolve` | `n ^ 2` / 2 | inconclusive | -1.467 | 25.795–1514.469 | — | within upper bound (observed faster) |
| `height8FullOption` | `n ^ 2` / 2 | inconclusive | -1.468 | 25.536–1513.813 | — | within upper bound (observed faster) |
| `height8FullInverse` | `n ^ 2` / 2 | inconclusive | -1.497 | 21.162–1404.545 | — | within upper bound (observed faster) |
| `height8DeficientSolve` | `n ^ 2` / 2 | inconclusive | -1.510 | 28.020–1893.329 | — | within upper bound (observed faster) |
| `height8DeficientOption` | `n ^ 2` / 2 | inconclusive | -1.510 | 28.097–1891.381 | — | within upper bound (observed faster) |
| `height8DeficientInverse` | `n ^ 2` / 2 | inconclusive | -1.524 | 22.645–1615.542 | — | within upper bound (observed faster) |
| `height8HalfSolve` | `n ^ 2` / 2 | inconclusive | -1.599 | 12.187–1056.234 | — | within upper bound (observed faster) |
| `height8HalfOption` | `n ^ 2` / 2 | inconclusive | -1.600 | 12.232–1060.863 | — | within upper bound (observed faster) |
| `height8HalfInverse` | `n ^ 2` / 2 | inconclusive | -1.565 | 10.119–805.294 | — | within upper bound (observed faster) |
| `height8DeficientErrorSolve` | `n ^ 2` / 2 | inconclusive | -1.494 | 27.680–1784.716 | — | within upper bound (observed faster) |
| `height8DeficientErrorOption` | `n ^ 2` / 2 | inconclusive | -1.505 | 30.769–2042.745 | — | within upper bound (observed faster) |
| `height8HalfErrorSolve` | `n ^ 2` / 2 | inconclusive | -1.385 | 11.734–590.305 | — | within upper bound (observed faster) |
| `height8HalfErrorOption` | `n ^ 2` / 2 | inconclusive | -1.569 | 11.851–947.589 | — | within upper bound (observed faster) |
| `height8TallSolve` | `n ^ 2` / 2 | inconclusive | -1.568 | 67.677–5359.579 | — | within upper bound (observed faster) |
| `height8TallOption` | `n ^ 2` / 2 | inconclusive | -1.567 | 67.730–5368.101 | — | within upper bound (observed faster) |
| `height8WideSolve` | `n ^ 2` / 2 | inconclusive | -1.474 | 35.798–2174.318 | — | within upper bound (observed faster) |
| `height8WideOption` | `n ^ 2` / 2 | inconclusive | -1.465 | 36.150–2134.473 | — | within upper bound (observed faster) |
| `height16FullSolve` | `n ^ 2` / 2 | inconclusive | -1.460 | 194.670–10991.957 | — | within upper bound (observed faster) |
| `height16FullOption` | `n ^ 2` / 2 | inconclusive | -1.493 | 292.496–17985.065 | — | within upper bound (observed faster) |
| `height16FullInverse` | `n ^ 2` / 2 | inconclusive | -1.499 | 269.101–16991.553 | — | within upper bound (observed faster) |
| `height16DeficientSolve` | `n ^ 2` / 2 | inconclusive | -1.463 | 173.870–9695.607 | — | within upper bound (observed faster) |
| `height16DeficientOption` | `n ^ 2` / 2 | inconclusive | -1.518 | 245.228–16249.620 | — | within upper bound (observed faster) |
| `height16DeficientInverse` | `n ^ 2` / 2 | inconclusive | -1.526 | 223.531–15227.547 | — | within upper bound (observed faster) |
| `height16HalfSolve` | `n ^ 2` / 2 | inconclusive | -1.563 | 92.915–7277.221 | — | within upper bound (observed faster) |
| `height16HalfOption` | `n ^ 2` / 2 | inconclusive | -1.549 | 94.359–7370.681 | — | within upper bound (observed faster) |
| `height16HalfInverse` | `n ^ 2` / 2 | inconclusive | -1.551 | 82.585–6294.965 | — | within upper bound (observed faster) |
| `height16DeficientErrorSolve` | `n ^ 2` / 2 | inconclusive | -1.492 | 248.977–15326.808 | — | within upper bound (observed faster) |
| `height16DeficientErrorOption` | `n ^ 2` / 2 | inconclusive | -1.496 | 248.630–15546.633 | — | within upper bound (observed faster) |
| `height16HalfErrorSolve` | `n ^ 2` / 2 | inconclusive | -1.538 | 92.704–6740.270 | — | within upper bound (observed faster) |
| `height16HalfErrorOption` | `n ^ 2` / 2 | inconclusive | -1.536 | 92.840–6766.311 | — | within upper bound (observed faster) |
| `height16TallSolve` | `n ^ 2` / 2 | inconclusive | -1.560 | 508.267–38417.999 | — | within upper bound (observed faster) |
| `height16TallOption` | `n ^ 2` / 2 | inconclusive | -1.559 | 509.616–38544.522 | — | within upper bound (observed faster) |
| `height16WideSolve` | `n ^ 2` / 2 | inconclusive | -1.494 | 426.033–26654.007 | — | within upper bound (observed faster) |
| `height16WideOption` | `n ^ 2` / 2 | inconclusive | -1.495 | 423.708–26551.454 | — | within upper bound (observed faster) |
