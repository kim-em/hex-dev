# Integer verdicts

The linked exports retain every point. Mode-2 faster results translate the harness’s `inconclusive` result using the declared one-sided bound; they are not two-sided passes. The original resolution failures remain in their original directories.

| Case | Mode | Declared model | β | Eligible rungs | Result |
| --- | ---: | --- | ---: | ---: | --- |
| [`runRowReduceDense`](integer/runRowReduceDense.json) | 2 | `hadamardBound n` | -2.002 | 7 | within upper bound (observed faster) |
| [`runRankCertDense`](integer/runRankCertDense.json) | 2 | `hadamardBound n` | -1.988 | 9 | within upper bound (observed faster) |
| [`runCheckRankDense`](integer/runCheckRankDense.json) | 2 | `hadamardBound n` | -2.166 | 7 | within upper bound (observed faster) |
| [`runRowReduceLowRank2At64`](integer/runRowReduceLowRank2At64.json) | 1 | `n * n` | +0.037 | 9 | consistent |
| [`runRankCertLowRank2At64`](integer/runRankCertLowRank2At64.json) | 1 | `n * n` | +0.040 | 9 | consistent |
| [`runCheckRankLowRank2At64`](integer/runCheckRankLowRank2At64.json) | 1 | `n * n` | -0.024 | 9 | consistent |
| [`runRowReduceLowRank8At64`](integer/runRowReduceLowRank8At64.json) | 1 | `n * n` | +0.095 | 9 | consistent |
| [`runRankCertLowRank8At64`](integer/runRankCertLowRank8At64.json) | 1 | `n * n` | +0.042 | 9 | consistent |
| [`runCheckRankLowRank8At64`](integer/runCheckRankLowRank8At64.json) | 1 | `n * n` | -0.074 | 9 | consistent |
| [`runRowReduceLowRank2At1024`](integer/runRowReduceLowRank2At1024.json) | 1 | `n * n` | +0.051 | 9 | consistent |
| [`runRankCertLowRank2At1024`](integer/runRankCertLowRank2At1024.json) | 1 | `n * n` | +0.053 | 9 | consistent |
| [`runCheckRankLowRank2At1024`](checker-resolution/runCheckRankLowRank2At1024.json) | 1 | `n * n` | +0.012 | 9 | consistent |
| [`runRowReduceLowRank8At1024`](integer/runRowReduceLowRank8At1024.json) | 1 | `n * n` | +0.098 | 8 | consistent |
| [`runRankCertLowRank8At1024`](integer/runRankCertLowRank8At1024.json) | 1 | `n * n` | +0.078 | 9 | consistent |
| [`runCheckRankLowRank8At1024`](integer/runCheckRankLowRank8At1024.json) | 1 | `n * n` | — | 3 | consistent |
| [`runRowReduceDeficientMinusOne`](integer/runRowReduceDeficientMinusOne.json) | 2 | `productBound n` | -1.956 | 9 | within upper bound (observed faster) |
| [`runRankCertDeficientMinusOne`](integer/runRankCertDeficientMinusOne.json) | 2 | `productBound n` | -1.842 | 9 | within upper bound (observed faster) |
| [`runCheckRankDeficientMinusOne`](integer/runCheckRankDeficientMinusOne.json) | 2 | `productBound n` | -2.124 | 9 | within upper bound (observed faster) |
| [`runRowReduceDeficientHalf`](integer/runRowReduceDeficientHalf.json) | 2 | `productBound n` | -1.952 | 9 | within upper bound (observed faster) |
| [`runRankCertDeficientHalf`](integer/runRankCertDeficientHalf.json) | 2 | `productBound n` | -1.998 | 9 | within upper bound (observed faster) |
| [`runCheckRankDeficientHalf`](integer/runCheckRankDeficientHalf.json) | 2 | `productBound n` | -2.274 | 8 | within upper bound (observed faster) |
| [`runRowReduceDeficientHalfShifted`](integer/runRowReduceDeficientHalfShifted.json) | 2 | `productBound n` | -2.093 | 4 | within upper bound (observed faster) |
| [`runRankCertDeficientHalfShifted`](shifted-resolution/runRankCertDeficientHalfShifted.json) | 2 | `productBound n` | -2.065 | 9 | within upper bound (observed faster) |
| [`runCheckRankDeficientHalfShifted`](integer/runCheckRankDeficientHalfShifted.json) | 2 | `productBound n` | -2.343 | 8 | within upper bound (observed faster) |
| [`Second.dense`](attribution/SecondDense.json) | 2 | `hadamardBound n` | -1.986 | 9 | within upper bound (observed faster) |
| [`Certify.dense`](attribution/CertifyDense.json) | 2 | `hadamardBound n` | -2.045 | 9 | within upper bound (observed faster) |
| [`Witness.dense`](attribution/WitnessDense.json) | 2 | `hadamardBound n` | -1.940 | 9 | within upper bound (observed faster) |
| [`Second.lowRank2At64`](attribution/SecondLowRank2At64.json) | 1 | `1` | -0.001 | 9 | consistent |
| [`Certify.lowRank2At64`](attribution/CertifyLowRank2At64.json) | 1 | `n * n` | +0.022 | 9 | consistent |
| [`Witness.lowRank2At64`](attribution/WitnessLowRank2At64.json) | 1 | `n * n` | +0.031 | 9 | consistent |
| [`Second.lowRank8At64`](attribution/SecondLowRank8At64.json) | 1 | `1` | +0.005 | 9 | consistent |
| [`Certify.lowRank8At64`](attribution/CertifyLowRank8At64.json) | 1 | `n * n` | +0.004 | 9 | consistent |
| [`Witness.lowRank8At64`](attribution/WitnessLowRank8At64.json) | 1 | `n * n` | +0.050 | 9 | consistent |
| [`Second.lowRank2At1024`](attribution/SecondLowRank2At1024.json) | 1 | `1` | -0.003 | 9 | consistent |
| [`Certify.lowRank2At1024`](certify-resolution/CertifyLowRank2At1024.json) | 1 | `n * n` | -0.002 | 9 | consistent |
| [`Witness.lowRank2At1024`](witness-resolution/WitnessLowRank2At1024.json) | 1 | `n * n` | +0.043 | 9 | consistent |
| [`Second.lowRank8At1024`](attribution/SecondLowRank8At1024.json) | 1 | `1` | +0.004 | 9 | consistent |
| [`Certify.lowRank8At1024`](attribution/CertifyLowRank8At1024.json) | 1 | `n * n` | +0.054 | 9 | consistent |
| [`Witness.lowRank8At1024`](attribution/WitnessLowRank8At1024.json) | 1 | `n * n` | +0.109 | 9 | consistent |
| [`Second.deficientMinusOne`](second-resolution/SecondDeficientMinusOne.json) | 2 | `productBound n` | -1.772 | 9 | within upper bound (observed faster) |
| [`Certify.deficientMinusOne`](attribution/CertifyDeficientMinusOne.json) | 2 | `productBound n` | -1.789 | 8 | within upper bound (observed faster) |
| [`Witness.deficientMinusOne`](attribution/WitnessDeficientMinusOne.json) | 2 | `productBound n` | -1.843 | 9 | within upper bound (observed faster) |
| [`Second.deficientHalf`](attribution/SecondDeficientHalf.json) | 2 | `productBound n` | -2.006 | 9 | within upper bound (observed faster) |
| [`Certify.deficientHalf`](half-certify-resolution/CertifyDeficientHalf.json) | 2 | `productBound n` | -2.092 | 9 | within upper bound (observed faster) |
| [`Witness.deficientHalf`](attribution/WitnessDeficientHalf.json) | 2 | `productBound n` | -2.070 | 9 | within upper bound (observed faster) |
| [`Second.deficientHalfShifted`](attribution/SecondDeficientHalfShifted.json) | 2 | `productBound n` | -2.046 | 9 | within upper bound (observed faster) |
| [`Certify.deficientHalfShifted`](attribution/CertifyDeficientHalfShifted.json) | 2 | `productBound n` | -2.165 | 9 | within upper bound (observed faster) |
| [`Witness.deficientHalfShifted`](attribution/WitnessDeficientHalfShifted.json) | 2 | `productBound n` | -2.126 | 9 | within upper bound (observed faster) |
