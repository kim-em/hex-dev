# Quotient witness verdicts

The linked exports retain every point. Mode-2 faster results translate the harness’s `inconclusive` result using the declared one-sided bound; they are not two-sided passes. The original resolution failures remain in their original directories.

| Case | Mode | Declared model | β | Eligible rungs | Result |
| --- | ---: | --- | ---: | ---: | --- |
| [`Quotient.produceFull`](quotient-large/produceFull/produceFull.json) | 1 | `n * n * n` | +0.121 | 7 | consistent |
| [`Quotient.prepareFull`](quotient-large/prepareFull/prepareFull.json) | 1 | `n * n * n` | +0.075 | 7 | consistent |
| [`Quotient.finishFull`](quotient-large/finishFull/finishFull.json) | 1 | `n * n * n` | +0.062 | 7 | consistent |
| [`Quotient.checkFull`](quotient-large/checkFull/checkFull.json) | 1 | `n * n * n` | +0.550 | 7 | inconclusive |
| [`Quotient.produceDeficient`](quotient-large/produceDeficient/produceDeficient.json) | 1 | `n * n * n` | -0.097 | 7 | consistent |
| [`Quotient.prepareDeficient`](quotient-large/prepareDeficient/prepareDeficient.json) | 1 | `n * n * n` | -0.056 | 7 | consistent |
| [`Quotient.finishDeficient`](quotient-large/finishDeficient/finishDeficient.json) | 1 | `n * n * n` | -0.050 | 7 | consistent |
| [`Quotient.checkDeficient`](quotient-large/checkDeficient/checkDeficient.json) | 1 | `n * n * n` | -0.038 | 7 | consistent |
