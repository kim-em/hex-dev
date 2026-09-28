# Explicit SQUFOF factorization examples

`Hex.Nat.factor?` and `factorPartial?` accept an explicit
`squfof := .first limits` or `.rescue limits` policy. The default is `.off`.
The policy applies to recursive cofactors and nested certificate work. The
existing structural reductions and composite filters precede the splitter;
failed bounded SQUFOF attempts leave the existing fallbacks available.

These measurements support two selected manual examples. They do not establish
a general portfolio improvement or justify automatic dispatch. The
[raw primitive evidence](hex-primality-squfof.md) covers the varied-gap ladder
and controls; its default-promotion requirements still apply.

## Protocol and retained data

The Mathlib-free `hexintfactor_bench squfof-factor` command times the complete
counted factorization, including certificate construction and checked
acceptance. Runtime arguments pass through an `IO.Ref` to prevent evaluation
before the timed region. Diagnostics and JSON serialization follow the timer.

The [collector](../scripts/bench/squfof_dispatch.py) runs eight trial-major
trials of seven inputs. Each trial runs adjacent `.off`/`.first` arms, reversing
their order on alternate trials. There is no warmup or sample rejection. An
automatic CPU lease pins both arms to CPU 63 on the shared host `chungus2`.
Start/end host load, executable and source hashes, commands, stdout, stderr,
timings, counters, final random states, factors and ordered route diagnostics
are retained in the [raw samples](bench-results/hex-int-factor-squfof-examples.jsonl).
The source was an uncommitted tree based on `d0a18e640`; the recorded source
hashes identify the measured implementation.

All 112 processes completed. Every nonzero input produced a complete checked
factorization in both arms, and zero produced the expected `FactorStop.zero`.
The collector independently checks products, canonical prime powers, and each
reported SQUFOF divisor by integer division. The 300-second process timeout is
an operational safeguard; no process reached it.

Both arms use seed `n`, queue capacity 128, default primality and rho budgets,
stage 2 disabled, and `factorFuel = 4 * floor(log2(n)) + 32` (32 for zero).
SQUFOF limits are per invocation, including nested work; they are not a single
total budget for the factorization.

| Case | Input | Prime factors | Factor fuel | Multiplier cap | Step cap |
| --- | ---: | --- | ---: | ---: | ---: |
| balanced 56-bit | 40249308338448479 | 184185251 × 218526229 | 252 | 2 | 65536 |
| close 64-bit | 16212959431627901207 | 4026531853 × 4026532019 | 284 | 1 | 128 |
| trace table control | 22117019 | 4451 × 4969 | 128 | 1 | 25 |
| table control | 9797 | 97 × 101 | 84 | 2 | 65536 |
| prime control | 100003 | 100003 | 96 | 2 | 65536 |
| square control | 18446744030759878681 | 4294967291² | 284 | 2 | 65536 |
| zero control | 0 | none | 32 | 2 | 65536 |

## Observations

Times are medians with the full observed minimum–maximum range, in milliseconds.
Attempt counts include recursive splits and certificate searches.

| Case | Off: median [range] | First: median [range] | Off/first median ratio | Attempts off/first |
| --- | --- | --- | ---: | ---: |
| balanced 56-bit | 8.709 [8.657–8.863] | 1.402 [1.356–1.440] | 6.21 | 20 / 17 |
| close 64-bit | 20.688 [20.387–21.018] | 2.250 [2.232–2.300] | 9.19 | 22 / 24 |
| trace table control | 0.0965 [0.0941–0.1037] | 0.0982 [0.0960–0.1029] | 0.98 | 0 / 0 |
| table control | 0.0813 [0.0777–0.0870] | 0.0797 [0.0773–0.0828] | 1.02 | 0 / 0 |
| prime control | 0.6503 [0.6259–0.7068] | 0.6443 [0.6215–0.7202] | 1.01 | 4 / 4 |
| square control | 1.324 [1.312–1.339] | 1.327 [1.292–1.342] | 1.00 | 10 / 10 |
| zero control | 0.00084 [0.00074–0.00094] | 0.00089 [0.00079–0.00114] | 0.94 | 0 / 0 |

The balanced example has factors differing by about 19%; its first SQUFOF call
finds `184185251` in one multiplier attempt and 2548 steps. The close example
is deliberately favorable: its first call finds `4026531853` in one attempt
and two steps. Their adjacent paired speedup ranges are 6.01–6.53 and
9.07–9.33 respectively. These are host-specific observations on selected
inputs. The controls show no material speedup: the table, prime and square
routes already avoid splitting their original subjects.

SQUFOF itself leaves the random state unchanged. A successful early split
skips rho's random draws, so later certificate searches can take a different
trajectory. This explains why the close example improves in time while its
total attempt count increases. Attempt count alone does not measure cost.

The `22117019` input is an API/conformance example for the raw 25-step trace.
Complete factorization already uses the small-prime table for this input;
it is not a complete-factorization speedup example. `.rescue` placement and
exhaustion accounting are covered by conformance assertions, not timing claims
in this selected `.first` comparison.

## Reproduction

```sh
lake build hexintfactor_bench
python3 scripts/bench/squfof_dispatch.py --output /tmp/squfof-examples-new.jsonl
```

The collector refuses to overwrite an existing file. The compiled probe can
also reproduce individual arms:

```sh
.lake/build/bin/hexintfactor_bench squfof-factor 40249308338448479 off 2 65536 128 40249308338448479 252
.lake/build/bin/hexintfactor_bench squfof-factor 40249308338448479 first 2 65536 128 40249308338448479 252
```

The manual presents these as explicit options for users who know their input
family. Bit length alone does not establish balanced factors or make a bounded
SQUFOF attempt profitable; the default portfolio and tactic allocations remain
unchanged.
