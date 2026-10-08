# Current scalar readiness observations

This focused refresh measures the existing `runAdd2/4/8` and `runSqrt2/4/8`
registrations after direct selected-root certification. It answers whether the
old seconds-scale square-root observation still describes the shipped path;
no external campaign or unrelated operation was rerun.

The positive operand is the real root of `X^d−2`. The callback computes `a+1`
or the principal square root, then checks the complete canonical polynomial
and positive sign. The output degree of square root is 2d. Operands are prepared
outside timing; no independently constructed expected nonrational result is
prepared. Warmup is excluded; result guards remain timed. The same API has
ordinary-kernel correspondence and current panic-rejecting verification.

Four fixed trial-major rounds cover all six cases on one automatically leased
CPU, with one fixed 50 ms minimum batch per observation. The retained
collector metadata’s generic boundary suffix mentions adjacent external arms;
this native-only run has none, as its command and enumerated 24 arms show.
Future metadata uses the corrected native-only boundary wording. All 24 observations
complete with matching expected hashes; no cap, discarded point, quiet-host
preflight or unchanged rerun occurs. Host activity is recorded context.
`analysis.json` divides each batch by its actual inner count. Whole-child peak
RSS includes preparation, warmup, startup and the native runtime; it is not
operation allocation or live-heap memory.

| Operation | Operand degree | Median ms | Observed range ms | Median whole-child RSS MiB |
| --- | ---: | ---: | ---: | ---: |
| Add one | 2 | 0.486 | 0.484–0.488 | 67.4 |
| Add one | 4 | 4.552 | 4.536–4.602 | 67.6 |
| Add one | 8 | 157.559 | 157.021–158.158 | 67.7 |
| Square root | 2 | 9.892 | 9.884–9.956 | 67.4 |
| Square root | 4 | 134.453 | 133.465–135.277 | 67.7 |
| Square root | 8 | 5636.850 | 5564.132–5697.971 | 68.0 |

[SVG](comparison.svg), [PNG](comparison.png) and [PDF](comparison.pdf) show
all native dots and min–max ranges against the retained historical FLINT/Z3
references. Their source and operation boundaries differ: external
annihilation/sign guards, transport and cleanup remain timed. These are not
contemporaneous adjacent arms, a controlled speedup or isolated primitive
rankings. No timing exponent or portable budget is fitted.

This supports practical small-degree calls and bounded larger scalar calls
with explicit latency limits. Degree-eight square root remains a seconds-scale
canonical operation. It is not a good repeated interactive hot path. Its source
performs eliminant/presentation construction, precision-bounded root selection,
factorization and canonical exactification; direct certification avoids the
initial global selection when it succeeds, but canonical output construction
still inherits NumberField costs. The older isolation profiles explain older
implementations and do not assign current percentage shares. There is no
unexpected newly introduced cost, explicit external speed target or blanket
promise of low latency for arbitrary canonical degrees. The readiness decision
accepts this documented cost rather than excluding degree eight or inventing a
new speed budget. Larger degrees/heights require their own practical assessment.

The clean source is `84618250b2812a477f8948427e5c2023cc3ff597`, retained on
`evidence/issue-10577-current-scalar`. Metadata retains the exact commands,
binary SHA, relevant source snapshots, toolchain/pins, CPU and host context.
The [source-cone comparison](source-cone.json) shows all 304 local compiled
modules unchanged from the latest root-enumeration source. The binary was built
and panic-verified on that same computational source before these documentation
and collector-option commits. Its frozen copy remains in persistent storage
as indexed by [persistent-retention.json](persistent-retention.json).

Reproduce from the recorded source, using a fresh output directory:

```sh
lake build hexrealalgebraic_bench
python3 scripts/bench/real_algebraic_scaling_comparison.py \
  --operations Add Sqrt --native-only --output /path/to/new-captures
```

Run `python3 reports/bench-results/real-algebraic-current-scalar/plot.py.txt`
in the configured plotting environment to regenerate the analysis and plots
from the committed observations and historical external references.
