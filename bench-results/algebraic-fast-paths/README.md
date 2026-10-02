# Algebraic comparison and radical fast paths

Stored intervals substantially reduce work on separated values. The same-imaginary case still needs exact subtraction and pays for two inconclusive refinement rounds: its median increased by about 9% in this sample. All figures are observations on the recorded shared host, including loop and checksum overhead; they are not portable latency bounds.

| Case | Reference, µs/call | New, µs/call | Reference / new |
|---|---:|---:|---:|
| real-separated | 78.535 | 1.115 | 70.40 |
| real-equal | 0.316 | 0.308 | 1.02 |
| imag-separated | 10835.168 | 1.221 | 8876.11 |
| same-imaginary | 4037.493 | 4411.526 | 0.92 |
| cube-negative/selection | 21843.238 | 2663.264 | 8.20 |
| cube-negative/complete | 29327.694 | 10315.936 | 2.84 |
| unity-eighth/selection | 1981821.928 | 10966.548 | 180.72 |
| unity-eighth/complete | 1545769.055 | 15565.326 | 99.31 |

Build with `lake build hexnumberfield_bench` and run `.lake/build/bin/hexnumberfield_bench algebraic-fast-compare` on an automatically selected CPU. `metadata.json` records placement, host load, toolchain, base revision, measurement source revision and source hashes; `samples.jsonl` retains every completed observation. There was no rerun or sample exclusion.

Each case has eight adjacent blocks, alternating reference/new and new/reference. Both arms use 64 calls per comparison block or two per selection/extraction block. Inputs are preconstructed, and operands or enumeration order alternate within a block. Construction is recorded separately. The driver checks exact agreement before measurement. The old real comparison always uses the product separation precision. The old complex comparison uses exact subtraction when its cheap equality/reality/side tests cannot decide. The selection reference canonicalizes all candidates and computes their real coordinates; it shares the current real comparator with the new selector. These compare operation strategies on the same representation, not two historical executables.

The negative-cube case measures the principal cube root of −8. The eighth-root case measures the fourth root of −1. Selection timings share a precomputed generic root list, so they isolate lazy selection and winner exactification. Complete timings include root construction: the new eighth-root case additionally uses the integer-binomial unity shortcut. The generic reference retains its exact selector. No claim of a general radical speedup is inferred from these two inputs.

Source inspection supplies the algorithmic distinction: a successful stored comparison performs no polynomial multiplication, exact subtraction, or exactification. Lazy selection checks one representative per candidate, caches each refinement, and exactifies only its selected winner. The bounded fallback retains correctness for inconclusive intervals. The direct radical solver and cyclotomic degree reduction remain design work in [issue #10147](https://github.com/kim-em/hex-dev/issues/10147).
