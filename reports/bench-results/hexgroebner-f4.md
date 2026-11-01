# Portable prime-field F4 candidate measurements

These measurements cover deterministic F4 candidate production and monomial
interning with Lean `v4.35.0-rc3` on the shared `chungus2` host (AMD EPYC 9455).
Every run uses one automatically leased logical CPU. Host load, affinity,
binary hashes, commands, source manifests and every completed sample are
retained beside the exports. No result establishes performance leadership.

## Monomial interning

The registration inserts distinct three-variable monomials, widening exponents
from one to two bytes at 256, and hashes the complete logical exponent and
metadata buffers. Stable identifiers and exact collision comparisons are part
of the operation. Expected work is amortized linear at fixed arity.

| Number of monomials | Median at `27be9af894a3` | Median at `54ad046fe11c` |
| ---: | ---: | ---: |
| 2,048 | 5.306 ms | 0.588 ms |
| 4,096 | 18.257 ms | 1.207 ms |
| 8,192 | 77.312 ms | 2.502 ms |
| 16,384 | 796.495 ms | 5.228 ms |
| 32,768 | 5,404.259 ms | 10.726 ms |

The two sweeps use different source and sampling configurations. They are
**separate complexity observations**, not adjacent AB/BA estimates of a speedup.
The earlier sweep has normalized slope `β = +1.799`, triggering investigation.
A diagnostic profile at 32,768 monomials attributes 48.86% of samples to Lean
object destruction, 42.49% to array copying/expansion, and 6.66% to `memmove`.
Generated C retained the previous table to service the caller's error branch;
this forced copy-on-write for each insertion. The ownership-preserving API
returns the table on both success and failure, and callers install it before
examining the status. This removes the retained rollback alias while preserving
charged failure work and stable identifiers. The profile used CPU 95 at 199 Hz,
with 1,131 samples and no lost samples. Kernel symbols were restricted; this
attribution concerns resolved user-space symbols.

The `54ad046fe11c` sweep has verdict **consistent with declared complexity**,
`β = +0.052`. It uses three fixed trial-major outer trials, with a four-second
inner calibration target. All 15 completed samples are retained; three leading
samples are marked by the harness's declared warmup trimming. The per-spawn
floor is 22.511 ms. Within-size spread is 0.030%–1.925%, and observed process
RSS is 66,660–75,688 KiB. The output hashes match the earlier implementation at
every size. The intervening `0c15209abaec` sweep retains another 15 samples;
its 500 ms target left every sample below the signal floor, so its verdict is
inconclusive. The longer target addresses that measurement-resolution issue.

Retained evidence:

- Initial [samples](hexgroebner-intern-27be9af894a3.json),
  [manifest](hexgroebner-intern-27be9af894a3.manifest),
  [metadata](hexgroebner-intern-27be9af894a3.measurement.json),
  [output](hexgroebner-intern-27be9af894a3.log),
  [profile output](hexgroebner-intern-27be9af894a3.profile.log) and
  [resolved profile](hexgroebner-intern-27be9af894a3.perf.txt).
- Short-target [samples](hexgroebner-intern-0c15209abaec.json),
  [manifest](hexgroebner-intern-0c15209abaec.manifest),
  [metadata](hexgroebner-intern-0c15209abaec.measurement.json) and
  [output](hexgroebner-intern-0c15209abaec.log).
- Longer-target [samples](hexgroebner-intern-54ad046fe11c.json),
  [manifest](hexgroebner-intern-54ad046fe11c.manifest),
  [metadata](hexgroebner-intern-54ad046fe11c.measurement.json) and
  [output](hexgroebner-intern-54ad046fe11c.log).

## Full F4 calls

Source fingerprint `68b53125ffac` includes the reusable measurement driver
`scripts/bench/groebner_measure.py`. The field is the prime field with modulus
65,537; the order is grevlex with the written variable precedence. Inputs are
standard cyclic and Katsura generators, with no field equations. Timings
include canonical input normalization, symbolic preprocessing, matrix calls,
pair processing, final interreduction, interchange decoding and full structural
output hashing. Input generation, certificate generation, independent native
verification and kernel checking are excluded. This interface returns an
explicitly **unchecked candidate**. IO-backed inputs prevent caching the pure
fixed computation.

| System | Median | Min–max | Process RSS | Output hash |
| --- | ---: | ---: | ---: | --- |
| cyclic-4 | 0.425 ms | 0.422–0.426 ms | 67,768–67,772 KiB | `12a8682b6bd4535b` |
| cyclic-5 | 10.600 ms | 10.572–10.632 ms | 67,764–67,768 KiB | `b052d1d60890c253` |
| Katsura-3 | 0.542 ms | 0.537–0.547 ms | 67,764 KiB | `97aae8dcaec9e6c0` |

Each fixed registration retains five repetitions, with automatic inner repeats
where needed. All repetitions succeeded and hashes agree within each case.
These are small descriptive baseline cases; short calls have correspondingly
limited timing resolution. The independent conformance corpus compares 567
smaller systems across seven primes and three orders against SymPy F5B; the
benchmark hashes alone are not independent proofs of correctness.

- cyclic-4 [samples](hexgroebner-cyclic4-68b53125ffac.json),
  [manifest](hexgroebner-cyclic4-68b53125ffac.manifest),
  [metadata](hexgroebner-cyclic4-68b53125ffac.measurement.json),
  [output](hexgroebner-cyclic4-68b53125ffac.log).
- cyclic-5 [samples](hexgroebner-cyclic5-68b53125ffac.json),
  [manifest](hexgroebner-cyclic5-68b53125ffac.manifest),
  [metadata](hexgroebner-cyclic5-68b53125ffac.measurement.json),
  [output](hexgroebner-cyclic5-68b53125ffac.log).
- Katsura-3 [samples](hexgroebner-katsura3-68b53125ffac.json),
  [manifest](hexgroebner-katsura3-68b53125ffac.manifest),
  [metadata](hexgroebner-katsura3-68b53125ffac.measurement.json),
  [output](hexgroebner-katsura3-68b53125ffac.log).

No matched external comparator or parallel sweep has been collected. These
measurements do not establish a fastest-open-source result or a language
barrier. The demonstrated interning cost was resolved by ownership changes
within Lean. Native arithmetic, packed monomial batches, mixed elimination,
SIMD and multithreading remain available optimization routes. The wider field,
certificate and theory requirements of
[#10987](https://github.com/kim-em/hex-dev/issues/10987) remain outstanding.
