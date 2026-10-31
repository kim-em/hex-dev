# Flat matrix scan state

Source `d42e621f1253` carries the seven mutable column-scan values in one
structure. The former generated C unpacked and rebuilt nested tuples at each
iteration. This changes representation of local loop state; arithmetic, matrix
sequence, provenance and operational counters are unchanged.

## Candidate-only lean-bench comparison

Baseline source `723cb50d1fa0`; leased CPU 65, one computation thread, adjacent
AB then BA blocks per input, three retained samples per arm/block. Both binaries
use p = 65537, grevlex, cap 1024, native monomials and shared final reductions
under identical allowances. Input generation, certification and kernel checking
are excluded. Every completed sample is retained; no unchanged rerun was used.

| Case | AB median A → B | BA median A → B | Geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-5 | 3.627 → 3.401 ms | 3.497 → 3.438 ms | 0.960 |
| cyclic-6 | 26.850 → 26.134 ms | 27.087 → 25.787 ms | 0.963 |
| Katsura-3 | 0.314 → 0.304 ms | 0.314 → 0.313 ms | 0.981 |
| Reimer-5 | 131.690 → 126.834 ms | 129.434 → 128.282 ms | 0.977 |

All 48 samples succeed with matching paired basis hashes. These are small
observed gains, particularly for Katsura and Reimer, rather than a large
elimination speedup.

[Raw samples and logs](hexgroebner-flat-scan-d42e621f1253.tar.gz),
[commands and context](hexgroebner-flat-scan-d42e621f1253.measurement.json),
[analysis](hexgroebner-flat-scan-d42e621f1253.analysis.json),
[manifest](hexgroebner-flat-scan-d42e621f1253.manifest),
[measured source](hexgroebner-flat-scan-sources-d42e621f1253.tar.gz) and
[baseline source](hexgroebner-flat-scan-baseline-723cb50d1fa0.tar.gz) are retained.
Raw archive SHA256:
`79bf689c6b1271b84776c5b3fadea5dfc4c657966b870e3a9b84c652fa9f1e44`.

## Whole-process diagnostic comparison

The unchanged 16-input frozen suite uses leased CPU 90, one computation thread,
adjacent AB/BA comparisons, a 10-second timeout, 16 GiB address-space limit and
64 MiB output limit. All 64 samples succeed and all 32 paired full bases match.
Whole-process observations vary substantially between adjacent arms and blocks,
including regressions. No general whole-process speedup is established.
Maximum observed RSS is 88,496 KiB for A and 90,384 KiB for B. Per-input memory,
all failures and complete outputs are retained in the records.

| Input | Internal candidate B/A | Whole-process B/A |
| --- | ---: | ---: |
| cyclic5-15 | 0.998 | 1.186 |
| cyclic5-31 | 0.982 | 0.940 |
| cyclic6-15 | 0.812 | 0.673 |
| cyclic6-31 | 0.862 | 0.979 |
| kat6-15 | 0.729 | 0.851 |
| kat6-31 | 0.979 | 0.843 |
| eco10-15 | 0.851 | 0.857 |
| eco10-31 | 0.994 | 1.018 |
| noon4-15 | 0.937 | 1.064 |
| noon4-31 | 0.999 | 0.675 |
| reimer5-15 | 0.857 | 0.938 |
| reimer5-31 | 0.997 | 1.096 |
| minrank_d_2_p_2_q_3_r_2-15 | 1.123 | 1.291 |
| minrank_d_2_p_2_q_3_r_2-31 | 0.992 | 0.803 |
| quadratic5-32003 | 0.968 | 0.717 |
| quadratic5-2147483647 | 0.920 | 1.167 |

[Metadata and per-input summary](hexgroebner-flat-scan-diagnostic-d42e621f1253.json)
and [raw records](hexgroebner-flat-scan-diagnostic-d42e621f1253.tar.gz) retain
all samples, inputs, outputs, source manifest and exact driver. The two arms
have separate retained binary hashes. The summary metadata states that contract
explicitly; the raw archive preserves the original metadata and its script.
Diagnostic archive SHA256:
`a3157fbdd8195dce7506e275d1c7780d836f1d334691b307477fb33d153a7e22`.

These observations compare two Hex candidates, without a fresh external
comparator. They are not the balanced acceptance suite or held-out inputs and
make no leadership claim. Complete checked-call timings and the existing gap
to faster open-source engines remain outstanding.
