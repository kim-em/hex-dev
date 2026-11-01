# Exact row-arithmetic specialization

Source `cbca23e34e93` specializes the scalar row kernel in two ways. For 8/16-bit
residues, `factor*b < 2^32`, so the reciprocal `floor(2^32/p)` suffices and its
product fits in uint64. Four-byte residues retain the uint128 Barrett path.
The exact-remainder fallback remains available. No separate speed benefit is
established for the narrow reciprocal specialization by these measurements.

After product reduction, `a` and `product` are canonical and below `2^31`.
Their uint64 difference has its top bit set exactly when subtraction wrapped.
Adding `p` under that mask gives the canonical difference without an
unpredictable conditional correction. Geometry, canonical-input rejection,
ownership, aliasing, coefficient widths, resource counters and the transparent
Lean body are unchanged. No floating point or ISA extension is used.

## Candidate-only lean-bench comparison

Baseline source `7f850171b281`; one leased CPU (64), one computation thread,
adjacent AB then BA blocks per input, three retained samples per arm/block.
Both binaries use `p = 65537`, grevlex, cap 1024, native monomials, shared final
reductions and identical allowances. Input generation is excluded;
normalization through interreduction, decoding and full basis hashing are
included. Certification, independent verification and kernel checking are
excluded. Every completed sample is retained; no unchanged rerun was used.

| Case | AB median A → B | BA median A → B | Geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-5 | 3.613 → 3.535 ms | 3.618 → 3.525 ms | 0.976 |
| cyclic-6 | 29.940 → 27.288 ms | 29.901 → 27.295 ms | 0.912 |
| Katsura-3 | 0.314 → 0.312 ms | 0.314 → 0.312 ms | 0.992 |
| Reimer-5 | 155.735 → 134.690 ms | 155.460 → 134.668 ms | 0.866 |

All 48 samples succeed and each paired full basis hash agrees. The small
Katsura result is close to unchanged; the larger cyclic-6 and Reimer cases
improve by about 9% and 13%. This benchmark uses four-byte residues, so it
never exercises the new 32-bit reciprocal path. The arithmetic change measured
on this route is the unsigned subtraction correction mask.

[Raw samples and logs](hexgroebner-row-arithmetic-cbca23e34e93.tar.gz),
[commands and host context](hexgroebner-row-arithmetic-cbca23e34e93.measurement.json),
[analysis](hexgroebner-row-arithmetic-cbca23e34e93.analysis.json),
[manifest](hexgroebner-row-arithmetic-cbca23e34e93.manifest) and
[exact measured source](hexgroebner-row-arithmetic-sources-cbca23e34e93.tar.gz)
are retained. Raw archive SHA256:
`d7153ce3fa2c599ddb0dd4df3d6b10aa1678558c4c319eebaf3d772558439042`.

## Frozen whole-process diagnostic comparison

The unchanged 16-input suite was compared on leased CPU 74 with the same
adjacent AB/BA schedule, one computation thread, 16 GiB address-space limit
and 64 MiB output limit. All 64 samples succeed; every coefficient and exponent
of all 32 paired full bases agrees. Internal candidate time, whole-process time
and memory are retained separately. Whole-process Eco10 improves by about 35%
at both field widths; Reimer-5 improves by about 11–12%. Similar Eco10 gains
on the unchanged four-byte reciprocal route support the mask as the main
measured improvement; the two-byte reciprocal effect was not isolated.
Several small cases regress by 2–6% in whole-process time, and MinRank also
regresses by about 4–5% internally. Noncandidate setup, parsing, field validation
and output costs dominate several small inputs, so internal gains can coexist
with whole-process losses. All inputs and both timing contracts are listed
below. This experiment compares only the two Hex binaries; msolve was not rerun.

| Input | Internal candidate B/A | Whole-process B/A |
| --- | ---: | ---: |
| cyclic5-15 | 0.969 | 0.997 |
| cyclic5-31 | 0.978 | 1.033 |
| cyclic6-15 | 0.906 | 0.967 |
| cyclic6-31 | 0.904 | 0.967 |
| kat6-15 | 0.931 | 1.026 |
| kat6-31 | 0.930 | 1.026 |
| eco10-15 | 0.645 | 0.656 |
| eco10-31 | 0.643 | 0.655 |
| noon4-15 | 0.999 | 1.052 |
| noon4-31 | 0.994 | 1.042 |
| reimer5-15 | 0.866 | 0.890 |
| reimer5-31 | 0.856 | 0.883 |
| minrank_d_2_p_2_q_3_r_2-15 | 1.048 | 1.056 |
| minrank_d_2_p_2_q_3_r_2-31 | 1.040 | 1.040 |
| quadratic5-32003 | 0.909 | 1.020 |
| quadratic5-2147483647 | 0.906 | 1.023 |

The [metadata](hexgroebner-row-arithmetic-diagnostic-cbca23e34e93.json) and
[raw records](hexgroebner-row-arithmetic-diagnostic-cbca23e34e93.tar.gz) retain
all inputs, outputs, exact driver, source manifest, scripts, samples and host
observations. Archive SHA256:
`28e6bd2b40c441501c0dfddb17de2f993b6b31f1fcce92f715f4efc5d9788d60`.

These fixed diagnostic observations are not the balanced acceptance suite or
held-out data and make no leadership claim. Full basis certification, wider
finite-field adapters and the remaining performance gap remain open.

The measured source archives preserve the exact historical inputs. Current
sources additionally contain the shared checked monomial append and matrix
peak telemetry from the batch comparison, arithmetic boundary tests (including the exhaustive maximal two-byte-factor
sweep) and the independent certificate checker. Those additions are not included in this
timing attribution.
