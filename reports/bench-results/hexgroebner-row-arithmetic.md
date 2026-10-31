# Exact row-arithmetic specialization

Source `cbca23e34e93` specializes the scalar row kernel in two ways. For 8/16-bit
residues, `factor*b < 2^32`, so the reciprocal `floor(2^32/p)` suffices and its
product fits in uint64. Four-byte residues retain the uint128 Barrett path.
The exact-remainder fallback remains available.

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
improve by about 9% and 13%.

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
at both field widths; Reimer-5 improves by about 11–12%. This experiment compares
only the two Hex binaries; msolve was not rerun.

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
peak telemetry from the batch comparison, plus arithmetic boundary tests;
those additions are not included in this timing attribution.
