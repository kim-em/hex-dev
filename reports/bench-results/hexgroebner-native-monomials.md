# Packed native monomial preparation

Source fingerprint `2a390ee6b209`, Lean `v4.35.0-rc3`, AMD EPYC 9455,
`chungus2`. Native preparation fuses LCM/product/exact-quotient coordinates,
degree, support mask, semantic hash and maximum-coordinate computation into
one bounded loop. Exact packed comparisons resolve hash collisions. One owned
workspace is reused; its payload counts against the parent byte allowance.
No monomial identifier, exponent bound, coefficient field or mathematical
order is changed. Zero-variable and greater-than-4096-variable operations
retain the portable coordinate-array route.

## Candidate-only lean-bench comparison

One leased CPU (60), one computation thread, adjacent AB then BA blocks per
case, three retained samples per arm/block. Both arms use the same binary,
GM criteria, shared independent final-tail reductions and native coefficient
row updates. Arm A selects `Limits.nativeMonomials := false`; arm B selects
the packed native route. Inputs use `p = 65537`, grevlex and identical
one-billion-unit work allowances. Input generation is excluded; normalization
through final interreduction, decoding and full structural basis hashing are
included. Certificate generation, independent verification and kernel checking
are excluded. No completed sample was removed and no unchanged rerun was used.

| Case | AB median A → B | BA median A → B | Geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-5 | 4.598 → 3.492 ms | 4.566 → 3.487 ms | 0.762 |
| cyclic-6 | 41.321 → 28.997 ms | 41.428 → 28.946 ms | 0.700 |
| Katsura-3 | 0.362 → 0.302 ms | 0.357 → 0.300 ms | 0.837 |
| Reimer-5 | 230.401 → 157.966 ms | 232.908 → 158.418 ms | 0.683 |

All 48 samples succeeded, with matching full basis hashes. These are fixed
systems, with no asymptotic or external leadership claim. The
[raw exports and logs](hexgroebner-native-monomials-2a390ee6b209.tar.gz),
[commands and host context](hexgroebner-native-monomials-2a390ee6b209.measurement.json),
[analysis](hexgroebner-native-monomials-2a390ee6b209.analysis.json),
[manifest](hexgroebner-native-monomials-2a390ee6b209.manifest) and
[exact measured source](hexgroebner-native-monomials-sources-2a390ee6b209.tar.gz)
are retained. Raw archive SHA256:
`7860b027d140d1e15d21d1e17c72704a0a587c1375c1d2a5cd6c5ab9f5ef5679`.

## Matched msolve diagnostic sweep

The unchanged 16-input diagnostic suite has SHA256
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
One leased CPU (93), one computation thread, adjacent AB/BA comparisons,
10-second deadline, 16 GiB address-space and 64 MiB output-file limits. All
64 samples succeeded; both engines solved 16/16 inputs. Every coefficient
and exponent of all 32 paired complete reduced grevlex bases agrees.

The comparator is msolve 0.11.0, commit
`3672113ee2c696a2ac9c637636e0f7214f500ba1`, built with GCC 16.2, FLINT 3.6
and `-O3 -march=native`; its 71 upstream tests pass. `-g 2 -t 1 -l 2`
requests exact sparse reduced bases. Rational reconstruction, FGLM and root
solving are excluded. Both commands include process startup, input parsing and
full output. Hex's internal candidate timer is retained separately. Hex limits
and driver code are in the raw archive. Certification and Lean kernel checking
are absent from both commands.

| Input | Hex/msolve at p = 32003 | Hex/msolve at p = 2147483647 |
| --- | ---: | ---: |
| cyclic-5 | 1.67 | 2.27 |
| cyclic-6 | 3.68 | 3.87 |
| Katsura, six variables | 2.19 | 2.33 |
| Eco10 | 26.20 | 26.49 |
| Noon-4 | 2.10 | 2.23 |
| Reimer-5 | 11.84 | 11.75 |
| tiny MinRank | 1.86 | 2.05 |
| dense quadratic, five variables | 2.19 | 2.27 |

Ratios are geometric means of the two paired whole-process ratios. Hex still
loses on every input. Eco10 takes about 2.1–2.2 seconds versus 80–83 ms;
Reimer-5 takes 182–188 ms versus 14–17 ms. Maximum observed peak RSS is
93,548 KiB for Hex and 19,352 KiB for msolve. Startup contributes substantially
to the small cases; the first msolve cyclic-5 sample is 23.23 ms and its reversed
sample is 11.73 ms, both retained.

This frozen diagnostic suite is not the SPEC's balanced acceptance suite or
held-out set. Other comparators, extension fields, parallel sweeps and complete
certification remain required. The evidence demonstrates a useful native
operation and quantifies the remaining gap; it establishes no compiler/runtime
impossibility and no fastest-open-source milestone.

[Metadata and summary](hexgroebner-msolve-native-monomials-2a390ee6b209.json) and
the [raw archive](hexgroebner-msolve-native-monomials-2a390ee6b209.tar.gz)
retain inputs, full outputs, individual samples, failures, memory, exact
commands, source manifest, driver and comparison scripts, and comparator
license. Raw archive SHA256:
`a1565571e5717a80c8c5b0d381b14b973532e85e107f1aa0d417b8d2c157fdd0`.
