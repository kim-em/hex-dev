# Packed native monomial preparation

Source fingerprint `7f850171b281`, Lean `v4.35.0-rc3`, AMD EPYC 9455,
`chungus2`. Native preparation fuses LCM/product/exact-quotient coordinates,
degree, support mask, semantic hash and maximum-coordinate computation into
one bounded loop. Exact packed comparisons resolve hash collisions. One owned
workspace is reused; its payload counts against the parent byte allowance.
No monomial identifier, exponent bound, coefficient field or mathematical
order is changed. Zero-variable and greater-than-4096-variable operations
retain the portable coordinate-array route.

## Candidate-only lean-bench comparison

One leased CPU (6), one computation thread, adjacent AB then BA blocks per
case, three retained samples per arm/block. Both arms use the same binary,
GM criteria, shared independent final-tail reductions and native coefficient
row updates. Arm A selects `Limits.nativeMonomials := false`; arm B selects
the packed native route. Inputs use `p = 65537`, grevlex and identical
one-billion-unit work allowances and batch cap 1024. Input generation is excluded; normalization
through final interreduction, decoding and full structural basis hashing are
included. Certificate generation, independent verification and kernel checking
are excluded. No completed sample was removed and no unchanged rerun was used.

| Case | AB median A → B | BA median A → B | Geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-5 | 4.877 → 3.700 ms | 4.870 → 3.603 ms | 0.749 |
| cyclic-6 | 43.349 → 30.066 ms | 43.180 → 30.126 ms | 0.696 |
| Katsura-3 | 0.375 → 0.312 ms | 0.378 → 0.314 ms | 0.832 |
| Reimer-5 | 232.183 → 155.433 ms | 229.588 → 156.549 ms | 0.676 |

All 48 samples succeeded, with matching full basis hashes. These are fixed
systems, with no asymptotic or external leadership claim. The
[raw exports and logs](hexgroebner-native-monomials-7f850171b281.tar.gz),
[commands and host context](hexgroebner-native-monomials-7f850171b281.measurement.json),
[analysis](hexgroebner-native-monomials-7f850171b281.analysis.json),
[manifest](hexgroebner-native-monomials-7f850171b281.manifest) and
[exact measured source](hexgroebner-native-monomials-sources-7f850171b281.tar.gz)
are retained. Raw archive SHA256:
`b95985091ace79d093ef1e35584b0e06985a47993f9aaa041a82f056234b16ac`.

## Matched msolve diagnostic sweep

The unchanged 16-input diagnostic suite has SHA256
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
One leased CPU (71), one computation thread, adjacent AB/BA comparisons,
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
| cyclic-5 | 2.12 | 2.21 |
| cyclic-6 | 3.75 | 3.84 |
| Katsura, six variables | 2.16 | 2.31 |
| Eco10 | 18.14 | 18.53 |
| Noon-4 | 2.06 | 2.14 |
| Reimer-5 | 11.61 | 11.51 |
| tiny MinRank | 1.70 | 1.95 |
| dense quadratic, five variables | 2.09 | 2.27 |

Ratios are geometric means of the two paired whole-process ratios. Hex still
loses on every input. Eco10 takes about 1.46–1.51 seconds versus 79–83 ms;
Reimer-5 takes 177–183 ms versus 14–17 ms. Maximum observed peak RSS is
95,756 KiB for Hex and 19,316 KiB for msolve. Startup contributes substantially
to the small cases; the first msolve cyclic-5 sample is 13.88 ms and its reversed
sample is 11.81 ms, both retained.

This frozen diagnostic suite is not the SPEC's balanced acceptance suite or
held-out set. Other comparators, extension fields, parallel sweeps and complete
certification remain required. The evidence demonstrates a useful native
operation and quantifies the remaining gap; it establishes no compiler/runtime
impossibility and no fastest-open-source milestone.

[Metadata and summary](hexgroebner-msolve-native-monomials-7f850171b281.json) and
the [raw archive](hexgroebner-msolve-native-monomials-7f850171b281.tar.gz)
retain inputs, full outputs, individual samples, failures, memory, exact
commands, source manifest, driver and comparison scripts, and comparator
license. Raw archive SHA256:
`f11406e88ef56cd75d782492dd1c3ea7b584b81196184ebe867eeeff5eb6a359`.

The earlier `2a390ee6b209` observation and its source, raw samples and metadata
remain retained. That version used batch cap 64 and backend-specific workspace
accounting. The version measured here uses a common reservation in both modes,
distinct byte/count exhaustion and batch cap 1024. The code changed between
observations; neither is an unchanged repeat.
