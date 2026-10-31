# Shared final-tail reduction

Source fingerprint `e77aafef582a`, Lean `v4.35.0-rc3`, AMD EPYC 9455 on
`chungus2`. Both arms use the same binary, deterministic GM pair criteria,
exact native row updates and resource allowances. Arm A reduces final tails
separately; arm B builds their union symbolic closure once and reduces each
original target independently. Targets never become pivots for other targets;
zero remainders, input order and the original scalar are preserved.

## Candidate-only lean-bench comparison

One leased CPU (61), one computation thread, adjacent AB then BA blocks per
case, three retained samples per arm/block. Input construction is excluded;
normalization through final interreduction, decoding and full basis hashing
are included. All cases use `p = 65537`, grevlex and a one-billion-unit work
allowance. Certificate generation, native verification and kernel checking
are excluded. Every completed sample is retained; no unchanged rerun was used. An earlier
measured version, `bc68b39bf673`, is also retained in its raw archives and
metadata. The version here skips the unused echelon-output scan and omits
empty tails from the shared matrix; it was measured after those code changes.

| Case | AB median A → B | BA median A → B | Geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-5 | 4.826 → 4.622 ms | 4.839 → 4.627 ms | 0.957 |
| cyclic-6 | 43.332 → 41.587 ms | 43.135 → 41.710 ms | 0.963 |
| Katsura-3 | 0.409 → 0.367 ms | 0.405 → 0.364 ms | 0.899 |
| Reimer-5 | 247.099 → 231.887 ms | 247.478 → 231.924 ms | 0.938 |

All 48 samples succeeded, with matching complete structural basis hashes.
The [raw exports and logs](hexgroebner-tail-sharing-e77aafef582a.tar.gz),
[exact commands and host context](hexgroebner-tail-sharing-e77aafef582a.measurement.json),
[source manifest](hexgroebner-tail-sharing-e77aafef582a.manifest) and
[analysis](hexgroebner-tail-sharing-e77aafef582a.analysis.json) are retained.
The raw archive SHA256 is
`08437f8476f3faaf4b491abc24fa02f91e7ba1c8985e0f29bff5859637bf980d`.

## Frozen diagnostic suite

A separate leased CPU (5) ran the unchanged 16-input diagnostic suite from
[the GM/msolve comparison](hexgroebner-msolve-gm.md): eight families, each at
`p = 32003` and `p = 2147483647`. This experiment compares only Hex arms A/B;
msolve was not rerun. The two measurements overlapped on separate leased CPUs;
recorded load and absolute times describe this shared host.

All 64 whole-process samples succeeded. Every coefficient and exponent of
all 32 paired complete bases agrees. Whole-process time includes executable
startup, prime checking, JSON parsing and output; the records separately
retain internal candidate time. Both arms use a 16 GiB address-space limit
and a 64 MiB output-file limit. These samples do not establish kernel-checked
results or the SPEC's balanced performance acceptance milestone.

Eco10 improves by about 10% and 11% in the two fields. At `p = 32003`, matrix
calls fall from 242 to 40, matrix entries from 12,392,534 to 8,867,016 and
charged work from 325,809,988 to 295,082,444. Reimer-5 improves by about 6%
and 5%. Whole-process cyclic-5 at `p = 32003` is about 7% slower, the
dense quadratic case at `p = 2147483647` is about 4% slower, and the tiny
MinRank case has ratios 0.993 and 1.001. These include process startup and
show more variability than the internal candidate measurements. All observations remain
in the records. This optimization removes repeated closure construction;
it leaves the much larger external gaps reported in the preceding sweep.

The [diagnostic metadata and samples](hexgroebner-tail-sharing-diagnostic-e77aafef582a.json)
and [raw archive](hexgroebner-tail-sharing-diagnostic-e77aafef582a.tar.gz)
retain all inputs, outputs, equality comparisons, scripts and the driver.
The diagnostic archive SHA256 is
`ea07d6af9cb569a25a3ba4b381770b22065f6ce7796e17a63a1acf1c4e0d9eaf`.

The 567-system conformance corpus also matches the separate-tail route,
serial batching, scalar arithmetic, SymPy F5B and Singular. An independent
Python RREF oracle checks each of 175 matrix cases for the exact unscaled
remainder of every original target and replays all derivations, including
zeros. Resource-boundary, native/portable and resume checks pass.
