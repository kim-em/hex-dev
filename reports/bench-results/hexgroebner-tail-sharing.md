# Shared final-tail reduction

Source fingerprint `bc68b39bf673`, Lean `v4.35.0-rc3`, AMD EPYC 9455 on
`chungus2`. Both arms use the same binary, deterministic GM pair criteria,
exact native row updates and resource allowances. Arm A reduces final tails
separately; arm B builds their union symbolic closure once and reduces each
original target independently. Targets never become pivots for other targets;
zero remainders, input order and the original scalar are preserved.

## Candidate-only lean-bench comparison

One leased CPU (39), one computation thread, adjacent AB then BA blocks per
case, three retained samples per arm/block. Input construction is excluded;
normalization through final interreduction, decoding and full basis hashing
are included. All cases use `p = 65537`, grevlex and a one-billion-unit work
allowance. Certificate generation, native verification and kernel checking
are excluded. Every completed sample is retained; no unchanged rerun was used.

| Case | AB median A → B | BA median A → B | Geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-5 | 4.772 → 4.572 ms | 4.757 → 4.576 ms | 0.960 |
| cyclic-6 | 42.648 → 41.270 ms | 42.589 → 41.029 ms | 0.966 |
| Katsura-3 | 0.396 → 0.354 ms | 0.400 → 0.357 ms | 0.892 |
| Reimer-5 | 242.572 → 227.925 ms | 242.587 → 228.030 ms | 0.940 |

All 48 samples succeeded, with matching complete structural basis hashes.
The [raw exports and logs](hexgroebner-tail-sharing-bc68b39bf673.tar.gz),
[exact commands and host context](hexgroebner-tail-sharing-bc68b39bf673.measurement.json),
[source manifest](hexgroebner-tail-sharing-bc68b39bf673.manifest) and
[analysis](hexgroebner-tail-sharing-bc68b39bf673.analysis.json) are retained.
The raw archive SHA256 is
`5ac445dfce69d5dcc0530733208559de4195fbdfa53f3508e0376772a8ce57f3`.

## Frozen diagnostic suite

A separate leased CPU (91) ran the unchanged 16-input diagnostic suite from
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
charged work from 325,809,988 to 295,083,128. Reimer-5 improves by about 6%
and 5%. The tiny MinRank case has B/A ratios 1.002 and 0.998; the individual
reversed block for Noon-4 at `p = 32003` is slower. All observations remain
in the records. This optimization removes repeated closure construction;
it leaves the much larger external gaps reported in the preceding sweep.

The [diagnostic metadata and samples](hexgroebner-tail-sharing-diagnostic-bc68b39bf673.json)
and [raw archive](hexgroebner-tail-sharing-diagnostic-bc68b39bf673.tar.gz)
retain all inputs, outputs, equality comparisons, scripts and the driver.
The diagnostic archive SHA256 is
`761165f3639b14cf5cf5980259032fbe2c95d925ffd3563ab9910fb0506d1653`.

The 567-system conformance corpus also matches the separate-tail route,
serial batching, scalar arithmetic, SymPy F5B and Singular. An independent
Python RREF oracle checks each of 175 matrix cases for the exact unscaled
remainder of every original target and replays all derivations, including
zeros. Resource-boundary, native/portable and resume checks pass.
