# Bounded native matrix scans and exact SIMD

The integrated native scan and row extraction reduce candidate time to **0.9233**
of the previous Lean scan with native sparse updates on the frozen 16-case
diagnostic suite. Whole-process time, including startup, parsing and full output,
has ratio **0.9658**. All 32 full reduced-basis comparisons and every recorded
operation counter agree. These observations support the native operations;
they do not establish performance leadership or the SPEC's family-balanced
acceptance milestone. Certificate generation, independent certification and
kernel checking are excluded from both timing arms.

## Matched contract

A and B run in one binary. A contains the elimination, symbolic preprocessing
and F4 driver from `d62715ec1894871cb4ab0cc204f6093ccc100579`, placed in a
separate namespace; B calls the integrated production implementation. Shared
polynomial, monomial and pair dependencies are identical. Both arms use exact
canonical residues, stable column order, native monomials, shared final
interreduction and batch cap 1024. The 16 inputs cover cyclic-5/6, Katsura-6,
Eco-10, Noon-4, Reimer-5, MinRank and fixed quadratic systems over 32003 and
2147483647 in grevlex. Cyclic has two sizes; this is a diagnostic suite rather
than a balanced or held-out acceptance suite.

Two adjacent blocks per input alternate AB then BA. Each arm uses one computation
thread, a leased CPU, a 10-second operational timeout and a 16-GiB address-space
allowance. All 64 completed samples, full outputs, failures, RSS, load averages,
commands, source manifests and binary hashes are retained. There are no failures
or timeouts, no discarded samples and no unchanged reruns.

The host is chungus2, AMD EPYC 9455, Lean 4.35.0-rc3, Clang 23.1.3,
`x86_64-unknown-linux-gnu`. The integrated comparison leased CPU 45. Native
objects use `cc -O3 -Wall -Wextra -fPIC -DLEAN_EXPORTING`; optional AVX2 is
selected at runtime, without a global ISA flag. The archive records CPU flags.
Input-suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
Measured source fingerprint is `8be04f0b8bd6`; its exact source snapshot is in
[the production archive](raw/native-production-records-8be04f0b8bd6.tar.gz).
The submitted source `b3c928b09605` only removes trailing whitespace from two
native files; [the object comparison](hexgroebner-native-matrix-object-equivalence.json)
records identical compiled bytes before and after that cleanup.

## Integrated full-system results

Ratios are B/A; lower is faster. The geometric mean of candidate ratios is
0.9366 for modulus 32003 and 0.9102 for 2147483647. AB and BA are shown
separately, including the narrower-prime MinRank regression in BA.

| Input | AB candidate ratio | BA candidate ratio |
| --- | ---: | ---: |
| cyclic5-15 | 0.9649 | 0.9626 |
| cyclic5-31 | 0.9661 | 0.9529 |
| cyclic6-15 | 0.9448 | 0.9441 |
| cyclic6-31 | 0.9238 | 0.9190 |
| kat6-15 | 0.9238 | 0.9227 |
| kat6-31 | 0.9082 | 0.9160 |
| eco10-15 | 0.8461 | 0.8454 |
| eco10-31 | 0.7504 | 0.7458 |
| noon4-15 | 0.9623 | 0.9693 |
| noon4-31 | 0.9595 | 0.9627 |
| reimer5-15 | 0.9503 | 0.9476 |
| reimer5-31 | 0.9230 | 0.9197 |
| minrank_d_2_p_2_q_3_r_2-15 | 0.9331 | 1.0047 |
| minrank_d_2_p_2_q_3_r_2-31 | 0.9673 | 0.9577 |
| quadratic5-32003 | 0.9377 | 0.9404 |
| quadratic5-2147483647 | 0.9194 | 0.9130 |

## Kernel measurements

[lean-bench raw exports](raw/lean-bench-records-8be04f0b8bd6.tar.gz) compare the
previous production binary with the integrated binary, adjacent AB then BA on
leased CPU 20. Each invocation uses the declared fixed trial-major schedule
and three outer trials. Preparation is excluded; full result structural
hashing is included. The prime is 65537, with one computation thread.
All 168 completed measurement points are retained and all result hashes match.
Fifteen points are flagged below lean-bench's signal floor; none are discarded
from these descriptive ratios. The raw complexity verdicts and flags are
preserved; these ratios do not establish a new asymptotic complexity result.

Each entry is the geometric mean of the six matched per-call ratios across
three trials and two blocks. Cauchy matrices perform cubic fixed-word work;
the traced variant also retains shared derivations. Sparse cases have six
nonzeros per row and linear work, as derived in the registrations.

| Size | Cauchy | Cauchy with provenance | Sparse |
| ---: | ---: | ---: | ---: |
| 32 | 0.5918 | 0.6910 | 0.9440 |
| 64 | 0.4885 | 0.6096 | 0.9746 |
| 128 | 0.4214 | 0.5450 | 0.9643 |
| 256 | 0.3949 | 0.4924 | 0.9370 |
| 512 | 0.3833 | 0.4783 | — |

## Native operation variants and controls

Every full-system experiment below has 64 completed samples and full matching
bases. They compare changed implementations, not unchanged reruns. Ratios are
geometric means over both blocks and all inputs. All raw samples, including
regressions, are retained.

| Native implementation | Baseline | CPU | Candidate B/A | Archive |
| --- | --- | ---: | ---: | --- |
| Entry-at-a-time scan | 2a6f523fa9 | 33 | 1.1025 | [raw](raw/native-scan-records-595f7362f1a1.tar.gz) |
| Bounded slices | 2a6f523fa9 | 26 | 0.9775 | [raw](raw/native-scan-chunk-records-595f7362f1a1.tar.gz) |
| Slices with owned transfer | 2a6f523fa9 | 56 | 0.9771 | [raw](raw/native-scan-owned-records-595f7362f1a1.tar.gz) |
| Owned scan and extraction | 2a6f523fa9 | 24 | 0.9641 | [raw](raw/native-scan-gather-records-595f7362f1a1.tar.gz) |
| Scan/extraction and AVX2 | d62715ec18 | 86 | 0.9402 | [raw](raw/native-scan-simd-records-713fef617e44.tar.gz) |
| Contiguous AVX2 control | scalar native | 88 | 0.9776 | [raw](raw/simd-control-records-713fef617e44.tar.gz) |
| Width-specialized AVX2 control | scalar native | 12 | 0.9758 | [raw](raw/dispatched-simd-control-records-713fef617e44.tar.gz) |
| Width-specialized inlined AVX2 | d62715ec18 | 62 | 0.9242 | [raw](raw/native-width-inline-records-713fef617e44.tar.gz) |

The entry-at-a-time transition regresses Eco-10 by roughly 53–55% and Reimer-5
by roughly 16%. The retained profile attributes the cost to repeated row
geometry and Lean object access. Hoisting geometry across a bounded contiguous
slice removes this regression. Owned transfer prevents the generated C from
retaining the dense buffer across the call; it has no additional aggregate
speed claim. The contiguous AVX2 control regresses the 32003 Eco input by about
4%. Dispatching outside width-specialized scalar loops removes that regression;
the selected scalar/AVX2 control ratios are 0.9932 at 32003 and 0.9587 at
2147483647. These controls use explicitly distinct objects with AVX2 disabled
for A; compiler traces and distinct binary hashes are retained. An initial
configuration-toggle attempt produced identical objects and was rejected as
an invalid control before scientific samples were collected.

The first four archives use baseline
`2a6f523fa9467fbc5e989c5b66e876fe9779c32c`, fingerprint `595f7362f1a1`.
Their inherited `protocol.A`/`protocol.B` labels name an earlier comparator
experiment. Their explicit `contract` and per-sample commands define these
experiments: A has no flag and B has `--prototype`; neither calls msolve.
Raw labels are preserved. The later prototype baseline is
`d62715ec1894871cb4ab0cc204f6093ccc100579`, fingerprint `713fef617e44`.

## Portable behavior and bounded calls

A scan call performs at most 4096 transitions: a column visit, one sparse-entry
update or completion of a reduction. Pending updates retain their work
reservation between calls. Extraction visits at most 4096 columns, normalizes
exact residues and clears consumed dense entries. Scalar loops specialize to
one-, two- or four-byte residues. Four-byte odd moduli can use exact AVX2
Montgomery products. Stored residues remain canonical. Vector validation
precedes mutation; invalid vectors fall back to the scalar failure prefix.

Native/portable comparisons cover all coefficient widths, large sugar labels,
malformed geometry, oversized natural indices, aliases, 4096-transition
boundaries, work, trace, output-entry and byte exhaustion. Full matrix tests
compare rows, derivations, sugar and all counters. Independent oracles compare
175 matrices, 567 full bases and 1288 division/normal-form/membership cases.
Address/undefined-behavior sanitizer checks cover the integrated native wrapper
and prototype Barrett/remainder, SIMD/scalar variants. Standalone SIMD tests
cover boundary residues, more than 17000 odd moduli and invalid vectors.
Ordinary-kernel scan/extraction examples use only `propext` and `Quot.sound`;
complete polynomial certificate examples retain their existing axiom audits.

## Reproduction

Extract the production archive and use `root-sources` as the measured source
overlay on the recorded parent checkout. Point the archived reference project's
Lake requirement to that checkout, preserve its reference modules and driver,
and build `production_compare`. A uses `--reference`; B has no flag. The
archived measurement script defines the adjacent AB/BA order, leased CPU,
limits and complete-output comparisons. Prototype archives instead use their
recorded Lake configuration and `--prototype` for B; explicit SIMD controls
use the separate `scan_compare_no_simd` binary for A. Preserve every completed
sample and compare complete bases and counters before interpreting timings.
The kernel archive records both binary hashes, commands and raw exports;
rebuild its A binary at the recorded baseline and B from the measured overlay.

Archive SHA-256 values:

- `dispatched-simd-control-records-713fef617e44.tar.gz`: `aab380ade9cab314e365b6a2b38cf3ac91185bd09614bbaa1710b4b693c78d31`
- `lean-bench-records-8be04f0b8bd6.tar.gz`: `30731d31bdfa20c8bd9dbe0c29aca7e012a5f1816ec0c026efda534f33f5e514`
- `native-production-records-8be04f0b8bd6.tar.gz`: `fbc04ba0a52cfd4ea222b5f0cba7a6c33f7e28190e385bd8aced5597a7c7ea6d`
- `native-scan-chunk-records-595f7362f1a1.tar.gz`: `4dc4f4e2aee3b3f38bb556ca318d0f018431e11cafd2c6d9e82f36a2b29c2a93`
- `native-scan-gather-records-595f7362f1a1.tar.gz`: `f5ef23fa942c3b0470e8ee552251a70e97f3df780ed05e65715956bb71123914`
- `native-scan-owned-records-595f7362f1a1.tar.gz`: `c0d89c40a924a0e0b84bde1fa803b82530af2f642b9c0774eee589bcc99885a5`
- `native-scan-records-595f7362f1a1.tar.gz`: `572bfd9bf17eadcd918d8ee50e757db1d0a579a131ae7610751a5b4691628d79`
- `native-scan-simd-records-713fef617e44.tar.gz`: `ef90dacb01da12659416022c738ee9e97ad7be72c3ca737698d03beb8285d53c`
- `native-width-inline-records-713fef617e44.tar.gz`: `5e075035a5336855394ff221574cec9e284dd46ee4cf50b4e829441d6d374111`
- `simd-control-records-713fef617e44.tar.gz`: `6eb7c991d0d81398e224e761b8b9b4730c125fcc0dcb67316c357faa78d07a81`
