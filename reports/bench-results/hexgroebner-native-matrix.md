# Bounded native matrix scans and exact SIMD

The integrated native scan and row extraction reduce candidate time to **0.9141**
of the previous Lean scan with native sparse updates on the frozen 16-case
diagnostic suite. Whole-process time, including startup, parsing and full output,
has ratio **0.9406**. All 32 full reduced-basis comparisons and every recorded
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
or timeouts and no discarded samples. An incomplete refreshed attempt retains
44 completed samples: Lake relinked the executable during that attempt, so its
binary identity is not fixed and no aggregate claim uses those samples. The
single unchanged rerun used an immutable executable copy and completed all 64
scheduled samples. Both records are preserved.

The host is chungus2, AMD EPYC 9455, Lean 4.35.0-rc3, Clang 23.1.3,
`x86_64-unknown-linux-gnu`. The reviewed integrated comparison leased CPU 36. Native
objects use `cc -O3 -Wall -Wextra -fPIC -DLEAN_EXPORTING`; optional AVX2 is
selected at runtime, without a global ISA flag. The archive records CPU flags.
Input-suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
The reviewed source fingerprint is `a21473499ab9`; its exact source snapshot is
in [the reviewed production archive](raw/reviewed-native-production-records-a21473499ab9-repeat.tar.gz).
An earlier integrated version has fingerprint `8be04f0b8bd6`, candidate ratio
0.9233 and whole-process ratio 0.9658; [its archive](raw/native-production-records-8be04f0b8bd6.tar.gz)
also retains its exact sources. The subsequent whitespace cleanup had fingerprint
`b3c928b09605`, verified at commit `2e80ce9490d690b151f4b5c6903b75d394095643`;
[the object comparison](hexgroebner-native-matrix-object-equivalence.json) records
identical object bytes for that cleanup, before the CPU-detection and event
capacity changes in the reviewed implementation.

## Integrated full-system results

Ratios are B/A; lower is faster. The geometric mean of candidate ratios is
0.9299 for modulus 32003 and 0.8985 for 2147483647. AB and BA are shown
separately. Variability is substantial on several small cases, and regressions
remain visible. No sample is rejected for host activity, and no further
unchanged rerun is used. These observations do not isolate the effect of CPU
detection or event capacity from the rest of the native implementation.

| Input | AB candidate ratio | BA candidate ratio |
| --- | ---: | ---: |
| cyclic5-15 | 1.0084 | 1.1004 |
| cyclic5-31 | 0.6221 | 0.9652 |
| cyclic6-15 | 0.7891 | 1.0566 |
| cyclic6-31 | 0.6548 | 1.0787 |
| kat6-15 | 0.9830 | 0.9495 |
| kat6-31 | 1.2944 | 0.9181 |
| eco10-15 | 0.7521 | 0.8401 |
| eco10-31 | 0.9107 | 0.6343 |
| noon4-15 | 1.2728 | 1.0061 |
| noon4-31 | 1.1200 | 0.9559 |
| reimer5-15 | 0.8695 | 0.9576 |
| reimer5-31 | 0.8439 | 0.9258 |
| minrank_d_2_p_2_q_3_r_2-15 | 1.1368 | 0.9787 |
| minrank_d_2_p_2_q_3_r_2-31 | 0.9700 | 0.9645 |
| quadratic5-32003 | 0.5208 | 0.9277 |
| quadratic5-2147483647 | 0.8999 | 0.8801 |

## Kernel measurements

[lean-bench raw exports](raw/reviewed-lean-bench-records-a21473499ab9.tar.gz) compare the
previous production binary with the integrated binary, adjacent AB then BA on
leased CPU 23. Each invocation uses the declared fixed trial-major schedule
and three outer trials. Preparation is excluded; full result structural
hashing is included. The prime is 65537, with one computation thread; these
Cauchy figures use the AVX2 path on this host.
All 168 completed measurement points are retained and all result hashes match.
Thirty-one points are flagged below lean-bench's signal floor; none are discarded
from these descriptive ratios. The raw complexity verdicts and flags are
preserved; these ratios do not establish a new asymptotic complexity result.

Each entry is the geometric mean of the six matched per-call ratios across
three trials and two blocks. Cauchy matrices perform cubic fixed-word work;
the traced variant also retains shared derivations. Sparse cases have six
nonzeros per row and linear work, as derived in the registrations.

| Size | Cauchy | Cauchy with provenance | Sparse |
| ---: | ---: | ---: | ---: |
| 32 | 0.5828 | 0.6868 | 0.9250 |
| 64 | 0.4883 | 0.5869 | 1.0647 |
| 128 | 0.4235 | 0.5224 | 1.1183 |
| 256 | 0.3964 | 0.4559 | 1.0024 |
| 512 | 0.3855 | 0.3531 | — |

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
Instrumented native builds run UBSan and ASan across the Barrett/remainder and
SIMD/scalar variants. ASan covers C-owned buffers and stack storage, while
Lean's mimalloc buffers lack ASan heap redzones. Standalone guard-page tests
place dense, column and coefficient buffers immediately before inaccessible
pages, including contiguous and strided vectors ending at the last valid column.
A retained one-off bounds-check mutation faults with SIGSEGV on the guard page,
confirming that this check detects an out-of-bounds SIMD gather. Standalone SIMD tests
cover boundary residues, more than 17000 odd moduli and invalid vectors.
The compiled harness in `scripts/ci/check_groebner_matrix.py` runs all four
SIMD/scalar and Barrett/remainder combinations, with counters proving both
wrapped native functions execute. All four pass with Clang 23.1.3 and GCC 16.2;
all four pass UBSan and ASan with the scope above. Each run records 92164 scan
and 198139 gather calls; SIMD variants additionally record 19933 contiguous
and 64 strided vector updates. Scalar variants record zero vector updates.
`HEX_GROEBNER_SANITIZE=1` selects sanitizers; optional runtime/loader overrides
support Nix. The existing CI native script invokes the ordinary variants.
CPU detection checks CPUID and OS-enabled YMM state, caches its answer atomically
and has no compiler-runtime CPU model dependency. Event arrays begin with at
most eight slots and grow with actual recorded reductions.
Ordinary-kernel scan/extraction examples use only `propext` and `Quot.sound`;
complete polynomial certificate examples retain their existing axiom audits.

## Reproduction

Extract the reviewed production archive and use `root-sources` as the measured source
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

The incomplete refreshed attempt is [retained separately](raw/reviewed-native-production-records-a21473499ab9.tar.gz).

- `reviewed-lean-bench-records-a21473499ab9.tar.gz`: `45c0734a5ec6d6fa6c4b2f73c20393eeaf2443234985e886791cd0db50789098`
- `reviewed-native-production-records-a21473499ab9-repeat.tar.gz`: `609de087b56622f3b8b834377309a6badc0341e484911b6d26d04aec4dd0e6b7`
- `reviewed-native-production-records-a21473499ab9.tar.gz`: `dbbbb9594c84834eefe0b5dda0cb2a3575ec3f268be22a9c7b83bd950ebe41ae`

The submitted family fingerprint is `3940d502ee50`. It differs from measured
`a21473499ab9` only in the standalone C selftest; the benchmark executable hash
is unchanged. [Validation metadata](hexgroebner-native-matrix-validation.json)
and [raw validation logs](raw/native-matrix-validation.tar.gz) retain compiler,
variant, vector-call, guard-page mutation and operational-time evidence.
The four-variant harness took 18–26 seconds in these shared-host runs; this is
an operational observation, not a CI timing or performance acceptance claim.
