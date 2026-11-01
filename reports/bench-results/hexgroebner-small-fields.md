# Exact SIMD for narrow finite-field coefficients

The production AVX2 route now handles one- and two-byte canonical coefficients
with exact Barrett products, alongside the existing four-byte Montgomery route.
On the shared host, the 512-row Cauchy case over 32003 has observed B/A time
ratio **0.3865** (median 0.3859, range 0.3833–0.3910). With derivations recorded,
its ratio is **0.4744**. Eco-10 over 32003 has full F4 candidate ratios 0.8773
and 0.8838 in adjacent AB/BA comparisons. Across the fixed diagnostic suite,
the candidate geometric mean is **0.9854**, median **0.9895**; the matrix gain
is substantially larger than the full-system gain. There is no fresh external
comparator or fastest-open-source claim.

## Arithmetic, bounds and ownership

For odd moduli below 65536, a canonical product satisfies `x < p² < 2^32`.
With `mu = floor(2^32/p)`, `q = floor(x*mu/2^32)` underestimates the true
quotient by at most one. Thus `x-q*p < 2p`, and one subtraction gives the exact
residue. Eight lanes form unsigned products and high halves, followed by exact
canonical subtraction. The final values fit the selected byte/word width, so
packing does not saturate them. Four-byte coefficients retain Montgomery
arithmetic; ordinary characteristic-two polynomials retain scalar updates.
No floating-point arithmetic or global ISA flag is introduced.

Contiguous supports use narrow vector loads/stores. Strided supports gather
four bytes per lane and mask the requested scalar. Each complete four-byte
read must fit the logical dense buffer; otherwise the caller uses scalar
updates. Strictly increasing columns and canonical coefficients are checked
before mutation. A rejected vector performs no writes, allowing scalar handling
to preserve the exact malformed prefix. Existing copy-on-write ownership,
4096-transition call bounds, work/trace charges and pending-row semantics are
unchanged. CPUID and OS YMM-state detection retain the cached portable fallback.

## Validation

The full HexGroebner, theory, conformance and benchmark build passes. The 175
matrix, 567 SymPy/Singular basis and 1288 division/normal-form/membership oracle
cases pass. New cases cover narrow malformed vectors, aliases, contiguous and
strided supports, and padding on either side of the full-read boundary. All 29
benchmark verification cases and DAG, phase, release-manifest, source and
admission audits pass. The three new parametric registrations include explicit
cost derivations; a fixed cyclic-6 case over 32003 adds full-system coverage.

Clang 23.1.3 and GCC 16.2 both pass all four compiled SIMD/scalar and
Barrett/remainder variants, ordinarily and with ASan/UBSan. Each run calls the
scan 99656 times and gather 198139 times. Successful SIMD counters are 45247
contiguous and 572 strided calls; a six-bit coverage mask confirms both access
patterns at all three coefficient widths. Forced-scalar variants have zero
SIMD calls. `typeof` declarations check the helper/wrapper signatures.

Sanitizers instrument the C probe, not Lean-generated code. Lean mimalloc
buffers lack ASan heap redzones, and intrinsic gathers are not ASan-instrumented.
Standalone tests therefore retain the preceding wide-field tests and add narrow
buffers at the start/end of protected pages, with all gather paddings, factors
0/1/p-1 and malformed-prefix checks. UBSan failures are fatal. The portable
models and existing kernel replay remain independent of the native code.

## Measurement contract

The host is chungus2, AMD EPYC 9455, Lean 4.35.0-rc3. Generated C uses bundled
Clang 23.1.0; FFI uses system Clang 23.1.3. All measurements use one computation
thread pinned to an automatically leased CPU, adjacent AB then BA comparisons,
and frozen executables. Every completed sample, failure and regression is
retained; there are no failures, timeouts, discarded samples or unchanged
reruns in these small-field experiments. Host activity is recorded, not filtered.
Certificate generation, independent certification and kernel checking are excluded.

The final measured source fingerprint is `04e1c0a5f392`, at `e5c21df5cc`.
After adding only adjacent benchmark cost comments, the source fingerprint is
`8142939751e3`; rebuilding produces the **identical** benchmark executable,
SHA-256 `3c2f71d55dc1cec209ba0b0d5d2401f50237ed0302d77767fd8f7436ce7d6044`.
The matrix baseline is `c7f3733d84`, fingerprint `6cd3c5cfa77b`, with the same
new registrations and preceding native implementation. The diagnostic baseline
is `2c67a6358e`, fingerprint `6bb2e9080284`; its computational code matches the
matrix baseline (the added bench definitions do not enter that driver).
Binary hashes, exact source blobs and commands identify each arm independently
of rebased ancestry. Per-run `env.git_commit` describes the checkout when the
runner executes, rather than the executable's build revision.

## Registered lean-bench comparisons

[Production exports](raw/small-fields-small-production-kernels-04e1c0a5f392.tar.gz)
use leased CPU 7 and identical registrations in two frozen executables.
Cauchy preparation is excluded; validation, workspace allocation, elimination,
output decoding and full structural hashing are included. Hilbert entries
`1/(i+j+1)` have nonzero minors throughout the registered `2*n < p` domain.
Their exact `(n³-n)/3` entry updates give the declared cubic fixed-word model;
validation/scans/output and shared derivations add quadratic work.

Each matrix comparison uses the declared fixed trial-major ladder and three
outer trials, in adjacent AB then BA arms per family. The fixed F4 case uses
its declared five repetitions, including canonicalization and final
interreduction. All **152 points** complete and full result hashes agree.
The twelve parametric exports have **inconclusive complexity fits** because
of the runner's spawn guard; their raw timing points remain available. No guard
was relaxed to obtain a fitted verdict, and the timings do not establish a
complexity fit. Ratios below normalize total times by actual inner repeats.

| Case | Size | Geometric mean B/A | Median | Range |
| --- | ---: | ---: | ---: | --- |
| cauchy8 | 32 | 0.9026 | 0.9074 | 0.8877–0.9111 |
| cauchy8 | 64 | 0.7573 | 0.7576 | 0.7559–0.7585 |
| cauchy8 | 96 | 0.6611 | 0.6614 | 0.6586–0.6633 |
| cauchy16 | 64 | 0.7635 | 0.7634 | 0.7600–0.7682 |
| cauchy16 | 128 | 0.5910 | 0.5909 | 0.5891–0.5928 |
| cauchy16 | 256 | 0.4769 | 0.4767 | 0.4726–0.4814 |
| cauchy16 | 512 | 0.3865 | 0.3859 | 0.3833–0.3910 |
| cauchy16Trace | 64 | 0.8373 | 0.8388 | 0.8299–0.8430 |
| cauchy16Trace | 128 | 0.7089 | 0.7082 | 0.7053–0.7133 |
| cauchy16Trace | 256 | 0.5822 | 0.5819 | 0.5803–0.5848 |
| cauchy16Trace | 512 | 0.4744 | 0.4731 | 0.4638–0.4899 |
| cyclic6Small | fixed | 0.9835 | 0.9831 | 0.9799–0.9871 |

## Full F4 diagnostic comparisons

[Production samples](raw/small-fields-small-production-records-04e1c0a5f392.tar.gz)
use leased CPU 52 and the fixed 16-case grevlex diagnostic suite: cyclic-5/6,
Katsura-6, Eco-10, Noon-4, Reimer-5, MinRank and fixed quadratics, over 32003 and
2147483647. Suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
Each process has a ten-second timeout and 16-GiB address-space limit. Candidate
time covers production through final interreduction; process time additionally
includes startup, parsing and complete output. All 64 processes complete; all
32 full reduced-basis comparisons and operation counters agree.

The suite weights cyclic twice and is neither balanced nor held out. Means
below weight each paired ratio equally. Candidate B/A has geometric mean
0.9854, median 0.9895 and range 0.8773–1.1879. Process B/A has geometric mean
1.0044, median 0.9948 and range 0.8540–1.7103: no consistent process-time gain
is established. At 32003, candidate geometric mean/median are 0.9709/0.9829;
at the wider-prime control they are 1.0000/0.9947. The wider cyclic AB regression
and MinRank BA decrease are retained and are not treated as algorithmic gains.

| Input | AB B/A | BA B/A |
| --- | ---: | ---: |
| cyclic5-15 | 0.9835 | 0.9879 |
| cyclic5-31 | 0.9936 | 1.0027 |
| cyclic6-15 | 0.9842 | 0.9810 |
| cyclic6-31 | 1.1879 | 0.9846 |
| kat6-15 | 0.9818 | 0.9844 |
| kat6-31 | 0.9920 | 0.9979 |
| eco10-15 | 0.8773 | 0.8838 |
| eco10-31 | 1.0054 | 0.9911 |
| noon4-15 | 0.9963 | 1.0063 |
| noon4-31 | 0.9866 | 0.9985 |
| reimer5-15 | 0.9574 | 0.9747 |
| reimer5-31 | 1.0066 | 0.9917 |
| minrank_d_2_p_2_q_3_r_2-15 | 0.9850 | 1.0028 |
| minrank_d_2_p_2_q_3_r_2-31 | 0.9958 | 0.8865 |
| quadratic5-32003 | 0.9824 | 0.9769 |
| quadratic5-2147483647 | 1.0103 | 0.9920 |

## Alternative accumulators and prototypes

These are separate implementations/experiments with their own exact source
snapshots. They are not pooled with production results. All full bases match.
The wide variants use eight bytes per dense coefficient; their work/allocation
counter differences equal the additional initialized workspace, while other
counters agree. Wider accumulation does not provide an overall gain on this
suite and is not part of production.

| Implementation | CPU | Candidate geometric mean B/A | 32003 | 2147483647 | Evidence |
| --- | ---: | ---: | ---: | ---: | --- |
| UInt64 delayed accumulator, scalar | 13 | 1.0106 | 0.9913 | 1.0304 | [raw](raw/small-fields-wide-scalar-records-b3c928b09605.tar.gz) |
| UInt64 delayed accumulator, four-lane additions | 88 | 1.0299 | 0.9946 | 1.0664 | [raw](raw/small-fields-wide-simd-records-b3c928b09605.tar.gz) |
| Same wide SIMD, full-range Barrett normalization | 62 | 1.0286 | 0.9826 | 1.0767 | [raw](raw/small-fields-wide-barrett-records-022db869dd08.tar.gz) |
| Canonical narrow coefficients, Montgomery products | 75 | 0.9915 | 0.9810 | 1.0021 | [raw](raw/small-fields-small-simd-records-022db869dd08.tar.gz) |
| Canonical narrow coefficients, Barrett products | 11 | 0.9980 | 0.9839 | 1.0122 | [raw](raw/small-fields-small-barrett-records-6bb2e9080284.tar.gz) |

The narrow prototypes show Eco-10 gains in both orders, with larger variation
in small wider-prime controls. The production comparison above is the final
measurement. A separate [prototype kernel experiment](raw/small-fields-small-kernel-records-6bb2e9080284.tar.gz)
retains all 132 points and inconclusive fits. The Barrett-prototype archive
notes its stale hard-coded baseline label; its exact source manifest, binary
hashes and embedded source snapshot identify the actual computational sources.

## Reproduction and evidence

Overlay each archive's `root-sources` onto its recorded baseline, using its
exact blob identities. Matrix production exports additionally include
`baseline-sources`. Use the pinned toolchain and package directory; rebuild
`hexgroebner_bench` for matrix exports or the archived `compiled-driver` project
for `production_compare`. Both diagnostic arms use its default production route
without `--reference`. Prototype archives contain their own Lake projects.
The embedded scripts specify CPU leases, arm order, limits and commands.
Stage source overlays before fingerprinting; retain every completed sample.

The validation archive retains compiler, source, ordinary/sanitizer checks,
project audits and the final executable identity comparison. These measurements
advance the prime-field route; wider/extension fields, packed characteristic
two, multithreading, complete deterministic F4 proofs and the SPEC's matched,
balanced multi-comparator acceptance sweeps remain open.

Archive SHA-256 values:

- `small-fields-small-barrett-records-6bb2e9080284.tar.gz`: `5a0b2cf041aac65ab8bf1c2d7d2a68118503c08803f04574e65cb7dd43738904`
- `small-fields-small-kernel-records-6bb2e9080284.tar.gz`: `91b7b10ba002fbb4468379428ac723f1750045dacba8f4faa7ce2144d5622989`
- `small-fields-small-production-kernels-04e1c0a5f392.tar.gz`: `b8162a8f59679fb2f6a5f572b692b6fef9158dcbcd6602c4d03d3fa6d9adb46d`
- `small-fields-small-production-records-04e1c0a5f392.tar.gz`: `265d088e6be8b1c83ae330bfbb5608964842229b98d1a70747bdff404e971c9a`
- `small-fields-small-simd-records-022db869dd08.tar.gz`: `a5a056fb711cddb5c4851893d109a6ac43655a1f37796d0cbf0d27cb3d22a977`
- `small-fields-validation.tar.gz`: `88e4dc4e4d821b673b6c2664ff88066481f3eceb1e46cbc5fade501b3709c364`
- `small-fields-wide-barrett-records-022db869dd08.tar.gz`: `86306784392c636b1ccd4cd595b2b2923876e6db4b0c7f73dbcfc78fd5f439b3`
- `small-fields-wide-scalar-records-b3c928b09605.tar.gz`: `c2da6eb853ab3bb0e8bd3b9fbc0028f3997ec0a647c15311efe301c2e06316ca`
- `small-fields-wide-simd-records-b3c928b09605.tar.gz`: `59014f800b1860b792815cd6073229dfc9acbd41521e8d4c4a81fad928625975`
