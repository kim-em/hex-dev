# Exact SIMD for narrow finite-field coefficients

The production AVX2 route now handles one- and two-byte canonical coefficients
with exact Barrett products, alongside the existing four-byte Montgomery route.
On the shared host, the 512-row Cauchy case over 32003 has observed B/A time
ratio **0.3865** (median 0.3859, range 0.3833–0.3910). With derivations recorded,
its ratio is **0.4744**. Eco-10 over 32003 has full F4 candidate ratios 0.8773
and 0.8838 in adjacent AB/BA comparisons. Across the fixed diagnostic suite,
the candidate geometric mean is **0.9854**, median **0.9895**; the matrix gain
is substantially larger than the full-system gain. A diagnostic comparison with current msolve is reported below; it shows a
substantial remaining gap and does not establish the balanced acceptance milestone.

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
strided supports, and padding on either side of the full-read boundary. The initial 29
benchmark verification cases and DAG, phase, release-manifest, source and
admission audits pass. The three new parametric registrations include explicit
cost derivations; a fixed cyclic-6 case over 32003 adds full-system coverage.

Clang 23.1.3 and GCC 16.2 both pass all four compiled SIMD/scalar and
Barrett/remainder variants, ordinarily and with ASan/UBSan. The original runs call the
scan 99656 times and gather 198139 times. Original successful SIMD counters are
45247 contiguous and 572 strided calls; a six-bit coverage mask confirms both access
patterns at all three coefficient widths. Forced-scalar variants have zero
SIMD calls. `typeof` declarations check the helper/wrapper signatures.

Sanitizers instrument the C probe, not Lean-generated code. Lean mimalloc
buffers lack ASan heap redzones, and intrinsic gathers are not ASan-instrumented.
Standalone tests therefore retain the preceding wide-field tests and add narrow
buffers at the start/end of protected pages, with all gather paddings, factors
0/1/p-1 and malformed-prefix checks. UBSan failures are fatal. The portable
models and existing kernel replay remain independent of the native code.

Expanded validation adds the tight raw moduli 255 and 65535, exhaustive
one-byte odd-modulus products, and the strided benchmark. All **30** benchmark
verifications pass. The four variants pass again under both compilers, ordinarily
and with sanitizers: 116054 scan and 198139 gather calls per variant, with
61471 contiguous and 740 strided SIMD calls and width/access mask 63. These
counts describe the expanded run, separately from the original counts above.
[Expanded logs and sources](raw/small-fields-expanded-validation.tar.gz) retain
the complete build, oracles, sanitizer checks and audits.

## Measurement contract

The host is chungus2, AMD EPYC 9455, Lean 4.35.0-rc3. Generated C uses bundled
Clang 23.1.0; FFI uses system Clang 23.1.3. All measurements use one computation
thread pinned to an automatically leased CPU, adjacent AB then BA comparisons,
and frozen executables. Every completed sample, failure and regression is
retained. The original production experiments have no failures, timeouts,
discarded samples or unchanged reruns. Subsequent calibration experiments below
retain and explicitly identify an invalid timing wrapper. Host activity is recorded, not filtered.
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
The twelve parametric exports have **inconclusive complexity fits**. Three
lack enough rows above the spawn guard; the other nine fit decreasing normalized
costs over the finite tested range. The original verdicts and every raw point
are retained. Beta denotes the log-log slope of `time/n^3`; the fitted raw-time
exponent is `3+beta`. The fit table and disposition below explain these findings.
Ratios below normalize total times by actual inner repeats.

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
at the wider-prime control they are 1.0000/0.9947. The wider cyclic AB ratio includes an unusually low A candidate counter
(23.1 ms, versus 27.1–27.5 ms in the other arms/blocks). The maximum process
ratio includes an unusually fast first A process (27.7 ms, versus about 47 ms
elsewhere). These are baseline-arm outliers, not isolated evidence of a B
regression. The MinRank decrease and all other samples are retained; none are
treated as algorithmic gains in the wider-prime control.

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

## Remaining gap to current msolve

Before the comparator sweeps, `git fetch origin master` confirmed that the
msolve checkout still matches upstream commit
`3672113ee2c696a2ac9c637636e0f7214f500ba1` (2026-10-25), version 0.11.0.
Its GCC 16.2 build uses `-O3 -march=native`, FLINT 3.6 and OpenMP support; all
71 upstream tests pass. Both arms run one thread on the same leased CPU.
`-g 2` requests the full reduced grevlex basis without FGLM/root solving.
The default exact sparse `-l 2` and probabilistic sparse/dense `-l 42` routes
are measured separately. Every exponent and coefficient in all 64 paired
basis comparisons agrees; every process completes under the same ten-second/
16-GiB limits. Native verification, certificates and kernel checking are excluded.

| Comparator route | CPU | Hex/msolve process geometric mean | Median | Range | Evidence |
| --- | ---: | ---: | ---: | --- | --- |
| Default exact sparse, `-l 2` | 8 | 3.1321 | 2.3475 | 1.7314–9.0112 | [raw](raw/small-fields-msolve-l2-records-8142939751e3.tar.gz) |
| Probabilistic sparse/dense, `-l 42` | 23 | 3.1936 | 2.3148 | 1.6922–12.8799 | [raw](raw/small-fields-msolve-l42-records-8142939751e3.tar.gz) |

These are whole-process comparisons, including each executable's startup,
parsing and full output, not isolated algorithm ratios. Hex's candidate-only
counter is recorded separately. Msolve also prints an internal F4 elapsed
counter, with 10-ms resolution; its conversion boundaries differ from Hex's
candidate timer. The rounding-aware observations below complement the matched
whole-process comparisons. On Eco and Reimer the process gap is about 7.6–9.1 times against
the default route; wider-prime Eco reaches about 12.4–12.9 times against the
probabilistic route. Smaller inputs include substantial startup cost. Every
completed sample is retained. This suite is diagnostic, gives cyclic two sizes,
and has no held-out or family-balanced acceptance claim. Other comparator
routes, current systems and parallel sweeps remain obligations.


Msolve's `TIMINGS` block prints `overall(elapsed)` with `%.2f` formatting. Its
F4 timer covers internal initialization, rounds and final reduction; Hex's
candidate counter additionally includes its canonicalization and interchange
decoding. These observations therefore have different conversion boundaries
and are coarser than the process samples. A displayed t seconds has rounding
interval approximately `[max(0,t-0.005),t+0.005]`. Below 0.05 s only a conservative
ratio lower bound is given. In particular, `0.00` is bounded by about 5 ms and
is never interpreted as zero running time.

| Route | Input | Hex candidate ms, AB/BA | Msolve displayed s, AB/BA | Rounding-aware ratio interval/bound across both samples |
| --- | --- | --- | --- | --- |
| -l 2 | eco10-15 | 590.2 / 589.5 | 0.06 / 0.06 | 9.1–10.7 |
| -l 2 | eco10-31 | 604.4 / 631.9 | 0.06 / 0.06 | 9.3–11.5 |
| -l 2 | reimer5-15 | 104.8 / 104.9 | 0.00 / 0.00 | > 21.0 |
| -l 2 | reimer5-31 | 107.0 / 106.9 | 0.00 / 0.00 | > 21.4 |
| -l 42 | eco10-15 | 589.7 / 586.8 | 0.06 / 0.06 | 9.0–10.7 |
| -l 42 | eco10-31 | 614.3 / 608.0 | 0.03 / 0.03 | > 17.4 |
| -l 42 | reimer5-15 | 104.1 / 104.3 | 0.00 / 0.00 | > 20.8 |
| -l 42 | reimer5-31 | 106.0 / 106.2 | 0.00 / 0.00 | > 21.2 |

These counters show a larger gap than process time: Reimer's internal comparison
is above about 20 times, and wider-prime Eco against probabilistic elimination
is above about 17 times even with conservative rounding. The bounds retain both
samples and do not infer an unrounded msolve runtime. These are qualified
internal-timer observations rather than matched representation-stage ratios.

The comparator archives include a source-metadata correction: their inherited
`hex_source_dirty` label was hard-coded and does not describe the clean execution
checkout. Exact executable hashes identify the measured `04e1c0a5f392` production
build; the archived `8142939751e3` source differs only in benchmark comments and
produces the byte-identical benchmark executable. No samples were changed or
excluded because of this metadata correction.

## Remaining full-system costs

A retained [production profile](raw/small-fields-production-profile.tar.gz)
of Eco-10 at modulus 32003 uses the frozen production driver, leased CPU 66,
1999-Hz cycle sampling and DWARF call graphs. No samples are reported lost.
About 16.6% of sampled cycles are in the narrow native scan; two reducer-trie
lookup loops account for about 8.7%, and monomial preparation, allocation and
reference-count operations also remain visible. These are sampled cycle
attributions, not isolated time savings or external-comparator evidence. The
profile explains why the matrix improvement exceeds the full-system gain and
motivates further work outside elimination. The raw recording and report are
retained; restricted kernel symbols do not resolve.


## Finite-range complexity findings

| Original export | Verdict | Normalized beta | Advisory |
| --- | --- | ---: | --- |
| cauchy16-b0-A | inconclusive | none | below_signal_floor, too_few_verdict_rows |
| cauchy16-b0-B | inconclusive | -0.753646 | finite-range slope |
| cauchy16-b1-A | inconclusive | -0.426374 | finite-range slope |
| cauchy16-b1-B | inconclusive | -0.753492 | finite-range slope |
| cauchy16Trace-b0-A | inconclusive | -0.551157 | finite-range slope |
| cauchy16Trace-b0-B | inconclusive | -0.826143 | finite-range slope |
| cauchy16Trace-b1-A | inconclusive | -0.545513 | finite-range slope |
| cauchy16Trace-b1-B | inconclusive | -0.825364 | finite-range slope |
| cauchy8-b0-A | inconclusive | none | below_signal_floor, too_few_verdict_rows |
| cauchy8-b0-B | inconclusive | none | partially_below_signal_floor, too_few_verdict_rows |
| cauchy8-b1-A | inconclusive | -0.93104 | finite-range slope |
| cauchy8-b1-B | inconclusive | -1.214567 | finite-range slope |

Disposition: the exact update count is `(n^3-n)/3`; validation, dense scans,
output decoding and hashing add quadratic work, and inversion/setup add lower
orders. In a model `T(n)=a*(n^3-n)/3+b*n^2+c*n+d`, normalized cost decreases
when lower-order terms remain significant. Reducing a with SIMD can make this
finite-range effect more visible. This is an inference consistent with the
slopes and known operations, not an isolated experimental attribution. At n=64
the original untraced two-byte cases take about 4.1/3.1 ns per update
(scalar/SIMD); at n=512 they take about 1.67/0.64 ns. The fits do not establish
a completed complexity milestone.

The one-byte Cauchy domain has the mathematical limit `2*n < 251`; increasing
n beyond 125 would invalidate the full-minor argument. Its registration now
includes 125. All four narrow parametric registrations now request four-second
batches with a 32-second per-call cap. The new strided two-byte case maps column j to 2*j,
adds trailing padding, preserves full row rank and retains the exact cubic
entry-update count while increasing quadratic dense scans. The default spawn
guard is retained; inconclusive fits remain findings rather than successful
complexity claims.

## Calibrated scalar and SIMD kernels

The [final calibration](raw/small-fields-final-calibrated-records-97a2e5357071.tar.gz)
uses source fingerprint `97a2e5357071` at `70441ea57e`, leased CPU 13,
three outer trials per rung and adjacent AB then BA per family. Unlike the
original old-engine comparison, these arms use the same current source with
`HEX_GROEBNER_NO_AVX2` selecting scalar A. Timed C providers contain no counters;
the pure benchmark bodies include elimination, decoding and complete hashing.
All **192 points** complete with matching hashes. Separate untimed strided-64
probes execute 10024 strided vector calls and zero contiguous calls; scalar
executes zero vector calls. Both return 64 valid rows. These probes are path
evidence, not timings. This one-host result does not establish gather performance
on other processors or under different microcode mitigations.

| Case | n=64 B/A | n=128 B/A | n=256 B/A | n=512 B/A |
| --- | ---: | ---: | ---: | ---: |
| cauchy16 | 0.7584 | 0.5494 | 0.4477 | 0.3485 |
| cauchy16Trace | 0.8195 | 0.6928 | 0.5615 | 0.4479 |
| cauchy16Strided | 0.8520 | 0.7095 | 0.6152 | 0.5354 |

The one-byte ratios at n=32/64/96/125 are 0.9256/0.7978/0.6893/0.6371.
All sixteen exports fit a slope, and all remain inconclusive. One export has
some rows below the spawn guard; each has enough verdict rows to fit.

| Case | AB scalar beta | AB SIMD beta | BA scalar beta | BA SIMD beta |
| --- | ---: | ---: | ---: | ---: |
| cauchy8 | -0.850160 | -1.026820 | -0.848982 | -1.153402 |
| cauchy16 | -0.406838 | -0.785229 | -0.410746 | -0.754647 |
| cauchy16Trace | -0.551441 | -0.832343 | -0.537691 | -0.831299 |
| cauchy16Strided | -0.417375 | -0.615555 | -0.409579 | -0.607704 |

The finite-range cubic/lower-order disposition above applies to these findings;
calibration fixes the missing signal without making the fitted exponent cubic.
All actual repeat counts, spawn floors, advisories and verdict membership remain
in the exports. No further unchanged rerun is used to seek a favorable fit.

Two earlier calibration datasets are retained separately and are not pooled.
The [first one-second experiment](raw/small-fields-calibrated-records-c8fa3b5641aa.tar.gz)
contains 192 completed points, of which **48 strided timing points are invalid**:
an IO wrapper constructed a pure elimination result outside the repeated timed
action, so repeated execution timed the wrapper rather than elimination. Its
`validity.json` identifies these points. They are retained as a measurement
failure and support no speed claim. The other 144 points use pure benchmark
bodies but include counted C probes, so they are also separate from production.
The [pure one-second experiment](raw/small-fields-pure-calibrated-records-c8fa3b5641aa.tar.gz)
fixes that wrapper and uses plain C providers. All 192 hashes match; its strided
512-row ratio is 0.5521. Some exports still lacked enough rows above the default
spawn guard, motivating the final four-second calibration. Each changed
experiment retains its own exact driver, source blobs, executable hashes,
commands and complete outputs, rather than replacing the unsuccessful data.

The [coarse-timer archive](raw/small-fields-coarse-timers.tar.gz) supplies the
msolve parser, both rounding-aware observations per input, source-boundary notes
and the original complexity-fit table. Its parser reproduces the observations
from the separately retained raw comparator stdout/stderr archives.

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
- `small-fields-production-profile.tar.gz`: `40fd77f7d711087865eff1402ffa5455827bce820ced4db734b939c018893356`
- `small-fields-msolve-l2-records-8142939751e3.tar.gz`: `c0a62a1f8a78969c684509c1b12f72e38f5becd07162a92013b481e9bb9adc61`
- `small-fields-msolve-l42-records-8142939751e3.tar.gz`: `81feb001c467fbd692ae21d8a6d5fe8690ab76ca688f3662ae62abb22bff2b1c`
- `small-fields-calibrated-records-c8fa3b5641aa.tar.gz`: `7bb42c69296bf9c867c0ac5129f0aff42f8d42a84c1c3d40490953e06d87ad88`
- `small-fields-pure-calibrated-records-c8fa3b5641aa.tar.gz`: `89caa73a24637fba53e910cc087e665f1b56c12689dc575234cae45c10995d01`
- `small-fields-final-calibrated-records-97a2e5357071.tar.gz`: `5079315c580f09dda66d9329a96b23b1ddd239051c9b33a6f62e1447ab3a3141`
- `small-fields-expanded-validation.tar.gz`: `58c00381756d5d733fe62c7682a3fd83c9def37a9c48d52cc41c1c76354a98d6`
- `small-fields-coarse-timers.tar.gz`: `145019d205c747346f0051d4b025523cec11fd2cb656f121b7bf0da32d9bd25d`
