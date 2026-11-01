# Proved packed-word reads for monomial metadata

Compared with the preceding production engine, the final implementation has
paired candidate-time median **0.9441** and geometric mean **0.9358** across
64 comparisons. The range is **0.6001–1.1024**, with large baseline-arm
variations retained. These observations support a candidate improvement around
5–6%; they establish neither a consistent whole-process gain nor an incremental
gain over the earlier compiler-rewrite variant. There is no fresh external
comparator, and the SPEC's fastest-open-source milestone remains open.

## Implementation and correctness

Degree, support-mask and hash reads previously assembled each cached word from
two four-byte reads, each with per-byte bounds checks. `Packed.read64` retains
a byte-based logical definition. A proved `csimp` equality selects checked
unboxed `ByteArray.uget` indices. The complete-range check is followed by a
scalar `USize` round-trip addressability check, avoiding comparison against a
boxed `2^64` on 64-bit platforms. Metadata byte offsets use one multiplication;
prepared workspace reads use byte offsets directly.

The fallback duplicates the original reads. The fast/reference equality is
proved for every byte array and natural offset, on either supported word size,
including partial or mathematically unaddressable words. Agreement with two
aligned packed 32-bit reads is also proved. The compiler equality uses only
`propext` and `Quot.sound`; ordinary-kernel examples retain direct reduction of
the reference definition. No new C binding or ISA requirement is introduced.

The `#guard` conformance check evaluates in the IR interpreter. A compiled
harness also calls it, comparing aligned/unaligned words against an independent
recursive natural-number decoder, including zero/all-one bytes and words
ending at the final byte. The same compiled Lean reader object is exercised
in each of four native-matrix harness executables; their differing C flags
apply to the matrix probe, not the Lean reader. The reader is not sanitizer
instrumented. Runtime reader checks use valid offsets; the fallback is covered
by the complete proof and kernel partial-word example rather than a compiled
fallback call. Existing 175 matrix, 567 SymPy/Singular basis and 1288 division/
normal-form/membership oracle cases pass, as do the full library/theory/
conformance build, 25 benchmark verification cases and project audits.

## Measurement contract

A is the production engine at `da900e60cb6136159c3b644c6cf8e4f01c765b13`,
source-family fingerprint `3940d502ee50`. Its successor `a2c60b61` changes only
tests/documentation and has a byte-identical benchmark executable. Merged
commit `a4aad390a6` has the same tree as `a2c60b61` and is a permanent baseline.
Final B has source fingerprint `6bb2e9080284`. Each archive retains exact indexed
source blobs, the driver project, commands, inputs/outputs, binary hashes,
failures, memory and raw samples. Both executables are frozen copies. The
per-run lean-bench `env.git_commit` describes the working checkout at execution
time, not the executable's build revision; the recorded binary hashes and
source manifests identify the arms.

The shared host is chungus2, AMD EPYC 9455. Lean is 4.35.0-rc3; generated C uses
the toolchain's Clang 23.1.0 with default `-O3` flags. Existing FFI kernels use
system Clang 23.1.3. The compiler trace retains the complete invocation. No
per-change ISA flag is added; native matrix selection/arithmetic is identical
between arms.

The 16 grevlex inputs are cyclic-5/6, Katsura-6, Eco-10, Noon-4, Reimer-5,
MinRank and fixed dense quadratics over 32003 and 2147483647. This diagnostic
suite gives cyclic two sizes; it is not balanced or held out. Suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
Each input has adjacent AB then BA comparisons, one computation thread pinned
to a leased CPU, a ten-second timeout and a 16-GiB address-space allowance.
Ratios below are B/A; geometric means weight paired input ratios equally,
without family balancing. All completed samples, regressions and outliers are
retained. There are no failures, timeouts or discarded samples.

Candidate time includes production through final interreduction. Process time
also includes startup, parsing and full output. Certificate generation,
independent certification and kernel checking are excluded and remain separate
obligations. The final diagnostic and fixed-benchmark experiments each have
one unchanged rerun after inconclusive variation; no further reruns or host
quietness selection are used. Earlier changed implementations are separate
experiments and are not pooled with the final implementation.

## Changed reader implementations

Each initial experiment has 64 process samples (32 paired comparisons).

| Reader | CPU | Candidate geometric mean | Process geometric mean | Evidence |
| --- | ---: | ---: | ---: | --- |
| Force-inline existing readers | 77 | 1.0212 | 1.0043 | [raw](raw/metadata-inline-records-419928896e5a.tar.gz) |
| One checked range, natural indices | 23 | 0.9754 | 0.9887 | [raw](raw/metadata-checked-records-09e9e300a801.tar.gz) |
| Checked unboxed indices | 25 | 0.9478 | 0.9747 | [raw](raw/metadata-usize-records-a169746e3a13.tar.gz) |
| Proved compiler rewrite, retained kernel definition | 1 | 0.9480 | 0.9764 | [raw](raw/metadata-csimp-records-022db869dd08.tar.gz) |
| Scalar address round trip, collapsed offsets | 11 | 0.9271 | 0.9474 | [raw](raw/metadata-roundtrip-records-6bb2e9080284.tar.gz) |
| Same implementation, single unchanged rerun | 1 | 0.9446 | 1.0027 | [raw](raw/metadata-roundtrip-records-6bb2e9080284-repeat.tar.gz) |

Inlining alone regresses the suite and is not retained. The final code avoids
the big-number address comparison, but the end-to-end evidence does not
separate its benefit from the earlier compiler rewrite. A retained
[baseline profile](raw/metadata-baseline-profile.tar.gz) of Eco-10 at modulus
32003 attributes about 7.6% of sampled cycles to the old word reader. Its source
is `8be04f0b8bd6`, CPU 92; it motivates the experiment rather than quantifying
an isolated wall-time saving.

## Final full-system observations

All 64 full reduced-basis comparisons and every recorded operation counter
agree. Both runs and their pooled descriptive statistics follow.

| Samples | Candidate geometric mean / median / range | Process geometric mean / median / range |
| --- | --- | --- |
| First 32 pairs | 0.9271 / 0.9441 / 0.6001–1.1024 | 0.9474 / 1.0059 / 0.3685–1.2450 |
| Rerun, 32 pairs | 0.9446 / 0.9429 / 0.8732–1.0424 | 1.0027 / 0.9876 / 0.7933–1.9010 |
| All 64 pairs | 0.9358 / 0.9441 / 0.6001–1.1024 | 0.9747 / 0.9920 / 0.3685–1.9010 |

Three first-run A process samples are unusually slow: cyclic5-15 starts the
experiment at 75.6 ms, cyclic6-15 takes 152.6 ms, and kat6-31 takes 66.0 ms.
The cyclic6-15 A candidate takes 40.88 ms versus 24.04 ms in the other block;
its paired B candidates take 24.53 and 22.33 ms. Low first-run block-1 Eco
and Reimer ratios likewise include slower A samples. These observations are
baseline variation, not evidence of a comparably large algorithmic saving.
The rerun does not establish a consistent process-time improvement. Every
sample remains included in the statistics and archives.

| Input | First AB | First BA | Rerun AB | Rerun BA |
| --- | ---: | ---: | ---: | ---: |
| cyclic5-15 | 0.9523 | 0.9421 | 0.9380 | 0.9358 |
| cyclic5-31 | 0.9421 | 0.9402 | 0.9381 | 0.9523 |
| cyclic6-15 | 0.6001 | 0.9291 | 0.9256 | 0.9382 |
| cyclic6-31 | 0.9438 | 0.9391 | 0.9261 | 0.9493 |
| kat6-15 | 0.9822 | 0.9489 | 0.9411 | 0.9510 |
| kat6-31 | 0.9383 | 0.9720 | 0.9584 | 0.9516 |
| eco10-15 | 0.8933 | 0.9504 | 0.8967 | 1.0084 |
| eco10-31 | 0.9419 | 0.8186 | 1.0424 | 0.8732 |
| noon4-15 | 0.9520 | 1.1024 | 0.9514 | 0.9408 |
| noon4-31 | 0.9460 | 0.9832 | 0.9496 | 0.9397 |
| reimer5-15 | 0.9213 | 0.8441 | 0.9278 | 0.9257 |
| reimer5-31 | 0.9341 | 0.8166 | 0.9742 | 0.8819 |
| minrank_d_2_p_2_q_3_r_2-15 | 0.9910 | 0.9184 | 0.9627 | 0.9529 |
| minrank_d_2_p_2_q_3_r_2-31 | 0.9721 | 0.9876 | 0.9603 | 0.9829 |
| quadratic5-32003 | 0.9479 | 0.9446 | 0.9374 | 0.9446 |
| quadratic5-2147483647 | 0.9483 | 0.9444 | 0.9458 | 0.9400 |

## Registered lean-bench cases

The final [first exports](raw/metadata-roundtrip-bench-records-6bb2e9080284.tar.gz)
and [single unchanged rerun](raw/metadata-roundtrip-bench-records-6bb2e9080284-repeat.tar.gz)
use existing fixed F4 registrations at modulus 65537 and their declared five
measured repetitions. Per case, frozen programs run adjacent AB then BA, on
leased CPUs 16 and 13 respectively. All 160 points complete; all complete result
hashes agree. Ratios normalize totals by actual inner-repeat counts.

| Case | First geometric mean | Rerun geometric mean | All-point geometric mean | All-point median | All-point range |
| --- | ---: | ---: | ---: | ---: | --- |
| cyclic4 | 0.8629 | 0.9486 | 0.9047 | 0.9487 | 0.4932–1.0868 |
| cyclic5 | 0.9117 | 0.9259 | 0.9187 | 0.9172 | 0.8749–0.9531 |
| cyclic6 | 0.9069 | 0.9210 | 0.9139 | 0.9106 | 0.8995–0.9387 |
| reimer5 | 0.9034 | 0.9087 | 0.9060 | 0.9044 | 0.7965–1.0340 |

Cyclic-4's first two A points of the first invocation are unusually slow;
their paired ratios are 0.4932 and 0.6087. They drive the first-run geometric
mean below its median. The unchanged rerun's range is 0.9309–0.9745. The report
retains every point and does not interpret the first-run aggregate as a stable
14% improvement.

The preceding [compiler-rewrite exports](raw/metadata-csimp-bench-records-022db869dd08.tar.gz)
and [unboxed-reader exports](raw/metadata-lean-bench-records-a169746e3a13.tar.gz)
remain separate. The latter use whole four-case suite arms; they are not pooled
with the final per-case comparisons.

## Reproduction

Extract an archive and overlay `root-sources` onto its recorded baseline tree.
Use its `compiled-driver` with the pinned toolchain; point the Hex requirement
and package directory to that checkout and build `production_compare`. Both
arms use the default route without `--reference`: A precedes the reader change,
B uses the archived source snapshot. Stage the overlay before fingerprinting.
The metadata embeds exact leased-CPU scripts, limits and full-output checks.
For lean-bench, use the retained commands and declared fixed repetitions. Keep
every completed sample and distinguish candidate, process and certification
costs. Combined analysis files in the rerun archives include both runs.

[Final compiler trace, assembly and validation logs](raw/metadata-roundtrip-validation.tar.gz)
retain the generated-code and correctness checks. The preceding
[validation archive](raw/metadata-validation.tar.gz) remains separate.

Archive SHA-256 values:

- `metadata-baseline-profile.tar.gz`: `3009cb875a0b978901bd46a9b41cfba01b5b3c57973721c6ffb1169990264faa`
- `metadata-checked-records-09e9e300a801.tar.gz`: `ec5c688d5dd82a842bb876de5cd583a3a7315c8c577af27ff7063332ad584ec2`
- `metadata-csimp-bench-records-022db869dd08.tar.gz`: `548065e2c7812a3b2c62265485889695843f07cd7127d2be96ef45d918b6eeee`
- `metadata-csimp-records-022db869dd08.tar.gz`: `3289068a64e06615e739786a5bcd1ba98414e461b4efacdbe286fbffe1e0a44b`
- `metadata-inline-records-419928896e5a.tar.gz`: `121e35040eef199b428a44ccdd2e3b80b99f5e7064969934797906d17b8c962f`
- `metadata-lean-bench-records-a169746e3a13.tar.gz`: `c5eaa74e5fc99f12a1cc5d7e7edb15ae5ede4f52bd37be131e4892553a8eb4d7`
- `metadata-roundtrip-bench-records-6bb2e9080284-repeat.tar.gz`: `aa78f583c97e23a1f4e7e39e7db27fd426d919df7f82752375936bd09ce8fd74`
- `metadata-roundtrip-bench-records-6bb2e9080284.tar.gz`: `45d1f5b21418ee0cfdbe36f1ea6d7512869b03c95aaddbfe3eb749a973972ce2`
- `metadata-roundtrip-records-6bb2e9080284-repeat.tar.gz`: `777b4ce37699771436436e59434364b4e9ac52629d04049cfd6ac841012183ff`
- `metadata-roundtrip-records-6bb2e9080284.tar.gz`: `556a78e07d37a4d5b9e1e780eb27e8b75556d885ad2c7ea6b9833e8c8955fa8d`
- `metadata-roundtrip-validation.tar.gz`: `c23b25e683bc8e8ab5da4decbec00ebe4bc6e955680ff7375c3f7d125cd9665e`
- `metadata-usize-records-a169746e3a13.tar.gz`: `4253d0fa5bdcd2950abeb18534e7e17ee490fcd4001dd4d3874f3e9fb272fb09`
- `metadata-validation.tar.gz`: `cc6acb3a341bfa2d3065b5abfe298db8fd349318c23a24b546882d24f4feb64f`
