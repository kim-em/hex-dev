# Proved packed-word reads for monomial metadata

The final compiler-rewrite implementation has observed candidate-time ratio
**0.9480** against the preceding production engine on the fixed 16-case
diagnostic suite. Whole-process ratio is **0.9764**. All 32 full reduced-basis
comparisons and every recorded operation counter agree. This is a Hex before/
after comparison, without a fresh external comparator; it does not establish
the SPEC's fastest-open-source milestone.

## Implementation and correctness

Degree, support-mask and hash reads previously assembled each cached word from
two four-byte reads, each with per-byte bounds checks. `Packed.read64` retains
a byte-based logical definition. A proved `csimp` equality selects an
implementation with one complete-range check, one addressability check and
unboxed `ByteArray.uget` indices. The fallback contains the original reads,
so partially available or mathematically unaddressable words retain their
logical behavior. The complete fast/reference equality is proved for every
byte array and natural offset, on either supported word size. Agreement with
two aligned packed 32-bit reads is also proved. The compiler equality uses only
`propext` and `Quot.sound`; ordinary-kernel examples retain direct reduction
of the reference definition. No new C binding or ISA requirement is introduced.

Compiled conformance compares valid aligned/unaligned words with an independent
recursive natural-number decoder, including zero and all-one bytes and words
ending at the final byte. Existing 175 matrix, 567 SymPy/Singular basis and 1288
division/normal-form/membership oracle cases pass, as do the complete library/
theory/conformance build and all 25 benchmark smoke cases.

## Measurement contract

A is the production engine at `da900e60cb6136159c3b644c6cf8e4f01c765b13`,
source-family fingerprint `3940d502ee50`. The subsequent parent commit
`a2c60b61a34fc8c238954570fec50e59ae4eece7` changes only tests/documentation;
its benchmark executable is byte-identical. B has measured source fingerprint
`022db869dd08`. Each archive retains exact indexed source blobs, the driver
project, commands, input/output data, binary hashes, failures, memory and raw
samples. Both executables are frozen copies, so later builds cannot replace
them during measurement.

The shared host is chungus2, AMD EPYC 9455. Lean is 4.35.0-rc3; generated C uses
the toolchain's Clang 23.1.0 with its default `-O3` flags. Existing FFI kernels
use system Clang 23.1.3. The retained compiler trace records the complete
invocation. No per-change ISA flag is added. Existing native matrix SIMD
selection and arithmetic are identical between arms.

The 16 inputs are cyclic-5/6, Katsura-6, Eco-10, Noon-4, Reimer-5, MinRank and
fixed dense quadratics over 32003 and 2147483647, in grevlex. This diagnostic
suite gives cyclic two sizes and is not the balanced or held-out acceptance
suite. Suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
Each input has adjacent AB then BA comparisons, one computation thread pinned
to a leased CPU, a ten-second timeout and a 16-GiB address-space allowance.
All completed samples are retained, including regressions. There are no
failures, timeouts, discarded samples or unchanged reruns in these experiments.
Candidate production through final interreduction is timed internally; whole-
process time additionally includes startup, parsing and complete output.
Certificate generation, independent certification and kernel checking are
excluded and remain separate obligations.

## Changed reader implementations

Each row is a separate 64-sample experiment against the preceding production
engine, not repeated samples pooled for one implementation.

| Reader | CPU | Candidate B/A | Whole process B/A | Evidence |
| --- | ---: | ---: | ---: | --- |
| Force-inline existing readers | 77 | 1.0212 | 1.0043 | [raw](raw/metadata-inline-records-419928896e5a.tar.gz) |
| One checked range, natural indices | 23 | 0.9754 | 0.9887 | [raw](raw/metadata-checked-records-09e9e300a801.tar.gz) |
| Checked unboxed indices | 25 | 0.9478 | 0.9747 | [raw](raw/metadata-usize-records-a169746e3a13.tar.gz) |
| Proved compiler rewrite, retained kernel definition | 1 | 0.9480 | 0.9764 | [raw](raw/metadata-csimp-records-022db869dd08.tar.gz) |

Inlining alone regresses the suite and is not retained. The selected version
has the unboxed reader's observed gain while keeping the original logical
byte-read behavior. A retained [baseline profile](raw/metadata-baseline-profile.tar.gz)
of Eco-10 at modulus 32003 attributes about 7.6% of sampled cycles to the old
word reader. That profile uses source `8be04f0b8bd6` and CPU 92; it motivates
the experiment rather than quantifying an isolated wall-time saving.

## Final full-system results

The ratios below are the two adjacent candidate-time comparisons, separately.
The wider-prime MinRank BA regression is retained.

| Input | AB B/A | BA B/A |
| --- | ---: | ---: |
| cyclic5-15 | 0.9444 | 0.9459 |
| cyclic5-31 | 0.9396 | 0.9480 |
| cyclic6-15 | 0.9438 | 0.9419 |
| cyclic6-31 | 0.9458 | 0.9470 |
| kat6-15 | 0.9485 | 0.9540 |
| kat6-31 | 0.9366 | 0.9447 |
| eco10-15 | 0.9606 | 0.9519 |
| eco10-31 | 0.9595 | 0.9564 |
| noon4-15 | 0.9521 | 0.9443 |
| noon4-31 | 0.9616 | 0.9410 |
| reimer5-15 | 0.9404 | 0.9256 |
| reimer5-31 | 0.9353 | 0.9331 |
| minrank_d_2_p_2_q_3_r_2-15 | 0.9356 | 0.9697 |
| minrank_d_2_p_2_q_3_r_2-31 | 0.9534 | 1.0077 |
| quadratic5-32003 | 0.9462 | 0.9435 |
| quadratic5-2147483647 | 0.9415 | 0.9400 |

## Registered lean-bench cases

[Final raw exports](raw/metadata-csimp-bench-records-022db869dd08.tar.gz) use the
existing fixed F4 registrations at modulus 65537, their default five measured
repetitions and complete result structural hashing. Per case, the two frozen
programs run adjacent AB then BA on leased CPU 63. All 80 measurement points complete, and all result hashes agree. Each ratio is the geometric mean of ten paired per-call
ratios, normalizing each total by its actual inner-repeat count.

| Case | B/A |
| --- | ---: |
| cyclic4 | 0.9449 |
| cyclic5 | 0.9288 |
| cyclic6 | 0.9216 |
| reimer5 | 0.9171 |

The earlier unboxed-reader [exports](raw/metadata-lean-bench-records-a169746e3a13.tar.gz)
are retained separately. Their adjacent arms are whole four-case suite
invocations, with the default fixed repetitions within each invocation; they
are not pooled with the final per-case schedule.

## Reproduction

Extract an archive and overlay `root-sources` onto its recorded baseline tree.
Use the archived `compiled-driver` project with the same pinned toolchain,
point its Hex requirement and package directory to that checkout, and build
`production_compare`. Both arms invoke its default production route without
`--reference`; A is built before the reader change and B from the archived
source snapshot. Stage the overlay before computing its source fingerprint.
The metadata embeds the exact leased-CPU measurement script,
limits and complete-output checks. Keep every completed sample, compare full
bases and counters, and distinguish internal candidate from process timings.
For the final lean-bench comparison, use the archived commands and declared
five-repetition registrations, per case in AB then BA order. All source and
binary identities are retained independently of rebased commit ancestry.

Archive SHA-256 values:

- `metadata-baseline-profile.tar.gz`: `3009cb875a0b978901bd46a9b41cfba01b5b3c57973721c6ffb1169990264faa`
- `metadata-checked-records-09e9e300a801.tar.gz`: `ec5c688d5dd82a842bb876de5cd583a3a7315c8c577af27ff7063332ad584ec2`
- `metadata-csimp-bench-records-022db869dd08.tar.gz`: `548065e2c7812a3b2c62265485889695843f07cd7127d2be96ef45d918b6eeee`
- `metadata-csimp-records-022db869dd08.tar.gz`: `3289068a64e06615e739786a5bcd1ba98414e461b4efacdbe286fbffe1e0a44b`
- `metadata-inline-records-419928896e5a.tar.gz`: `121e35040eef199b428a44ccdd2e3b80b99f5e7064969934797906d17b8c962f`
- `metadata-lean-bench-records-a169746e3a13.tar.gz`: `c5eaa74e5fc99f12a1cc5d7e7edb15ae5ede4f52bd37be131e4892553a8eb4d7`
- `metadata-usize-records-a169746e3a13.tar.gz`: `4253d0fa5bdcd2950abeb18534e7e17ee490fcd4001dd4d3874f3e9fb272fb09`

[Compiler trace, assembly and validation logs](raw/metadata-validation.tar.gz)
retain the final generated-code and correctness checks.
