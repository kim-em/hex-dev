# Bounded packed monomial comparisons

`MonomialTable.compare` and `divides` retain their cached degree and support-mask
filters and perform the remaining coordinate comparisons in a borrowed native
call. It handles lexicographic, reversed lexicographic and pointwise comparison
for one-, two- and four-byte exponents, with at most 4096 coordinates. Stable
IDs, storage, field arithmetic, scheduling and resource counters are unchanged.
Larger arities and unsupported shapes use the original portable loops.

Arbitrary-precision indices are bounded before conversion to the u64 ABI. The
selected `7ad863391bb7` implementation checks complete accessed row spans;
`(max(id)+1)*arity*width ≤ 2^46`, so validation cannot overflow even on 32-bit
hosts. Unused partial trailing rows require no access. Calls mutate no storage
and retain no pointers. The pure bodies remain available to the kernel.

The current `802ae51122d7` snapshot exposes typed `Native.Monomial.compare`
and `divides` wrappers. The kernel theorem `compareCode_eq` proves that checked
Nat narrowing equals the unrestricted portable definition for every input; its
axiom audit reports only `propext` and `Quot.sound`.

On CPU92, the current snapshot retains 64 successful processes and 32 full-basis
and counter agreements. Candidate B/A is 0.9562, median 0.9529 and range
0.9249–1.0268; process B/A is 0.9812, median 0.9800 and range 0.9443–1.0214.
No unchanged repeat is used. Its separate 120-point fixed sweep runs on CPU65,
with every structural hash matching:

| Current fixed case | Geometric mean B/A | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.9785 | 0.9792 | 0.9328–1.0140 |
| cyclic5 | 0.9731 | 0.9711 | 0.9593–0.9909 |
| cyclic6 | 0.9594 | 0.9590 | 0.9478–0.9701 |
| katsura3 | 0.9755 | 0.9783 | 0.9248–1.0472 |
| reimer5 | 0.9669 | 0.9676 | 0.9625–0.9693 |
| cyclic6Small | 0.9576 | 0.9579 | 0.9507–0.9666 |

The current and earlier snapshots are not pooled. Their observations do not
establish which snapshot is faster. The API and accessed-span semantics select
the current design, whose own measurements support a candidate-computation
improvement. These development observations do not establish leadership.

The earlier `03abfd63909b` implementation validates whole-arena row geometry
using division. The row-span version removes those division instructions from
the native helper; disassemblies of both frozen binaries are retained. This
instruction change does not establish a full-system speedup over that earlier
snapshot. Each snapshot is compared separately with the same frozen zero-scan
baseline, `f3d5acec8365`, whose source agrees with merged #11002.

Both arms use identical drivers and benchmark sources. The 16-input development
suite covers seven families at primes 32003 and 2147483647. Every input runs
adjacent AB then BA, one thread on an automatically leased CPU. Complete reduced
bases and every non-timing counter must agree. Every completed sample and
outlier is retained. Candidate time includes canonicalization, F4 and final
interreduction; process time adds startup, parsing and complete output.
Certificate generation, independent final certification and kernel checking
are excluded. This is not a held-out or fastest-open-source acceptance suite.

| Snapshot / campaign | CPU | Processes | Candidate geometric mean B/A | Median | Range | Process geometric mean |
| --- | ---: | ---: | ---: | ---: | --- | ---: |
| 03abfd63909b | 47 | 64 | 0.9510 | 0.9522 | 0.8686–0.9944 | 0.9967 |
| 7ad863391bb7 | 38 | 64 | 0.9784 | 0.9700 | 0.8097–1.3473 | 1.0006 |
| 7ad863391bb7, permitted repeat | 56 | 64 | 0.9600 | 0.9622 | 0.8709–1.0158 | 0.9851 |

All 96 paired complete bases and non-timing counter sets agree across the
three earlier campaigns. The first row-span observation is inconclusive, so one unchanged repeat is used.
Eco10 at p32003, block 0, supplies the 1.3473 candidate and 1.4124 process
maxima. Eco10 at p2147483647, block 0, supplies the 0.8097 candidate and 0.7383
process minima. Both campaigns are retained and pooled below. No further unchanged repeat is used. Pooling only the two
row-span campaigns gives candidate B/A 0.9691, median 0.9648 and range
0.8097–1.3473; process B/A is 0.9928, median 0.9871 and range 0.7383–1.4124.
The row-span design is selected because it validates exactly the bytes read by
the portable loops, accommodates unused trailing storage and avoids division.
These separate campaigns do not establish which geometry variant is faster.
The initial geometry snapshot is not pooled with the row-span implementation.
The observations support an improvement in candidate computation; whole-process
time remains near parity and the overall performance milestone is not met.

The registered fixed cases retain five declared repetitions and normalize by
actual inner repeats. Complete structural basis hashes agree. The initial
snapshot retains 120 points on CPU45. The earlier row-span snapshot retains 120 points
on CPU53 and its one permitted repeat retains 120 on CPU35.

| Fixed case | Initial geometry B/A | Row-span first B/A | Row-span repeat B/A | Row-span pooled B/A | Pooled median | Pooled range |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| cyclic4 | 0.9796 | 0.8601 | 0.9604 | 0.9089 | 0.9641 | 0.4409–1.1886 |
| cyclic5 | 0.9786 | 0.9395 | 0.9684 | 0.9538 | 0.9640 | 0.8842–0.9933 |
| cyclic6 | 0.9686 | 0.9242 | 0.9621 | 0.9429 | 0.9613 | 0.8180–0.9772 |
| katsura3 | 0.9631 | 0.8785 | 0.9509 | 0.9140 | 0.9367 | 0.6427–1.0160 |
| reimer5 | 0.9739 | 0.9266 | 0.9751 | 0.9505 | 0.9752 | 0.5884–0.9849 |
| cyclic6Small | 0.9414 | 1.1413 | 0.9624 | 1.0481 | 0.9649 | 0.9451–1.9699 |

The wide fixed-case ranges also limit conclusions from their means alone.
The pooled cyclic6Small mean regresses despite its lower median. Its completed
outlier remains included. These small development cases do not meet the
SPEC's family-balanced leadership requirements.

Clang and GCC pass all four ASan/UBSan variants. Standalone tests check 2700
array-oracle cases, maximum coordinates, read-only guard pages at both ends,
truncated rows, invalid indices and opcodes. Compiled tests compare every
native result with portable behavior and independent list order/inequalities,
including distinct arity-4096 rows, oversized left/right Nat inputs and unused
trailing bytes. Table-level tests compare all three orders with `TermOrder.cmp`
and divisibility with integer inequalities across u8/u16/u32 storage and arity
4097, exercising the portable dispatch as well as native calls. At the
latest F4 window, counters record 23064 native comparisons, 3553 during full
F4 calls. Matrix arithmetic mask 255 and zero-packet counters remain separate.
The 1950-job relevant library/theory conformance build, independent 175 matrix,
567 basis and 1288 division checks, and all 32 fast benchmark checks pass.
Their operational duration is not scientific timing evidence.

Archives retain exact source manifests and Git blobs for both arms, executable
hashes, full outputs, samples, memory, failures, analysis, source and compiler
identity. The current measured commit is
`e896a5bcea7891a0a501d196c6621db52286304f`. The earlier row-span commit is
`2487deec4c4689575c50d8f77e88c1321d231558`; the content-preserving rebase onto
merged `96c4c114debdbabe487113d81c53d121817d213c` has the same source family.

- [inspect-production-bench-03abfd63909b.tar.gz](raw/inspect-production-bench-03abfd63909b.tar.gz): `4def1eca0e5da8ab4e62de15245f7d58ae4884436dcc0018ee4a3be4058eed78`
- [inspect-production-records-03abfd63909b.tar.gz](raw/inspect-production-records-03abfd63909b.tar.gz): `2e5f102781cb68b737ede5af384e4eaae9f60b09f9d9cc3e2a5e1592af3da789`
- [inspect-validation.tar.gz](raw/inspect-validation.tar.gz): `4371cdf60861ea4f7c9c4459400a507f0cea7c07422cc92f5bc1925316a75e6b`
- [inspect-span-production-bench-7ad863391bb7.tar.gz](raw/inspect-span-production-bench-7ad863391bb7.tar.gz): `05d5f3bd3553f1d37d41a7ab04e1b17ebd7215fe3f2e9842c9712aa433ad61cd`
- [inspect-span-production-bench-7ad863391bb7-repeat.tar.gz](raw/inspect-span-production-bench-7ad863391bb7-repeat.tar.gz): `d28f22aea74f0b40514cb5e44266017397a1f04d3b34235843e55511fae8264b`
- [inspect-span-production-records-7ad863391bb7.tar.gz](raw/inspect-span-production-records-7ad863391bb7.tar.gz): `19203a1258091b2e85cd8854dcff19cd4a766eb3f5c6542e1e42663a56d91e29`
- [inspect-span-production-records-7ad863391bb7-repeat.tar.gz](raw/inspect-span-production-records-7ad863391bb7-repeat.tar.gz): `3e83ab326848f7bd969ae78e50627f3181c077fdc9f892fe78741d17e2908d7a`
- [inspect-span-validation.tar.gz](raw/inspect-span-validation.tar.gz): `e787d619a4a907de7cbbab51d22022aa407ae281d438496baa1056aabb6145fe`

- [typed-compare-production-bench-802ae51122d7.tar.gz](raw/typed-compare-production-bench-802ae51122d7.tar.gz): `7287fe65a4929b797a9cf8bfded4554a8d8962bed7de31c7bff0a1b98f77fc61`
- [typed-compare-production-records-802ae51122d7.tar.gz](raw/typed-compare-production-records-802ae51122d7.tar.gz): `635fece8c60beb74e0734d3c193332dc0e313aaeb93682fe272ec56f3d714c52`
- [typed-compare-validation.tar.gz](raw/typed-compare-validation.tar.gz): `faa3a33523a914c8dcc00dcfa830f3da22f287e5fa8021de580b898c4cae34e5`
