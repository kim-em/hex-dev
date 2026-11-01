# Bounded packed monomial comparisons

`MonomialTable.compare` and `divides` retain their cached degree and support-mask
filters and perform the remaining coordinate comparisons in a borrowed native
call. It handles lexicographic, reversed lexicographic and pointwise comparison
for one-, two- and four-byte exponents, with at most 4096 coordinates. Stable
IDs, storage, field arithmetic, scheduling and resource counters are unchanged.
Larger arities and unsupported shapes use the original portable loops.

Arbitrary-precision indices are bounded before conversion to the u64 ABI. The
current implementation checks complete accessed row spans;
`(max(id)+1)*arity*width ≤ 2^46`, so validation cannot overflow even on 32-bit
hosts. Unused partial trailing rows require no access. Calls mutate no storage
and retain no pointers. The pure bodies remain available to the kernel.

Source fingerprint `802ae51122d7`, commit
`e896a5bcea7891a0a501d196c6621db52286304f`, exposes typed `Native.Monomial.compare`
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

Both arms use identical drivers and benchmark sources. The 16-input development
suite covers seven families at primes 32003 and 2147483647. Each input runs
adjacent AB then BA, one thread on an automatically leased CPU. Complete reduced
bases and every non-timing counter agree. All completed samples and outliers are
retained. Candidate time includes canonicalization, F4 and final interreduction;
process time adds startup, parsing and complete output. Certificate generation,
independent final certification and kernel checking are excluded. This is a
development suite, not a held-out or fastest-open-source acceptance suite.

The baseline is source fingerprint `f3d5acec8365`, the
[bounded zero-scan implementation](https://github.com/kim-em/hex-dev/pull/11002).
Earlier source fingerprints `03abfd63909b` (whole-arena geometry) and
`7ad863391bb7` (accessed-row spans) have separate archives below. The latter
used its one permitted unchanged repeat after an inconclusive observation;
both campaigns and their outliers remain included in its archived analyses.
Those observations, including a cyclic6Small fixed-case regression, are not
pooled with the current implementation. Accessed-span semantics are selected
because they validate exactly the bytes read by the portable loops and avoid
division. Separate campaigns do not establish which geometry variant is faster.

Clang and GCC pass all four ASan/UBSan variants. Standalone tests check 2700
array-oracle cases, maximum coordinates, read-only guard pages at both ends,
truncated rows, invalid indices and opcodes. Compiled tests compare every
native result with portable behavior and independent list order/inequalities,
including distinct arity-4096 rows, oversized left/right Nat inputs and unused
trailing bytes. Table-level tests compare all three orders with `TermOrder.cmp`
and divisibility with integer inequalities across u8/u16/u32 storage and arity
4096/4097, exercising the portable dispatch as well as native calls. The current
compiled window records 23724 calls and 4485 declines across all positive and
malformed primitive/table cases. Its F4 window accepts 3553 native answers and
declines zero. The harness requires positive accepted F4 work with zero declines.
Matrix arithmetic mask 255 and zero-packet counters remain separate.
The 1950-job relevant library/theory conformance build, independent 175 matrix,
567 basis and 1288 division checks, and all 32 fast benchmark checks pass.
Their operational duration is not scientific timing evidence.

Archives retain exact source manifests and Git blobs for both arms, executable
hashes, full outputs, samples, memory, failures, analysis, compiler identity and
validation logs. All twelve archive hashes and 2794 source blobs were
verified against the recorded Git IDs. The measured current source is identical
to the production source after the later conformance-only coverage changes.

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

- [monomial-comparison-final-coverage.tar.gz](raw/monomial-comparison-final-coverage.tar.gz): `99104ed5f9df161dcd85fc07e09b0a27141cebf2127939b395a3502464c9b93d`
