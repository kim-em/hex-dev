# Bounded scans of zero coefficients

The selected implementation `f3d5acec8365`, measured commit `94e3d7662e`,
checks for a block only after encountering a zero coefficient. It skips eight
zero entries within the active interval, remaining quantum and already-reserved
work. The loop consumes eight logical ticks. It preserves every portable state,
error prefix, trace and counter. Nonzero entries follow the existing path.
The content-preserving rebase onto merged `99e2c77b` has the same source family.

One-byte packets use an unaligned-safe word copy, two-byte packets use SSE and
four-byte packets use AVX2. Runtime dispatch still protects unsupported hosts.
`last < columns` and `charged > column` hold before the packet check, so the
active-interval bound also proves the complete load lies in the logical buffer.
No speculative read crosses a work, quantum or active-range boundary. Skipping
zeros does not inspect or validate unreachable pivot slots.

The baseline is `b1e96ea920dd`, the dedicated Mersenne-dispatch implementation.
Its executables are byte-identical to timed `d1278bde9bd5`; the retained baseline
manifest includes the equivalence check. Both arms use identical benchmark
sources and complete-output consumption. All measurements use automatically
leased CPUs on the shared host, adjacent AB/BA order and one thread. Every
completed sample, failure and outlier is retained. Each source snapshot has
one AB/BA campaign; no unchanged implementation is repeated.

## Matrix kernels

The full declared 32/64/128/256 ladders retain 96 points per implementation,
with three outer trials, 0.5-second inner targets and 8-second call caps. Every
complete output hash matches. Spread-support inputs perform quadratic active
interval scans after cancelling to zero; sparse-pivot inputs exercise linear
stored-entry work. Eight-entry packets improve constants without changing
these operation-count models.

The initial `71a43c11998a` snapshot considers packets before reading the current
coefficient. Its sparse-kernel regressions motivate the conditional version.
The snapshots are different compiled implementations: the initial version
checks before reading a coefficient; the selected version checks only after a
zero. Their timings are not pooled, and the second is not an unchanged rerun.

| Size | Initial spread mean B/A | Initial sparse mean B/A | Selected spread mean B/A | Median | Range | Selected sparse mean B/A |
| ---: | ---: | ---: | ---: | ---: | --- | ---: |
| 32 | 0.6464 | 1.0270 | 0.5988 | 0.5988 | 0.5917–0.6047 | 1.0056 |
| 64 | 0.5118 | 1.0318 | 0.4621 | 0.4629 | 0.4547–0.4694 | 1.0140 |
| 128 | 0.3995 | 1.0827 | 0.3389 | 0.3349 | 0.3314–0.3506 | 0.9430 |
| 256 | 0.3207 | 1.0276 | 0.2603 | 0.2600 | 0.2583–0.2627 | 0.9545 |

Kernel CPUs are 63 initially and 45 for the selected version. Four initial
spread fits and seven selected fits are inconclusive; none is budget-truncated.
These are finite-size kernel observations, not a full-system improvement or
leadership claim. Sparse medians, ranges, fits and every point are retained.

## Complete F4 systems

Candidate time includes canonicalization, F4 and final interreduction. Process
time additionally includes startup, parsing and full-output serialization.
All 64 diagnostic processes per snapshot have matching full bases and every
non-timing counter. Initial candidate mean B/A is 1.0068, median 1.0003,
range 0.9083–1.3416 on CPU 17. Selected candidate mean is 1.0125, median
0.9941, range 0.8261–1.6680 on CPU 46. Selected process mean is 0.9122,
median 0.9939, range 0.1743–3.1857. These variable results do not establish
an overall F4 speedup.

All 120 fixed points per snapshot have matching full hashes. The selected
means on CPU 48 are 1.0071 cyclic4, 1.0015 cyclic5, 0.9383 cyclic6,
1.0091 katsura3, 1.0080 reimer5 and 0.8661 cyclic6Small. Medians are
1.0058/1.0032/0.9814/1.0064/1.0030/0.9682. The initial implementation uses CPU 67 with means
1.0125/1.0249/0.9028/1.0010/1.0097/0.8941 in the same case order. Both source
snapshots and every outlier remain in separate analyses. These are distinct
implementations, with no unchanged rerun or discarded sample.

## Validation and provenance

The selected 331-job core/benchmark/emitter build and 1928-job theory/F4/basis/
kernel-replay build pass. All 175 matrix, 567 independent SymPy/Singular basis
and 1288 division oracle cases pass, along with 32 benchmark verification cases
and project DAG/phase/manifest/header/line/admission checks. Four Clang and four
GCC ASan/UBSan variants pass. The instrumented F4 window records 139 actual
zero packets in aggregate. The arithmetic-update tests separately cover
eight vector paths (mask 255); that mask does not classify zero packets.

Additional tests check every byte of each packet, guard pages at both ends,
all 32 alignments, shared buffers, invalid coefficients and unreachable invalid
slots. Quantum/work boundaries at 7/8/9, 15/16 and 63/64/65 preserve every state
field and error prefix. No new theorem admission or native_decide is introduced.

Archives are authoritative source snapshots; commit references are supplementary.
They retain both complete source families, compiled-driver source, executable
hashes, measurement and analysis scripts, raw samples and all output comparisons.
SHA-256:

- [zero-scan-kernels-71a43c11998a.tar.gz](raw/zero-scan-kernels-71a43c11998a.tar.gz): `f388443d08053390429ff31d4562a7facb6fe4270b8db5f02a7b93eec3139b4e`
- [zero-scan-production-bench-71a43c11998a.tar.gz](raw/zero-scan-production-bench-71a43c11998a.tar.gz): `2d1153e30efcdb33309074f0ef1c6281aaa4b6a98bf9fffaf7715d686f3c40ae`
- [zero-scan-production-records-71a43c11998a.tar.gz](raw/zero-scan-production-records-71a43c11998a.tar.gz): `ef0c1a3292cc39e4e004f578321823343f5b168c3d3302b04ff50bad77c8824a`
- [zero-branch-kernels-f3d5acec8365.tar.gz](raw/zero-branch-kernels-f3d5acec8365.tar.gz): `1d3b69bc62361ef68f3e991aa832e9d155b452de59ec68d9f0be63df3ec1f50d`
- [zero-branch-production-bench-f3d5acec8365.tar.gz](raw/zero-branch-production-bench-f3d5acec8365.tar.gz): `29a86f35300f58c1618f2970b4701ae6e6002988715b200dfdf01b0da3d8043a`
- [zero-branch-production-records-f3d5acec8365.tar.gz](raw/zero-branch-production-records-f3d5acec8365.tar.gz): `11b97087951c79c662ef539853196132b76ac34b0666ec293bc83de4d786c5a2`

- [zero-scan-validation.tar.gz](raw/zero-scan-validation.tar.gz): `84e83a61ac806df7def6a4fde2f544fb42e9f8f6a08f07da5bcf5f16f7a893f8`

The final boundary tests enumerate all eight starting offsets and reservations
independently of environment seeds. They also use short active intervals with
work reserved beyond their ends and an aliased buffer case that actually writes.
Four sanitizer variants per compiler pass. Isolated C copies with either the
reservation guard or the active-interval guard removed fail at the new boundary
check. Production source family `f3d5acec8365` remains unchanged.

[zero-scan-boundary-validation.tar.gz](raw/zero-scan-boundary-validation.tar.gz), SHA-256 `94bc9fdf3d479cd9fac9efb8951f5b50899633b0848b6c3f973c67956fffbfd9`.
