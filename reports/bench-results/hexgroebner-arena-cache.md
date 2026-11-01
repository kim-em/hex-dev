# Exact current-arena reducer cache validation

Cached rows now validate every product exponent against the current monomial
arena before reuse. Byte-equal IDs from another arena cannot return a stale row,
even if the base and multiplier retain their meanings while a result ID changes.
The final combined cache/read/lookup implementation has diagnostic candidate
B/A geometric mean **0.8809**, median **0.9007**, against the pre-cache native
engine. All six registered fixed cases have geometric means below one; one
Katsura3 point regresses. These finite observations do not establish performance
leadership or a universal gain.

## Exact behavior

A hit requires equal field/variable/order metadata, the complete base support
and coefficients, and exact identities
`exponent(result[i],j) = exponent(base[i],j) + exponent(multiplier,j)` for every
term and variable. Hashes are never used as equality proofs. Products pass
coefficients through unchanged, and fresh certificate derivations use the
current basis. This validates basis/arena compatibility directly, including
public raw cache entry points, without retaining an arena buffer alias.

The borrow-only native checker validates geometry and the complete slice before
support reads, then each identifier before coordinate reads. It compares at most
4096 exponent coordinates per call.
Little-endian reads make no alignment/byte-order assumption. UInt64 sums of
u32 coordinates cannot overflow; a sum exceeding u32 cannot equal a stored
coordinate. Count/stride multiplication and slice endpoints are checked before
pointer arithmetic. Both portable and native routes have the same rejection
contract. Larger arities use the ordinary exact Lean exponent loop. Comparison
work consumes the parent allowance before validation; no rejection bypasses
its accounting or falls back with an uncharged retry.

At most 16384 keys remain. A full cache can replace an existing key, so stale
entries do not permanently block its updates. Every insertion, including a
replacement, reserves eight logical bytes cumulatively; shared base/product
buffers retain their existing charges. Peak occupancy of the timed inputs was
not instrumented. Sugar and derivations remain fresh, and final certification
independently proves the complete reduced-basis contract.

## Validation

The final `lake build` passes 14203 jobs across implemented libraries, theory,
conformance, benchmark and emitters. Independent oracles pass 175 matrix,
567 SymPy/Singular reduced-basis and 1288 division/normal-form/membership cases.
All 30 benchmark verifications and DAG, phase, release-manifest, source/header
and admission audits pass. Kernel examples reduce the portable product checker
with `decide +kernel`; no native_decide or new axiom is introduced.

Cross-arena tests cover both changed base meanings and changed result meanings
with unchanged base/multiplier semantics. Dynamic runtime tests cover coefficient-
only changes, field/order changes and exponent-width widening. Long rows have
4200 terms, deterministic coefficient mismatches at offsets 4096, 4150 and 4199,
a support mismatch at byte 6000 and another in the final partial support chunk.
A capacity test fills 16384 keys, replaces one, verifies its subsequent allocation-
free hit, and checks that a new key remains uncached at capacity.

All four SIMD/scalar and Barrett/remainder variants pass with Clang 23 and GCC 16,
ordinarily and under ASan/UBSan. Each records 4078 byte comparisons and 205
product validations. Independent counter windows require both primitives to
run during real F4 and during cache checks. Standalone C and portable/native
comparisons cover all exponent widths, the 4096-coordinate bound, aliases,
malformed geometry, large arguments and final-coordinate mismatches. Sanitizers
instrument C, and portable equality/range checks remain separate obligations.

Compared with main, 326 F4 fixture cases change only work fields: `work` in 326,
`serialWork` in 326 and `referenceWork` in 325. Every basis, input and other field
is equal. These changed charges can exhaust a tight allowance that previously
succeeded; resumptions keep their existing absolute cumulative budget semantics.

## Frozen matched measurements

B is fingerprint `65d5517c4d57`, computational commit `a74d092a08`. A is the
frozen narrow-field SIMD engine `04e1c0a5f392`, before reducer caching. Both
executables are frozen before timing. Host chungus2, AMD EPYC 9455, Lean 4.35.0-rc3,
generated C Clang 23.1.0 and FFI Clang 23.1.3. One computation thread pins to an
automatically leased CPU. Arms run adjacent AB then BA. Every completed point,
regression and outlier is retained, with no quiet-host condition or discarded
sample. There are no failures or timeouts and no unchanged rerun in this source
snapshot's experiments.

The 16-case diagnostic suite is cyclic5/6, Katsura6, Eco10, Noon4, Reimer5,
MinRank and fixed quadratics over 32003/2147483647 in grevlex. Suite SHA-256:
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
It is neither family-balanced nor held out. Each process has ten seconds and
16-GiB address space. Candidate time includes canonicalization, F4 and final
interreduction; process time also includes startup, parsing and complete output.
Certificate generation, independent certification and kernel checking are excluded.
All 64 processes complete and all 32 full-basis comparisons and non-resource
counters agree. Work/allocation differ from A because of the cache.

Diagnostic CPU 93: candidate geometric mean/median 0.8809/0.9007,
range 0.7156–1.0839; process geometric mean/median 0.9278/0.9613,
range 0.3314–3.5931. Process dispersion remains large and
does not isolate startup or conversion costs.

Registered fixed cases have 120 completed points (ten paired ratios per case),
five declared repetitions, and equal full structural basis hashes. Totals are
normalized by actual inner repeats. Preparation is excluded; canonicalization,
F4, final interreduction and full output consumption are included. Modulus is
65537, except cyclic6Small at 32003.

| Case | Geometric mean | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.9772 | 0.9824 | 0.9469–0.9876 |
| cyclic5 | 0.9478 | 0.9504 | 0.9110–0.9683 |
| cyclic6 | 0.9125 | 0.9129 | 0.9056–0.9197 |
| katsura3 | 0.9612 | 0.9458 | 0.9189–1.0387 |
| reimer5 | 0.7185 | 0.7146 | 0.7120–0.7562 |
| cyclic6Small | 0.9147 | 0.9146 | 0.9068–0.9229 |

Fixed-case CPU is 43. Katsura3 includes one 1.0387 ratio; it remains.
The earlier guarded-cache [campaign](hexgroebner-hotloop.md) has an unexplained
fixed cyclic6 regression, retained with its two complete experiments and cost
profiles. It does not recur in this later source snapshot. Changes in source
and execution context prevent attributing the difference to the arena checker.
Neither campaign replaces or invalidates the other.

The final source has no fresh external comparator sweep here. The preceding
reports retain a substantial msolve gap; the SPEC's fastest-open-source,
family-balanced, held-out and parallel acceptance remains open. No evidence
establishes that language or runtime changes are necessary before further gains.

## Reproduction and retained evidence

Archives retain exact staged source manifests/blobs, driver sources, frozen
executable hashes, commands, CPU/toolchain context, raw outputs, memory, all
samples, comparisons and analyses. Overlay `root-sources` on the recorded
baseline, point the archived Lake driver at that checkout, and build
`production_compare`; fixed cases use `hexgroebner_bench`. SHA-256:

- [arena-production-bench-65d5517c4d57.tar.gz](raw/arena-production-bench-65d5517c4d57.tar.gz): `fe2d6a7e1d59346b2b8c7e27e260ad78808f69501bda07096ca401d6e246a25c`
- [arena-production-records-65d5517c4d57.tar.gz](raw/arena-production-records-65d5517c4d57.tar.gz): `b71bf69c6f7893ba50b1b4f0f7c0e120ec82fda7de9fcb7132214f87e4e9e874`
- [arena-cache-validation.tar.gz](raw/arena-cache-validation.tar.gz): `f6d160b6fa4d1040f2ebb86a1c1caff49300a65ad7f17f16184973e296ca4535`
