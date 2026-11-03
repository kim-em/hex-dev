# F4 matrix target and reduction counts

The driver and library expose submitted matrix targets, completed pivot
applications and zero rows. A shared `Statistics.recordMatrix` merges these
counters for traced and untraced production, including consumed prefixes of
failed calls. Submitted rows include retried atomic stages; these are counts
of attempted work, not distinct polynomial identities.

Source fingerprint `b6822c6a5f65` identifies the frozen
driver source at `285a8a09902b81731fcedf14af06499091724b0d`. The 14-input medium development
suite is run once for untimed diagnostics. Complete bases and every previous
metadata/counter field agree with retained `fd0313c0ed28` outputs. The three
new fields are the only additions. The raw `candidateNanos` values are retained
but no timing, speedup or acceptance claim uses these executions.

The external `F4.step` runner separates input normalization, pair rounds and
final interreduction. Its complete bases and all five matrix counters match
the separately built candidate driver from the same runtime source; final interchange decoding work is
absent from that runner and is not equated. All stage source/build records
are retained. Eco11 M31 stage data has collector-level binary/source identity,
without a separate per-run binary attestation. Aggregate zero fractions mix these different stages and do not
predict the rank of an individual sampling block.

| Case | All targets | All zero rows | Pair-round targets | Pair-round zero rows | Pair-round zero fraction | Pair-round pivot applications |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| cyclic7-15 | 2828 | 2027 | 2612 | 2027 | 77.60% | 626662 |
| cyclic7-31 | 2828 | 2027 | 2612 | 2027 | 77.60% | 626678 |
| kat8-15 | 457 | 307 | 375 | 307 | 81.87% | 127142 |
| kat8-31 | 457 | 307 | 375 | 307 | 81.87% | 127144 |
| eco11-15 | 3708 | 2831 | 3308 | 2831 | 85.58% | 5803858 |
| eco11-31 | 3708 | 2831 | 3308 | 2831 | 85.58% | 5803981 |
| noon5-15 | 339 | 195 | 262 | 195 | 74.43% | 6832 |
| noon5-31 | 339 | 195 | 262 | 195 | 74.43% | 6832 |
| reimer6-15 | 767 | 468 | 666 | 468 | 70.27% | 154435 |
| reimer6-31 | 767 | 468 | 666 | 468 | 70.27% | 154435 |
| minrank_d_2_p_2_q_4_r_2-15 | 45 | 15 | 24 | 15 | 62.50% | 593 |
| minrank_d_2_p_2_q_4_r_2-31 | 45 | 15 | 24 | 15 | 62.50% | 593 |
| quadratic6-15 | 201 | 123 | 156 | 123 | 78.85% | 10874 |
| quadratic6-31 | 201 | 123 | 156 | 123 | 78.85% | 10874 |

Eco11 at the largest prime has 2831 zero reductions
among 3308 pair-round targets. Its
389 final-interreduction targets have
0 zero rows. These observations identify a
concrete candidate for a block-sampling experiment. They establish neither a
sampling success probability nor a speedup; no sampler is implemented here.

All 9 project checks pass at `983eb622ba4d651c7c5a0b7256d96bf0e37e7b75`. At
`285a8a09902b81731fcedf14af06499091724b0d`, all 9 project checks and 8 source-identified
Clang/GCC sanitizer/SIMD/scalar/remainder variants also pass. The reviewed emitter verifies
traced/untraced and native/portable counts on 1,134 profiles, and the regenerated
fixtures preserve every pre-existing field. All 2 complete driver corpora pass.
The hand-checkable matrix with reducer `x` and targets `1,x` has two targets,
one pivot application and one zero row. Its additional work-exhaustion guard
retains that completed reduction/zero prefix at conformance commit
`983eb622ba4d651c7c5a0b7256d96bf0e37e7b75`, command `lake build HexGroebner HexGroebnerTheory HexGroebner.BasisConformance HexGroebner.BasisReplayConformance HexGroebner.ByteConformance HexGroebner.CertificateConformance HexGroebner.CertificateProducerConformance HexGroebner.ColumnMapConformance HexGroebner.Conformance HexGroebner.DivisionAPIConformance HexGroebner.DivisionConformance HexGroebner.DivisionFixtures HexGroebner.EliminationConformance HexGroebner.EliminationReplay HexGroebner.F4Conformance HexGroebner.F4Fixtures HexGroebner.Fixtures HexGroebner.GatherConformance HexGroebner.HitConformance HexGroebner.MatrixLayout HexGroebner.MatrixNativeConformance HexGroebner.MatrixPrimitiveConformance HexGroebner.MatrixStateConformance HexGroebner.MatrixStateReplay HexGroebner.MembershipConformance HexGroebner.MonomialCompareConformance HexGroebner.MonomialConformance HexGroebner.NativeChecks HexGroebner.NativeConformance HexGroebner.NormalFormConformance HexGroebner.PackedWordConformance HexGroebner.PairRowsConformance HexGroebner.PolynomialBatchConformance HexGroebner.ProducerConformance HexGroebner.ProductBatchConformance HexGroebner.ProductConformance HexGroebner.ReducerCacheConformance HexGroebner.ReducerConformance HexGroebner.ScanConformance HexGroebner.SchedulingConformance HexGroebner.SchedulingResumeConformance HexGroebner.SearchConformance HexGroebner.TraceConformance HexGroebner.TrieConformance hexgroebner_compute hexgroebner_compute_full hexgroebner_emit_f4 hexgroebner_emit_division hexgroebner_emit_fixtures hexgroebner_bench` (exit 0).
Four additional traced guards retain consumed reduction/zero prefixes when trace
capacity is exhausted, across joint/independent and native/portable calls. A fresh
build at reviewed runtime fingerprint `ff6634c1918f` produces
both driver executables byte-identically to the frozen diagnostic drivers.

The [count-report generator](../../scripts/bench/groebner_count_report.py)
rechecks the old output fields, raw diagnostic counts, stage sums and complete
bases before generating this table. Every input consumed from unpacked paths is byte-bound to a capsule member,
and every payload digest is verified before analysis. The guard command and
its complete log are read from a separate verified capsule. The historical
source identifiers are bound through the retained source patch, tree hashes
and blob manifest.
Candidate production, certificate generation, native verification and kernel
checking remain distinct. This change makes no performance milestone claim;
issue #10987 remains open.

[Raw matrix-count capsule](raw/f4-matrix-counts-b6822c6a5f65.tar.gz): SHA-256
`d10192c5af478079b4222a7781e1c50fc6826d918ca6800c20c1a5d6776dd346`, 302 data payloads, each read back and digest
checked, plus the digest manifest. The raw comparison outputs come from the previously retained
[combined campaign](hexgroebner-combined-performance.md), SHA-256
`ceb95beadbc9cc4e7e7eae24345b5d05ba6c5fee819056ee8db176d90d474373`. The separate guard capsule is
[guard validation](raw/f4-matrix-counts-review-983eb622ba4d.tar.gz), SHA-256 `2535cd85ef911a328fd8750707d0b77c4789958e553bc6337fc202c40eea6f9c`.
