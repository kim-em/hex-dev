# Sparse-support phase costs

These mode-1 registrations in `bench/HexSignDet/Phases.lean` separate the
actual operations identified by the sparse-support production profile. They
use the same checked `P=X²−1`, repeated-`X` input family and six fixed trials
at `s=64,128,256,512,1024,2048`. The [family derivation](sign-det-sparse-model.md)
establishes `2s−1` nodes, `7s−4` query slots, bounded matrix dimensions and
scalar sizes, and balanced-tree arity volume `s(log₂s+1)`.

Fixture preparation retains actual nodes, prepared query representatives
and remainder coefficients outside the timed bodies. Every operation returns
an optional hash; missing prepared input or an internal solver failure has
a different result from the expected successful output. Inspection binds
query values, reduced representatives and solved counts to the checked
literal tree. Matrix outputs reuse the already validated upstream matrix
operation. Coefficient signs are checked against rational numerator signs.
This validates benchmark outputs without claiming a new root-semantics proof.

| Registration | Declared model | Timed operation and derivation |
| --- | --- | --- |
| `runQueries` | `s` | `Sturm.certifyPrepared` at each actual moment representative. All `7s−4` calls have bounded polynomial degree and coefficient size. |
| `runProducts` | `s * (Nat.log2 s + 1)` | `nodeReduction` on each actual node row, using retained query preprocessing. A node of arity k scans Θ(k) exponent slots, with at most two nonzero factors per row. |
| `runMatrices` | `s * (Nat.log2 s + 1)` | `momentMatrix` at every node. Matrix dimensions are bounded, but each integer entry scans its length-k sign/exponent words. |
| `runSolvers` | `s * (Nat.log2 s + 1)` | The actual rational leaf solver and scaled parent solver, including `System.check`. Scalar solves have bounded dimensions and sizes; their checks construct matrices and scan length-k slots. |
| `runSigns` | `s` | `Sturm.orderSign` on the actual stored remainder coefficients. There are Θ(s) bounded-size coefficients. Mapping and result hashing also cost Θ(s). |

The operations are not disjoint buckets: solver checks include matrix
construction, and prepared queries include coefficient-sign work. Their
times must not be summed as a decomposition of production. In particular,
`runSolvers` is not advertised as pure matrix inversion time, and this
rational sign family does not measure extension-level sign search.

The same runner retains all raw samples, validates the exact schedule and
expected hashes, records the harness verdict without changing its model,
and leases a CPU without any host-idleness test. Use
`python3 scripts/bench/sign_det_sparse.py --components --output NEW_DIRECTORY`.
No measurement or Phase-4 completion is claimed by the registrations alone.
Maximal support, degree/bit/witness growth, nested evidence, comparisons,
descriptor operations, allocation/serialization sizes and proof checking
remain separate required coverage.

## Retained measurements

[Raw samples and provenance](data/sign-det-phases/95ef4e489/metadata.json)
record clean source `95ef4e489`, the same pinned LeanBench revision as the
end-to-end schedules, and the automatic CPU lease on shared host `chungus2`.
All 180 timed samples completed with the expected hashes and exact schedule.
Every mode-1 verdict is **consistent with declared complexity**; no sample
was discarded and no rerun was used.

| Registration | Median at s=64 | Median at s=2048 | Normalized slope |
| --- | ---: | ---: | ---: |
| `runQueries` | 2.301 ms | 75.806 ms | 0.013968 |
| `runProducts` | 0.693 ms | 27.740 ms | -0.075676 |
| `runMatrices` | 0.453 ms | 27.190 ms | 0.033356 |
| `runSolvers` | 1.644 ms | 64.972 ms | -0.079357 |
| `runSigns` | 0.031 ms | 1.293 ms | 0.082709 |

The fixture inventory contains 444–14,332 prepared-query calls and
2,284–73,708 stored coefficient-sign operands across this range. Query work
tracks node count while matrix construction reflects sign-word lengths as
well. The solver includes the matrix checks described above; the separate
figures therefore overlap. These host-specific observations are not an AB/BA
comparison and do not establish a speedup. Allocation bytes remain unavailable
in these exports, and all additional coverage gates listed above remain open.
