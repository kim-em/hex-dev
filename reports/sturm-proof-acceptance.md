# Sturm proof acceptance

HexSturm and HexSturmMathlib satisfy the [Phase-5 criteria](../PLAN/Phase5.md):
complete proofs, a successful build on the pinned toolchain and passing
conformance. Both counters are 5. The owner Phase-4 attestation is merged in
[#10860](https://github.com/kim-em/hex-dev/pull/10860); its
[readiness matrix](real-closure-prerequisites.md) and
[performance report](hex-sturm-performance.md) retain evidence and limits.
This acceptance does not advance Phases 6 or 7 or establish publication eligibility.

## Build and conformance

A full monorepo `lake build` passes on `leanprover/lean4:v4.35.0-rc3`.
The focused command also passes:

```sh
lake build HexSturm HexSturmMathlib HexSturmMathlibTests \
  +HexSturm.Conformance \
  +HexSturmMathlib.Tests.Replay.Semantics \
  +HexSturmMathlib.Tests.Replay.SemanticsBaseline
```

The computational conformance checks actual ordinary/prepared queries, root
counts, certificates, cached/plain replay, endpoint retargeting and positive
certificate transport. It includes constants, invalid domains, repeated heads,
noncanonical storage, changed literal bindings and corrupted evidence. Its
integer/field comparisons are differential controls; they do not replace the
ordinary-kernel semantic proofs or the shared integer owner's exact oracle.

The companion tests apply domain/query contracts to canonical and noninjective
coefficient storage and accepted/rejected literal replay. Semantic replay and
root-count guards build through the existing adapter test modules. Their axiom
inventories admit only `propext`, `Classical.choice` and `Quot.sound`.
The named-admission and published trust checks pass; there are no sorries,
new axioms or `native_decide` in the completed production claims.

## Scope and remaining work

The [declaration assessment](sturm-declaration-review/README.md) covers the
48 computational and 78 companion handwritten production declarations.
Phase 5 requires proof completion rather than a new implementation or repeated
performance measurements. No Lean source changes accompany these counters.

Phase 6 still requires final lint/docstring/use acceptance and the computational
comparison against the prescribed committed benchmark baseline. The existing
[manual chapter](../HexManual/Chapters/HexSturm.lean) does not bypass that gate.
The [publication plan](real-closure-publication.md) retains companion dependency
pins, split fixtures, candidate consumer checks and external distribution
requirements. Real-algebraic and rank Phases 5–7 remain outside this pair's scope.
