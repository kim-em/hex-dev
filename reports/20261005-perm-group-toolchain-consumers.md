# Permutation-group toolchain consumers

Fresh Mathlib-free consumers of the staged HexBasic and HexPermGroup packages
build on both a Lean nightly and a Lean PR toolchain. Each consumer has exactly
two dependencies, `hex-perm-group` and `HexBasic`, both supplied by local paths.

| Toolchain | Compiler commit | Core tests and emission | Independent source replay and Basic boundary tests |
| --- | --- | --- | --- |
| `leanprover/lean4-nightly:nightly-2026-10-04` | `ef8e00518ce26d4cd902c81fec2daad5230840da` | Pass, 304 jobs | Pass, 298 jobs |
| `leanprover/lean4-pr-releases:pr-release-15471-d81678a` | `d81678af187fae05d0b481f990dbaf35f02e0fae` | Pass, 304 jobs | Pass, 298 jobs |

The PR toolchain is an iteration of
[Lean PR #15471](https://github.com/leanprover/lean4/pull/15471).
The consumers import `HexPermGroup.ImportTests`, `HexPermGroup.Tests` and
`HexPermGroup.CertificateTests`. They cover all four goal forms, false goals,
M11 order and transposition non-membership, rollback, canonical witnesses,
namespace boundaries and the standard axiom checks. A separate emitter writes
the order proof for the symmetric group on three points; a subsequent
`lake build` compiles that source. Basic's module-boundary tests are also built
explicitly.

The packages were generated from candidate `f2e746c8c359` using the guarded
release staging machinery. Their source trees are:

- `HexBasic`: `37753d2a2843743fcaa415d1cd2b32cf08ef3602`;
- `HexPermGroup`: `f373b7873e5ca6cd48364667f5f889ea8f049ce1`.

Each toolchain stage preserves all 149 published Lean source files byte for
byte. Only the toolchain files and Lake dependency configuration change: the
core package requires the sibling Basic package, and the consumers resolve
both packages from scratch. The emitted replay module is compiled after its
emitter has created it.

These checks establish compatibility with the two specified compilers. They
do not exercise registration in `downstream-lean4`, automatic adaptation
exports or the return of mirror adaptations to hex-dev; those remain separate
prerequisites for the Mathlib dependency.
