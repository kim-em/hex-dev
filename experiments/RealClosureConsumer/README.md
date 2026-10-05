# Ordinary-import real-closure consumers

This separate Lake project requires the local monorepo and imports its
[`RealClosureConsumer` examples](../../examples/RealClosureConsumer) through
[`Consumer.lean`](Consumer.lean). It does not define a second provider of those
modules. It prepares
consumer examples for [#10575](https://github.com/kim-em/hex-dev/issues/10575) without moving active owners' adapter modules.

From the monorepo root:

```sh
lake build RealClosureConsumer
```

From this directory:

```sh
lake update
lake build
```

The separate project's lock is generated locally and is not committed. Its
Hex requirement is the local path `../..`; the root `lake-manifest.json` fixes
the external revisions listed in the
[package inventory](../../reports/real-closure-package-inventory.json).
The consumer has its own external package checkouts, lock and build directory.
As with any local Lake path dependency, Hex itself builds in the monorepo
build directory; run these two projects sequentially. Run `lake update` after changing root dependency pins; it also
refreshes the toolchain selected by the local Hex dependency. This is a local
downstream-style project, not validation of staged split packages or
release-sync output.

| Module | Ordinary imports and claim |
| --- | --- |
| `Query` | `HexSturmMathlib`, `HexRealRootsMathlib`; the real-roots umbrella proves arbitrary integer-certificate root sums; the exact `query_iff` characterizes producer success and value; accepted field certificates establish domain and root sum, prepared counts equal distinct-root cardinality, and a rational producer guard accompanies a conditional ℚ → ℝ interpretation theorem |
| `Sign` | `HexSignDetMathlib.ThomRoots`, `HexRealRootsMathlib.RealClosed`; valid-domain production finds each real root, preserves both directions of coverage, and returns distinct descriptors in strict order |
| `Ordered` | `HexOrderedFnMathlib`; the next infinitesimal is positive and below every power of its predecessor |
| `Tower` | `HexRealClosureMathlib.TowerRoots`; in a supplied common model, native nonzero root production succeeds with exact coverage, multiplicities and strict order |

The root default build and existing CI build include the same consumers. Exact `#print axioms`
guards permit only `propext`, `Classical.choice` and `Quot.sound`. These are
proof/API composition checks; there are no new performance measurements or
claims of joint ordinary-real realization. Optional tactic examples remain
owned by [#10358](https://github.com/kim-em/hex-dev/issues/10358) and are reused from `conformance/HexRCF/TotalAlgebraicProofs.lean`
and `ProductionProgress.lean`. Merged #10668 also supplies
`PreparedCoefficients.lean`, `FiniteReplay.lean` and fresh
`bench/HexRCF/ProofProbe/Prepared` examples (removed from `main` after commit
`45a4e4e9a4`); reuse their original
source modules and exact axiom guards for preparation/frozen replay. The [local candidate experiment](CANDIDATES.md) additionally builds these
examples against exact Git-pinned package trees. Exploration acceptance and
full release-sync consumer validation remain in the
[publication plan](../../reports/real-closure-publication.md).
