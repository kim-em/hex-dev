# Ordinary-import real-closure consumers

This separate Lake project requires the local monorepo and compiles sources in
[`examples/RealClosureConsumer`](../../examples/RealClosureConsumer). It prepares
consumer examples for #10575 without moving active owners' adapter modules.

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
External package sources/caches are shared with the root project; the consumer
has its own Lake build directory. This is a local downstream-style project,
not validation of staged split packages or release-sync output.

| Module | Ordinary imports and claim |
| --- | --- |
| `Query` | `HexSturmMathlib.Soundness`, `HexRealRootsMathlib.RealClosed`; accepted arbitrary certificates establish both domain and shared Tarski root sum, and prepared counts equal distinct-root cardinality |
| `Sign` | `HexSignDetMathlib.ThomRoots`, `HexRealRootsMathlib.RealClosed`; valid-domain production finds each real root in an actual selected descriptor and orders the returned list |
| `Ordered` | `HexOrderedFnMathlib`; the next infinitesimal is positive and below every power of its predecessor |
| `Tower` | `HexRealClosureMathlib.TowerRoots`; in a supplied common model, native nonzero root production succeeds with exact coverage, multiplicities and strict order |

The root default build includes the same consumers. Exact `#print axioms`
guards permit only `propext`, `Classical.choice` and `Quot.sound`. These are
proof/API composition checks; there are no new performance measurements or
claims of joint ordinary-real realization. Optional tactic examples remain
owned by #10358 and are reused from `conformance/HexRCF/TotalAlgebraicProofs.lean`
and `ProductionProgress.lean`. Exploration and a fresh split-package consumer
remain explicit gates in the [publication plan](../../reports/real-closure-publication.md).
