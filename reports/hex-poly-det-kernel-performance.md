# General symbolic determinant replay improvements

The shared polynomial replay path is faster on the three retained
counterexamples, but `norm_det` followed by `ring` remains faster on all three.
No matrix-specific route is added and the default-on policy is unchanged.

## Implementation

The final theorem application's non-atomic proof arguments are closed over
needed locals and checked as opaque auxiliary lemmas. The final application is
checked separately. Every component is charged to the same proof-node budget
before admission, including retained let payloads, and the reported count sums
all components and the final application. Tests cover universe-polymorphic
locals, retained lets, exact budget admission and exhaustion after component
admission. No component's kernel check is skipped.

The closed type and proof use Lean's common-expression sharing operation before
auxiliary declaration admission, matching ordinary theorem elaboration.

The common list checker uses `List.rec` directly for exponent comparison,
exponent equality, exponent addition, multiplication by one term and polynomial
list equality. This avoids the `List.brecOn`/`below` machinery produced by the
recursive-equation elaborator. The original recursive functions remain the
compiled implementations through proved `@[csimp]` equalities. Their behavior
is unchanged for all inputs, including noncanonical and unequal-length lists;
no trusted runtime assertion replaces a proof.

## Diagnostic stages

Each stage has two adjacent Mathlib/Hex pairs, AB then BA. Times below are Hex's
median explicit tactic-call time plus its final theorem kernel check, in ms.
All auxiliary checks are already inside the tactic clock. Profiler and trace
logging are disabled inside the timed call. Statement elaboration, imports,
serialization and Lake overhead are excluded.

| Shared implementation | Dense 4×4, sixteen variables | Dense 4×4, quadratics in two variables | 6×6, two dense 3×3 diagonal blocks |
|---|---:|---:|---:|
| Before | 410.3 | 998.8 | 770.9 |
| Opaque components | 374.6 | 949.8 | 731.0 |
| Plus simple exponent recursors | 328.1 | 920.4 | 632.7 |
| Plus common-expression sharing | 319.2 | 936.0 | 615.4 |
| Plus simple row-product and list-equality recursors | 317.5 | 914.5 | 604.2 |

The observed before/final reductions are 23%, 8%, and 22%. Before and after
stages are separate runs, not adjacent before/after arms. These two-pair
observations are diagnostic, not six-pair shipping speedup estimates.
In particular, the small individual effects of sharing and the final two
recursors are not independently resolved by these samples. Mathlib's proof
work in the final diagnostic pairs is about 125, 343 and 272 ms respectively.

The earlier isolated splitting experiment does not predict a twofold fresh-call
improvement. In a fresh module, the first certificate component alone takes
638 ms; the earlier roughly 310 ms measurement checked that component after
checking the original whole proof. Every retained fresh measurement here
includes the first check. The exact cause of that ordering sensitivity has not
been isolated.

## Quiet six-pair comparison

| Input | Mathlib + ring, ms | Hex, ms | Mathlib wins |
|---|---:|---:|---:|
| Dense 4×4, independent variables | 236.5 | 399.4 | 6/6 |
| Dense 4×4, quadratic entries | 676.7 | 934.4 | 6/6 |
| 6×6, two dense diagonal blocks | 511.5 | 695.8 | 6/6 |

This uses the existing fresh-module runner and automatic CPU lease. Each case
has six adjacent Mathlib/Hex pairs in alternating AB/BA order, fresh module
builds, and an import-only baseline per arm. Every completed sample is retained;
none is rejected based on shared-host activity. Route and axiom audits run in
separate modules. All three Hex proofs use `Polynomial.target_det`; accepted
proofs depend only on `propext`, `Classical.choice`, and `Quot.sound`.

External build deltas are affected by Lake's completion polling, so they are
reported separately from the explicit proof-work clocks. Neither table supports
a claim that Hex now beats Mathlib.

All measurements are serial, each build has a 60-second ceiling, and no memory
cap is imposed. A timeout aborts the small campaign rather than scheduling a
larger case. The completed diagnostic and quiet campaigns together take 8 minutes 20 seconds;
setup and dependency rebuilds are separate.

## Validation

- `lake build`: 14,548 jobs, successful.
- `HexMvPoly.KernelTests`, `HexMvPoly.KernelResidueTests`,
  `HexMvPolyMathlib.KernelResidueTests`, and `HexPolyDetMathlib.Tests`: successful.
- Both affected computational conformance modules build. Regenerated fixtures
  are unchanged; the oracles accept 42 exact matrix records and 59 multivariate
  polynomial cases. All 29 matrix-oracle rejection tests pass. The first local
  oracle attempt lacked Python dependencies; the retained successful rerun uses
  an isolated `uv` environment with SymPy and python-flint.
- DAG, Phase-4, release-manifest, source-size, copyright, published trust-surface
  and Mathlib-free benchmark checks pass. DAG and release-manifest unit tests pass.
- All six quiet probe arms pass the separate axiom audit; all three Hex arms
  retain the polynomial certificate route.

Raw compiler output, completed samples, source snapshots, stage hashes and
reproduction scripts are retained in
[the archive](bench-results/hex-det-tree/kernel-improvements/).
