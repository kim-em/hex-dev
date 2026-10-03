# Real-closure package preparation

This is the package-boundary proposal for [#10575](https://github.com/kim-em/hex-dev/issues/10575).
The source base revision, input digest and exact external pins are recorded in
[the inventory](real-closure-package-inventory.json). The proposal consumes
merged APIs. It does not attest implementation owners' pending contracts,
advance phases, or admit new release-manifest entries. The accompanying
[requirements audit](real-closure-requirements.md) records the acceptance gaps.

## Public imports and source ownership

Regenerate the source inventory with
`python3 scripts/audit_real_closure_packages.py > reports/real-closure-package-inventory.json`.
It records declared dependencies separately from imports reachable through
current public umbrellas and the development semantic modules, including
external import roots. It neither creates package trees nor publishes them.

The eight family libraries are HexOrderedFn/Mathlib, HexSturm/Mathlib,
HexSignDet/Mathlib and HexRealClosure/Mathlib. The computational packages
stay independent of Mathlib, Tau Ceti and the companions, including transitive
dependencies. Tau Ceti requirements belong only in Mathlib proof packages.
The inventory records each library's `mathlib` classification. Development
semantic modules keep their existing ownership:

| Development source | Intended package and public import | Current availability |
| --- | --- | --- |
| `adapters/HexRealRootsMathlib/Tarski{Foundation,Soundness,Real}.lean` | `hex-real-roots-mathlib`; `HexRealRootsMathlib.TarskiSoundness`, with a public umbrella import | Three modules built by `HexQuerySemantics`; absent from the published source tree and umbrella |
| `adapters/HexSturmMathlib/Soundness.lean` | `hex-sturm-mathlib`; `HexSturmMathlib.Soundness`, with a public umbrella import | Built by `HexQuerySemantics`; regular companion already contains domain/producer correspondence |
| `adapters/HexSignDetMathlib/` | `hex-sign-det-mathlib`; `HexSignDetMathlib.ThomRoots`, `SelectedProducer`, `ComparisonProducer`, `Convert`, with public umbrella imports | Seventeen adapter modules; the regular umbrella exposes finite BKR algebra, not these selected-root semantics |
| `adapters/HexRealClosureMathlib/` | `hex-real-closure-mathlib`; `HexRealClosureMathlib.TowerRoots`, `RootCollection`, `TowerEnlargeOrder`, with public umbrella imports | Eighty-seven adapter modules including tests; current umbrella exposes only computation, polynomial interpretation and `BaseContext` |
| `HexOrderedFnMathlib/` | `hex-ordered-fn-mathlib`; `HexOrderedFnMathlib` | Ordinary umbrella already exposes real and infinitesimal ordered extensions |
| `adapters/HexRCF/RealFormula.lean` | Base `hex-rcf`; `HexRCF.RealFormula` after RealFormulaMathlib is publishable | One module built by `HexRCFRealFormula`; absent from base `HexRCF.lean` |
| `adapters/HexRCF/RealCoefficients/` plus its umbrella | Optional Mathlib adapter proposal below; `HexRCF.RealCoefficients` | Forty-six modules built by `HexRCFRealCoefficients`; absent from base `HexRCF.lean` |

The inventory lists every adapter source and its direct import roots. Tests
ending in `Tests` stay development checks unless individually selected as
standalone regression modules under existing release policy. Migration must
move each semantic file into its owner directory, preserve its module name,
update companion umbrellas, then remove the adapter file and its old Lake
glob in the same change. Leaving two providers of one module is invalid.
No active owner's module is moved by this preparation.

## Tau Ceti impact

The [real-roots companion SPEC](../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#sturm-tarski-correspondence)
and [family contract](../SPEC/future-work.md#one-sturmtarski-primitive) place
the shared Tarski semantics in **HexRealRootsMathlib**. Its adapter directly
imports `TauCeti.Algebra.Polynomial.Sturm.Infinity`. The sign companion's regular
`Foundation.lean` already imports `TauCeti.Data.Matrix.OccCount`; its adapters
also directly import Tau Ceti's BKR/Thom foundations. The tower companion directly
imports its ordered algebraic real-closure foundation. Publishing those
modules requires direct Tau Ceti requirements in those three companion Lake
skeletons, pinned to the monorepo lock.

The concrete dependency paths include:

```text
hex-rcf -> hex-real-roots-mathlib -> TauCeti
hex-real-algebraic-mathlib -> hex-real-roots-mathlib -> TauCeti
hex-sturm-mathlib -> hex-real-roots-mathlib -> TauCeti
hex-sign-det-mathlib -> hex-sturm-mathlib -> hex-real-roots-mathlib -> TauCeti
hex-real-closure-mathlib -> hex-real-roots-mathlib -> TauCeti
hex (aggregate) -> hex-rcf / hex-real-roots-mathlib -> TauCeti
```

The existing manifest already pins `hex-real-roots-mathlib` from base
`hex-rcf` and from the aggregate. **HexRCF is a Mathlib proof/tactic package**:
`libraries.yml` declares `mathlib: true`, and its released manifest entry
declares `mathlib_only: true`. Its name is an existing exception to the
companion naming convention; it is not a computational library. The aggregate
also includes Mathlib companions. Thus even a rational-only base tactic consumer would
resolve Tau Ceti after that companion's packaging changes. This is a package
dependency impact; it does not mean rational `rcf` needs a tower at execution
or imports its algorithms. The independent computational real-algebraic fast
path remains independent of towers. Moving the primitive into
HexSturmMathlib would change the specified ownership and is not proposed.

Exact candidate foundation requirements from `lake-manifest.json`:

| Package | Git URL | Revision |
| --- | --- | --- |
| TauCeti | `https://github.com/TauCetiProject/TauCeti.git` | `0dbbe255a4f418084b30a3ffe6763d824a6b4250` |
| mathlib | `https://github.com/leanprover-community/mathlib4.git` | `d870b9068518a0870842d15a0cd42637ec30b587` |

The candidate toolchain is `leanprover/lean4:v4.35.0-rc3`. A future release uses
one maintainer-selected shared Hex version; none is selected here. Existing
`external_pins`/`rewrite_external_pins` synchronize declared external requirements
and locks; they do not create a missing Tau Ceti declaration in a skeleton.
Tau Ceti's own lock uses the same Mathlib revision shown above. Downstream
proof/tactic packages must resolve a compatible shared Mathlib revision;
updating Tau Ceti requires checking that compatibility.

## Optional real-coefficient adapter proposal

Proposed installable boundary, requiring user decision before changing the
published packages:

- Keep `hex-rcf` and `import HexRCF` as the existing rational tactic package.
- Publish an optional Mathlib proof/tactic package, provisionally named
  `hex-rcf-real-coefficients`, containing
  `HexRCF.RealCoefficients` and its submodules. Preserve
  the public import `HexRCF.RealCoefficients`; no second copy of `HexRCF.lean`.
- Integrate `HexRCF.RealFormula` into base HexRCF when RealFormulaMathlib is
  publishable. Its existing SPEC ownership and imports need no tower; shared
  formula consumers should not install the tower just for this bridge.
- Use the coefficient adapter's existing Lake declaration with explicit module globs.
  The optional package and base package share the `HexRCF` namespace but own
  disjoint modules. The optional package requires base `hex-rcf` and the
  delivered tower/sign/ordered companions. Base `hex-rcf` never requires it.
- Keep the coefficient-extension contract in the owning HexRCF SPEC. Specify
  the optional package there before implementation. Maintain a package README
  describing certified caller inputs, finite refusal and joint-realization
  prerequisites; reuse [#10358](https://github.com/kim-em/hex-dev/issues/10358)'s manual and ordinary-import examples.

This proposal isolates the tower installation cost. It does **not** revise
`libraries.yml`'s existing `HexRCF -> HexRealFormulaMathlib` dependency or the
Tau Ceti impact above. The current released RCF manifest pins only the
published part of that dependency closure. Removing those pins or splitting the already published
real-roots companion would be a separate architecture decision and SPEC change.
The optional package is not silently included in the aggregate; that surface
also needs an explicit decision.

## Candidate consumers

[The consumer project](../experiments/RealClosureConsumer/README.md) builds
ordinary-import examples from a separate Lake project requiring the local
monorepo. Its four modules consume arbitrary query certificates, prepared
counts, a runtime rational query and its conditional real interpretation,
complete BKR/Thom root production, successive infinitesimal order,
and native tower production/completeness/multiplicities/order. Every resulting
theorem has an exact ordinary-kernel axiom guard. None imports `all`, test
internals, or an active worker's branch. The root default build compiles the
same source files, as does the existing CI build; the admission scan includes
their import cones. The rational runtime guard is a conformance case, not a
kernel proof of producer totality.

This validates **local monorepo consumer composition**, not candidate split
packages or a release sync. [#10476](https://github.com/kim-em/hex-dev/pull/10476)
is open at the inventory revision. Its staging/consumer implementation is
not copied or replaced. The fresh consumer against split-package trees and
precisely their pinned Hex requirements remains outstanding. These sources
are ready to reuse when that infrastructure lands and the migration is authorized.
Optional tactic consumers reuse [#10358](https://github.com/kim-em/hex-dev/issues/10358)'s `TotalAlgebraicProofs` and
`ProductionProgress`; exploration consumers await [#10378](https://github.com/kim-em/hex-dev/issues/10378)'s delivered API.

## Unapplied publication changes and distribution prerequisites

No change to `released.yml` is applied. The exact source moves above and
the inventory's declared dependencies and separately computed public/semantic
import closures define the candidate layout. Declared dependency closure is
the current manifest pin rule; public imports identify actual ordinary-import
needs and must not silently replace that rule. For example, current Sturm and
RealRootsMathlib umbrellas do not import the PolyZ fast-kernel helpers, while
their declared graph includes those helpers' dependencies. OrderedFn actually
imports HexPolyFast through RationalFn. To turn the proposal into eligible
manifest state:

1. Finish owner contracts in the requirements audit and this issue's eight
   libraries' Phases 5–7, including real API review and built Verso chapters.
   The inventory records current **main** counters: ordered pair 4; Sturm,
   sign and tower pairs 0. These are recorded counters, not assessments that
   their merged implementations are absent.
2. Separately obtain distribution eligibility for every transitive input.
   RealAlgebraic/Mathlib are recorded at 1: [#10577](https://github.com/kim-em/hex-dev/issues/10577) owns implementation and
   Phase-4 readiness, followed by their own Phases 5–7. Rank/Mathlib are 4
   with [#10352](https://github.com/kim-em/hex-dev/issues/10352) complete, but still require their own Phases 5–7. RealFormula/
   Mathlib and Reflect/Mathlib are 1 and need their remaining Phases 2–7.
   HexPolyFast is 4 and also needs Phases 5–7; RationalFn/Mathlib remain separate
   inputs. HexTruncatedSeries and HexModular are 7 but have no manifest entries,
   so their publication/bootstrap still needs preparation when required by
   the admitted graph. The inventory lists both declared and actual import
   closures and each input's phase; absence from a public import is not a
   license to bypass the current manifest pin rule.
3. Preserve [#9809](https://github.com/kim-em/hex-dev/issues/9809)'s ownership of HexPolyFp performance (recorded phase 3).
   Existing published inputs are not automatically promoted by publishing a
   downstream consumer. No worker or measurement is dispatched here.
4. After phase eligibility, add new manifest entries in topological order for
   unpublished prerequisites and the eight family libraries; each uses its
   owner directory, umbrella, owning SPEC and existing managed README rules.
   Preserve monorepo fixtures/oracles/benches under current bootstrap policy.
   Select standalone regression modules explicitly. Populate `pins` with
   exactly the **published** transitive closure, using the inventory as the
   initial audit and rerunning the existing manifest checker after migrations.
   The optional package additionally needs an agreed manifest representation
   for its disjoint module globs and owning SPEC; no new release framework.
5. Before moving Tarski adapters into the already published real-roots
   companion, extend the existing release tooling to manage the missing
   direct Tau Ceti requirement in its Lake file. Its synchronized declaration,
   lock and consumer build must be ready in the same migration; otherwise the
   next unrelated sync would publish sources needing an undeclared package.
   `validate_external_imports` now rejects a missing Tau Ceti requirement, but
   does not add one. Do not hand-edit an existing published mirror. Reconcile
   exact-path private-import rules for moved modules; TarskiFoundation currently
   uses `import all HexRealRootsMathlib.TarskiSum`.
   Obtain maintainer-created new mirrors and skeletons under
   [BOOTSTRAP.md](../scripts/release/BOOTSTRAP.md). Declare the direct Tau Ceti
   requirements above and pinned Hex requirements in new skeletons. Update
   aggregate coverage only for the agreed package boundary.
6. Use [#10476](https://github.com/kim-em/hex-dev/issues/10476) to build staged trees and a fresh consumer with candidate pins,
   including Tarski, BKR/Thom, ordered extensions, tower roots/exploration and
   the optional tactic. Then run the **full** sync dry run and reconcile any
   diverged mirror baseline. Current `--dry-run` does not stage packages.

Mirror creation, version selection, release dispatch and announcements follow
the maintainer's schedule. Unrelated distribution eligibility is separate
from [#10575](https://github.com/kim-em/hex-dev/issues/10575)'s final integrated acceptance, but remains a release prerequisite.
