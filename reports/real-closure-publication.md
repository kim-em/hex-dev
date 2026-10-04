# Real-closure package preparation

This records companion integration and package-boundary preparation for
[#10575](https://github.com/kim-em/hex-dev/issues/10575).
The source base revision, input digest and exact external pins are recorded in
[the inventory](real-closure-package-inventory.json). The integration consumes
merged APIs. It does not attest implementation owners' pending contracts,
advance phases, or admit new release-manifest entries. The accompanying
[requirements audit](real-closure-requirements.md) records the acceptance gaps.

## Public imports and source ownership

Regenerate the source inventory with
`python3 scripts/audit_real_closure_packages.py --base-revision 49a7bada21543b6d1631de5537c0dda4b1da68ad > reports/real-closure-package-inventory.json`.
It records declared dependencies separately from imports reachable through
current public umbrellas and the development semantic modules, including
external import roots. The digest covers the generator and its source inputs;
unresolved local library imports are errors. The base revision can be supplied
explicitly, including in a clone without `origin/main`. Separate
`candidateRCFPackages` records describe base HexRCF plus RealFormula and the
proposed optional coefficient package using current imports. The integrated real-roots companion and remaining companion
migrations introduce the Tau Ceti installation dependency described
below. The generator neither creates package trees nor publishes them.

The eight family libraries are HexOrderedFn/Mathlib, HexSturm/Mathlib,
HexSignDet/Mathlib and HexRealClosure/Mathlib. The computational packages
stay independent of Mathlib, Tau Ceti and the companions, including transitive
dependencies. Tau Ceti requirements belong only in Mathlib proof packages.
The inventory records each library's `mathlib` classification. Development
semantic modules keep their existing ownership:

| Source | Owning package and public import | Current availability |
| --- | --- | --- |
| `HexRealRootsMathlib/Tarski{Foundation,Soundness,Real}.lean` | `hex-real-roots-mathlib`; `HexRealRootsMathlib` | Integrated in the normal companion target and public umbrella; existing published versions do not contain this migration |
| `HexSturmMathlib/Soundness.lean` | `hex-sturm-mathlib`; `HexSturmMathlib` | Integrated alongside domain/producer correspondence in the normal target and umbrella; companion remains unreleased. Two semantic regression modules remain under adapters |
| `adapters/HexSignDetMathlib/` | `hex-sign-det-mathlib`; `HexSignDetMathlib.ThomRoots`, `SelectedProducer`, `ComparisonProducer`, `Convert`, with public umbrella imports | Seventeen adapter modules; the regular umbrella exposes finite BKR algebra, not these selected-root semantics |
| `adapters/HexRealClosureMathlib/` | `hex-real-closure-mathlib`; `HexRealClosureMathlib.TowerRoots`, `RootCollection`, `TowerEnlargeOrder`, with public umbrella imports | 104 adapter modules including tests; current umbrella exposes only computation, polynomial interpretation and `BaseContext` |
| `HexOrderedFnMathlib/` | `hex-ordered-fn-mathlib`; `HexOrderedFnMathlib` | Ordinary umbrella already exposes real and infinitesimal ordered extensions |
| `adapters/HexRCF/RealFormula.lean` | Base `hex-rcf`; `HexRCF.RealFormula` after RealFormulaMathlib is publishable | One module built by `HexRCFRealFormula`; absent from base `HexRCF.lean` |
| `adapters/HexRCF/RealCoefficients/` plus its umbrella | Optional Mathlib adapter proposal below; `HexRCF.RealCoefficients` | 54 coefficient modules built by `HexRCFRealCoefficients`; absent from base `HexRCF.lean` |

The inventory lists every adapter source and its direct import roots. Modules under `Tests/` or ending in `Tests` stay development checks unless individually selected as
standalone regression modules under existing release policy. Migration must
move each semantic file into its owner directory, preserve its module name,
update companion umbrellas, then remove the adapter file and its old Lake
glob in the same change. Leaving two providers of one module is invalid.
This integration moves only the completed shared Tarski and Sturm semantic
modules. Active sign, tower and tactic modules remain with their owners.

## Tau Ceti impact

The [real-roots companion SPEC](../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#sturm-tarski-correspondence)
and [family contract](../SPEC/future-work.md#one-sturmtarski-primitive) place
the shared Tarski semantics in **HexRealRootsMathlib**. Its `TarskiFoundation.lean` directly
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
one maintainer-selected shared Hex version; none is selected here. The existing
release driver now uses `rewrite_external_requires` to add a missing direct
provider from the exact monorepo lock before checking managed-source imports.
`rewrite_external_pins` synchronizes existing declarations; `rewrite_manifest`
also adds newly needed external providers to downstream locks, marking Tau
Ceti inherited in packages that obtain it through a pinned companion.
Existing external dependency records remain pinned. This does not add any
ineligible Hex library to the release manifest.
Tau Ceti's own lock uses the same Mathlib revision shown above. Downstream
proof/tactic packages must resolve a compatible shared Mathlib revision;
updating Tau Ceti requires checking that compatibility.
The existing mirror CI cache policy does not cache Tau Ceti build artifacts,
so its imported modules rebuild in affected mirrors. Tau Ceti enables
`warningAsError`; dependency-pin updates need a fresh compatible build,
including that warning policy.

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
  formula consumers should not install the tower just for this module.
- Sharing the `HexRCF` namespace needs an explicit module-ownership rule in
  the base package, as well as disjoint source files. Lake’s default `HexRCF`
  library root claims all `HexRCF.*` modules, including absent optional ones.
  The local candidate experiment proposes `roots = []` plus an exact list of
  the 26 non-test base modules; the existing test target retains its separate
  module list. The optional adapter then owns its own explicit modules.
  This base-package configuration change is unapplied and needs user direction
  and an owning SPEC revision before production integration. The rational
  `import HexRCF` surface is preserved in the experiment. The optional package requires base `hex-rcf` and the
  companions in its separate candidate inventory record, including the
  real-algebraic, Sturm and number-field companions. Its imports require
  RealFormulaMathlib and `HexRCF.RealFormula`, so publication also requires
  RealFormula/Mathlib and Reflect/Mathlib eligibility and that module's
  availability in base HexRCF. Base `hex-rcf` never requires it.
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
and native tower production/completeness/multiplicities/order. The query
consumer also applies the shared integer-certificate theorem through the
real-roots umbrella and the complete `query_iff` characterization through
the Sturm umbrella. Every resulting
theorem has an exact ordinary-kernel axiom guard. None imports `all`, test
internals, or an active worker's branch. The root default build compiles the
same source files, as does the existing CI build; the admission scan includes
their import cones. The rational runtime guard is a conformance case, not a
kernel proof of producer totality.

The existing path-based consumer validates **local monorepo composition**.
The separate [local candidate experiment](../experiments/RealClosureConsumer/CANDIDATES.md)
uses ordinary imports against Git-pinned package trees, with no monorepo path
requirement. It reuses the existing publication source mappings and pin
rewriters. [#10476](https://github.com/kim-em/hex-dev/pull/10476) is merged;
its existing `--dry-run --stage` and `consumer_check.py` supply the exact
release-output check. The earlier local candidate results below predate that
infrastructure and remain identified separately. Candidate
success is not a full release-sync validation, manifest eligibility, or
availability of any published version. The optional tactic sources are test
modules in the consumer; no optional installable package is selected.
Optional tactic consumers reuse [#10358](https://github.com/kim-em/hex-dev/issues/10358)'s `TotalAlgebraicProofs`,
`ProductionProgress`, and merged #10668's `PreparedCoefficients`, `FiniteReplay`
and fresh `ProofProbe.Prepared` proofs. The latter authenticate source/divisor
bindings and quote frozen replay with exact ordinary-kernel axiom guards; exploration consumers await [#10378](https://github.com/kim-em/hex-dev/issues/10378)'s delivered API.

The earlier [candidate evidence ledger](real-closure-candidate-consumer.json) records
the 62 local Git pins, exact external pins and source/configuration/log hashes.
The fresh consumer uses the experimental HexRCF declaration, and its rational
test target passes under that declaration. Separate builds of
the two migrated companions and the base HexRCF package with its existing
library declaration pass against the generated locks without `lake update`;
those locks remain unchanged. Computational candidate declarations and locks
contain neither Mathlib nor Tau Ceti. These checks validate the local package
layout and the new provider/lock synthesis; they do not choose the optional
package boundary or certify a release sync.

The earlier three [targeted sync previews](real-closure-sync-previews.json), using the
read-only live `release-sync-baseline` state, pass for
`hex-real-roots-mathlib`, `hex-rcf` and the aggregate `hex`. They preview the
direct Tau Ceti requirement and the inherited downstream lock entries using
the actual published manifest pin lists. They predate the aggregate requirement
repair and the merged staging consumer, and do not validate the current driver. The checkout's bootstrap baseline
first fails because its proposed tag already exists; that failure is retained.
These previews do not build or retain staged packages and are not a full
sync dry run. The full-declared-closure candidate builds above do not certify
the smaller published-only graph.

The [staged-consumer ledger](real-closure-staged-consumer.json) records a full
60-repository dry run using the merged release tool and the live baseline.
The initial consumer failed because the aggregate omitted its manifest's
published ECPP/Mathlib requirements; the driver now adds them. A combined
aggregate/test-kit consumer then failed module ownership, and changing
require order did not repair it. Those failures are retained. The existing
checker now uses a separate helper project without changing published roots.
Its helper build, aggregate import/test/example build (23,585 jobs), and native
link check all pass. Separate checks build the existing `Hex` umbrella, the
complete `HexTestKit` target, and the existing arbitrary-certificate Tarski
example with its exact ordinary-kernel guard. All 32 computational staged
lockfiles contain no Mathlib, Tau Ceti or AINTLIB.

The stage was produced at the ledger's `b01673` source commit; fresh consumer
projects reuse content-hashed staged library build outputs. The newer checker
supplies helper isolation and additional targets. Since staging, the driver
runtime syntax tree and parsed manifest data are unchanged; README wording was
corrected afterward. This validates the recorded candidate code and dependency
configuration on Linux, not every platform or new-family eligibility. The
release workflow must restage current output and pass its blocking consumers
before publication. The earlier 62-package experiment still covers a different,
full declared graph including unreleased libraries and the unapproved optional
ownership prototype.

Merged #10668's authenticated preparation/replay, fresh proof probes, manual
and existing consumers also build in the monorepo (15,522 jobs), and the full
conformance target passes (14,763 jobs). The 116 release/DAG tests pass. CI run
[37178450711](https://github.com/kim-em/hex-dev/actions/runs/37178450711) passed
all oracles but failed smoke verification at 385/360 seconds; it remains a
failed operational gate, with the cap and scientific settings unchanged.
No performance attestation follows from these builds or smoke results.

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
   The inventory records source counters: ordered pair 4; Sturm pair 3;
   sign and tower pairs 0. These are recorded counters, not assessments that
   their merged implementations are absent.
2. Separately obtain distribution eligibility for every transitive input.
   RealAlgebraic/Mathlib are recorded at 3: [#10577](https://github.com/kim-em/hex-dev/issues/10577) owns implementation and
   Phase-4 readiness, followed by their own Phases 5–7. Rank/Mathlib are 4
   with [#10352](https://github.com/kim-em/hex-dev/issues/10352) complete, but still require their own Phases 5–7. RealFormula/
   Mathlib and Reflect/Mathlib are 1 and need their remaining Phases 2–7.
   HexPolyFast and RationalFn/Mathlib are 4 and need their own Phases 5–7.
   HexTruncatedSeries is 7 and imported by OrderedFn through RationalFn; it
   needs a manifest entry and mirror bootstrap. HexModular is also 7 and
   absent from the manifest; it remains required by the declared graph even
   though current family public imports do not reach it. The inventory lists
   both declared and actual import closures and each input's phase; absence from a public import is not a
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
5. The shared Tarski modules are integrated into the already published real-roots
   companion’s managed paths, with direct pinned Tau Ceti requirement synthesis
   and inherited downstream lock synthesis in the existing driver. Candidate
   checks validate the local 62-package layout with the full declared graph;
   they do not establish a build of precisely the published-only mirror graph.
   Merging puts these modules in the existing managed paths: the next routine
   full sync will copy them and add Tau Ceti to the companion and downstream
   locks. The aggregate requirement repair also adds its already-published
   ECPP/Mathlib requirements, carrying AINTLIB/HasseWeil into aggregate consumers;
   existing direct Hex requirements are marked direct in generated locks.
   This is a Mathlib-only dependency, not a computational package requirement.
   The merged #10476 workflow builds staged output before pushing and
   tagging. Hold release dispatch until a fresh
   build of the exact candidate release output and pins passes under that
   infrastructure. The local full-graph builds and targeted previews
   do not provide that check. TarskiFoundation’s `import all HexRealRootsMathlib.TarskiSum` accesses
   its own companion internals and passes the existing DAG/trusted-import policy;
   consumers use ordinary imports. No published mirror is edited or pushed.
   Obtain maintainer-created new mirrors and skeletons under
   [BOOTSTRAP.md](../scripts/release/BOOTSTRAP.md). Declare direct Tau Ceti and
   pinned Hex requirements in new skeletons. Update aggregate coverage only for
   an agreed optional package boundary.
6. Use [#10476](https://github.com/kim-em/hex-dev/pull/10476) to build staged trees and a fresh consumer with candidate pins,
   including Tarski, BKR/Thom, ordered extensions, tower roots/exploration and
   the optional tactic. Then run the **full** sync dry run and reconcile any
   diverged mirror baseline. A plain `--dry-run` does not retain staged packages; pass `--stage`
   to retain them for `consumer_check.py`.

The staged aggregate's unmanaged `Hex.lean` omits HexECPP/Mathlib and
HexPermGroup/Mathlib, despite their inclusion in the manifest and generated
README table. Ordinary per-library imports remain the consumer surface tested
here. Reconcile that umbrella with the manifest before promising complete
`import Hex` re-exports. A proposal is to manage `Hex.lean` from the existing
`HexAggregateCheck.lean` import set; changing the aggregate's source ownership
requires a separate package decision before applying it. No mirror is hand-edited.

Mirror creation, version selection, release dispatch and announcements follow
the maintainer's schedule. Unrelated distribution eligibility is separate
from [#10575](https://github.com/kim-em/hex-dev/issues/10575)'s final integrated acceptance, but remains a release prerequisite.
