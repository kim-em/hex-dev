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
`python3 scripts/audit_real_closure_packages.py --base-revision e422aabd1c85f5d246c6415d0907c7d4d4134b4b > reports/real-closure-package-inventory.json`.
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
| `HexSignDetMathlib/` | `hex-sign-det-mathlib`; `HexSignDetMathlib.ThomRoots`, `SelectedProducer`, `ComparisonProducer`, `Convert`, with public umbrella imports | Eighteen root/sign correspondence modules integrated in the normal companion target and umbrella; companion remains unreleased |
| `adapters/HexRealClosureMathlib/` | `hex-real-closure-mathlib`; `HexRealClosureMathlib.TowerRoots`, `RootCollection`, `TowerEnlargeOrder`, with public umbrella imports | 171 adapter modules including tests; current umbrella exposes computation, polynomial interpretation and base-context models/transport |
| `HexOrderedFnMathlib/` | `hex-ordered-fn-mathlib`; `HexOrderedFnMathlib` | Ordinary umbrella already exposes real and infinitesimal ordered extensions |
| `adapters/HexRCF/RealFormula.lean` | Base `hex-rcf`; `HexRCF.RealFormula` after RealFormulaMathlib is publishable | One module built by `HexRCFRealFormula`; absent from base `HexRCF.lean` |
| `adapters/HexRCF/RealCoefficients/` plus its umbrella | Optional Mathlib adapter proposal below; `HexRCF.RealCoefficients` | 65 coefficient modules built by `HexRCFRealCoefficients`; absent from base `HexRCF.lean` |

The inventory lists every adapter source and its direct import roots. Modules under `Tests/` or ending in `Tests` stay development checks unless individually selected as
standalone regression modules under existing release policy. Migration must
move each semantic file into its owner directory, preserve its module name,
update companion umbrellas, then remove the adapter file and its old Lake
glob in the same change. Leaving two providers of one module is invalid.
The completed shared Tarski, Sturm and SignDet semantic modules are integrated
in their normal companions. Remaining tower and tactic development modules
retain their adapter targets. Active implementations remain with their owners.

## Tau Ceti impact

The [real-roots companion SPEC](../HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md#sturm-tarski-correspondence)
and [family contract](../SPEC/future-work.md#one-sturmtarski-primitive) place
the shared Tarski semantics in **HexRealRootsMathlib**. Its `TarskiFoundation.lean` directly
imports `TauCeti.Algebra.Polynomial.Sturm.Infinity`. The sign companion's regular
`Foundation.lean` already imports `TauCeti.Data.Matrix.OccCount`; its root correspondence
also directly imports Tau Ceti's BKR/Thom foundations. The tower companion directly
imports its ordered algebraic real-closure foundation. Publishing those
modules requires direct Tau Ceti requirements in those three generated companion
Lake files, pinned to the monorepo lock.

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
| TauCeti | `https://github.com/TauCetiProject/TauCeti.git` | `1c497c347f615b3087cb605f8cf743e591376105` |
| mathlib | `https://github.com/leanprover-community/mathlib4.git` | `6b7abb3c7686292736be2955bd3eb9ebf63b456a` |

The candidate toolchain is `leanprover/lean4:v4.35.0-rc3`. A future release uses
one maintainer-selected shared Hex version; none is selected here. The existing
release driver uses `release_requires` and `render_lakefile` to generate direct
providers from the monorepo lock. `rewrite_manifest` and
`_add_closure_externals` supply exact locked providers downstream, marking Tau
Ceti inherited in packages that obtain it through a pinned companion.
Computational/proof classification follows `libraries.yml`, shared with the
DAG checks. This does not add an ineligible Hex library to the release manifest.
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
supplies helper isolation and additional targets. That stage predates the configuration generator merged in #10682. Its driver
runtime syntax tree and parsed manifest data were unchanged at the recorded
checker revision; README wording was corrected afterward. It does not validate
the later generator or its native carrier configuration. This validates the recorded candidate code and dependency
configuration on Linux, not every platform or new-family eligibility. The
release workflow must restage current output and pass its blocking consumers
before publication. The earlier 62-package experiment still covers a different,
full declared graph including unreleased libraries and the unapproved optional
ownership prototype.

The pre-rebase owner-source snapshot from merged `77aadd66` built #10668's authenticated
preparation/replay, fresh proof probes, manual and existing consumers (15,522
jobs), with a separate full conformance build (14,763 jobs). Those invocation
HEADs were not separately captured; the current source-bound replacement
build is recorded below. The earlier 116 release/DAG tests pass on their recorded source. CI run
[37178450711](https://github.com/kim-em/hex-dev/actions/runs/37178450711) passed
all oracles but failed smoke verification at 385/360 seconds; it remains a
failed operational gate. The later run
[37189870141](https://github.com/kim-em/hex-dev/actions/runs/37189870141) also
passed all builds and oracles but failed at 388/360 seconds. Both failures are
retained; neither is a performance pass. Main subsequently merged the separate
CI-limit change [#10696](https://github.com/kim-em/hex-dev/pull/10696). This
integration changes no smoke limit, scientific settings or fixed inputs.
No performance attestation follows from these builds or smoke results.

The [generated-package evidence](real-closure-generated-consumer.json) covers
#10682's generator at source `3c2e7fa09d`, based on `767b3e15ee`. The full
60-repository dry run and fresh downstream helper/aggregate projects pass:
8 helper jobs, 22,529 aggregate jobs, ordinary generated `import Hex`, manifest
tests, eligible examples and native linking. The shared arbitrary-certificate
Tarski example with its exact kernel axiom guard also builds (9,343 jobs).
All 32 computational locks exclude Mathlib, Tau Ceti and AINTLIB. The complete
monorepo integration, owner examples, manual and conformance pass together
(13,767 jobs), with 295 admission cones and the 2,048-file trust scan. The
119 package/dependency tests run against the separately recorded review
corrections at `2a9a6283f9`. External Mathlib artifacts are cached; Hex package
build outputs start absent. Parser/boundary corrections leave all 60 rendered
configurations byte-identical to the built stage. The ledger identifies that
scope and the remaining requirement to restage final output under the release
workflow; Linux evidence does not assert every platform or family eligibility.

Evidence source snapshots are retained on upstream branches
`issue-10575-evidence-candidates`, `issue-10575-evidence-staged` and
`issue-10575-evidence-generated`; the ledgers' exact commit IDs remain the
reproduction references. These branches do not publish split mirrors.

## Unapplied publication changes and distribution prerequisites

No eligibility or dependency-entry change to `released.yml` is applied. The exact source moves above and
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
   The inventory records source counters: ordered pair 5; Sturm and sign pairs 3;
   tower pair 0. These are the inventory snapshot's counters. Current Sturm
   counters are 5 after [proof acceptance](sturm-proof-acceptance.md); SignDet
   counters are 4 after [#10861](https://github.com/kim-em/hex-dev/pull/10861).
   These phase counters do not establish publication eligibility.
2. Separately obtain distribution eligibility for every transitive input.
   RealAlgebraic/Mathlib now record 4 through merged
   [#10860](https://github.com/kim-em/hex-dev/pull/10860); their own Phases 5–7
   remain required. Rank/Mathlib are 4
   with [#10352](https://github.com/kim-em/hex-dev/issues/10352) complete, but still require their own Phases 5–7. RealFormula/
   Mathlib and Reflect/Mathlib are 1 and need their remaining Phases 2–7.
   RationalFn is now 3 after the nested-numeral rollback in
   [#10864](https://github.com/kim-em/hex-dev/pull/10864), with repair tracked by
   [#10863](https://github.com/kim-em/hex-dev/issues/10863); its companion remains
   4. RationalFn must re-attest Phase 4; both then need Phases 5–7.
   HexPolyFast, HexTruncatedSeries and HexModular are 7 and already present
   in the released manifest. OrderedFn imports HexPolyFast and HexTruncatedSeries
   through RationalFn; HexModular remains required by the declared graph even
   though current family public imports do not reach it. The inventory lists
   both declared and actual import closures and each input's phase; absence from a public import is not a
   license to bypass the current manifest pin rule.
3. Preserve [#9809](https://github.com/kim-em/hex-dev/issues/9809)'s ownership of HexPolyFp performance/comparator findings.
   HexPolyFp is recorded at 7 and published, but that owning audit remains open.
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
   companion’s managed paths, with direct pinned Tau Ceti requirements
   and inherited downstream locks generated by the existing driver. Candidate
   checks validate the local 62-package layout with the full declared graph;
   they do not establish a build of precisely the published-only mirror graph.
   Merging puts these modules in the existing managed paths: the next routine
   full sync will copy them and add Tau Ceti to the companion and downstream
   locks. The generator also includes its already-published
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
   [BOOTSTRAP.md](../scripts/release/BOOTSTRAP.md). The existing generator supplies direct Tau Ceti and
   pinned Hex requirements from monorepo source imports and manifest metadata. Update aggregate coverage only for
   an agreed optional package boundary.
6. Use [#10476](https://github.com/kim-em/hex-dev/pull/10476) to build staged trees and a fresh consumer with candidate pins,
   including Tarski, BKR/Thom, ordered extensions, tower roots/exploration and
   the optional tactic. Then run the **full** sync dry run and reconcile any
   diverged mirror baseline. A plain `--dry-run` does not retain staged packages; pass `--stage`
   to retain them for `consumer_check.py`.

Merged [#10682](https://github.com/kim-em/hex-dev/pull/10682) generates the
aggregate Lake file and `Hex.lean` from the existing manifest's aggregated
entries. This supplies the previously missing ECPP/Mathlib and PermGroup/Mathlib
re-exports. The preparation uses that established generator; no additional
aggregate ownership decision or mirror edit is needed here. Current generated
output still requires a fresh staged consumer build before publication.
