# Sturm proof and API review

The [computational assessment](computational.md) treats all 48 handwritten
declarations in the four production modules exported by `HexSturm`.
The [companion assessment](companion.md) treats all 96 handwritten declarations
in the seven production modules exported by `HexSturmMathlib`, including their
private helpers. Generated record projections and elaborator declarations are
not separate entries. The prepared-domain fields are assessed with their
structure. The [manifest](manifest.json) records the reviewed module hashes and
declaration names at its `reviewed_revision`. The separate
`predecessor_revision` retains the original review source. The original review supplied
documentation; current polishing adds
endpoint/domain characterizations and sign normalization, uses the new API in
the existing endpoint proofs and moves reduced-query axiom checks into tests.
Computational definitions and existing theorem statements are preserved.
Each module's `predecessor_sha256` binds that predecessor; its `reviewed_sha256`
identifies the module bytes after the current proof/API polishing.
The retained `documented_sha256` values identify the earlier documentation-stage
snapshots; they are provenance metadata, rather than current source bindings.

## Contracts and public imports

The computational modules require explicit coefficient operations and sign
functions. They do not install field or order laws on storage. Their equalities
characterize the executed operations and literal bindings. Semantic guarantees
require the companion's zero-reflecting interpretations and arithmetic/sign
laws. Domain correspondence works over ordered fields; general root-sum
semantics additionally requires a real-closed target.

Producer domain/totality and arbitrary-certificate soundness have separate
proof routes. `query_isSome` characterizes when the actual query succeeds;
`query_iff` gives its full domain/value contract. `check_sound` assumes only
accepted literal replay, not producer provenance, and proves both domain and
value. Prepared objects retain their exact producer equation, whereas arbitrary
certificates can use different valid chains. The review does not replace these
contracts with successful fixtures.

`import HexSturm` exports preparation, queries, counting, remainder reduction
and certificate translation. `import HexSturmMathlib` exports the seven
reviewed semantic modules in the monorepo. Their shared Tarski semantic inputs
already live in `HexRealRootsMathlib/` and its public umbrella. The released
manifest has no Sturm pair entries, and its `hex-real-roots-mathlib` entry still
lacks the Tau Ceti requirement/cache needed by `TarskiFoundation`. Published
versions predate that migration. Candidate package requirements and publication
eligibility remain in the [publication plan](../real-closure-publication.md).
Computation stays independent of Mathlib and Tau Ceti.

## Polishing and validation

The restoration projections use `simp` to expose literal fields without opening
the private constructor. Retargeting, prepared query/count agreement, cache
agreement and operation transport have explicit characterizing lemmas. Semantic
theorems retain their hypotheses rather than asking automation to choose an
interpretation. The short names distinguish mathematical domain, produced
queries and accepted replay within their owning namespaces. No computational
implementation is duplicated by the companion.

The source documentation covers the public restoration projections and the
non-obvious private clearing/embedding helpers. Scaling identities allow zero
input factors; the separate positivity lemma supplies the conditions needed by
accepted chain translation. Sturm count agreement uses root-free **endpoints**,
not a root-free interval.

The existing `HexSturmMathlibTests` target builds canonical and noninjective
domain/query examples, accepted and rejected literal replay, stale context
rejection and rational/integer certificate translation. Its ordinary-kernel
axiom guards cover representative public contracts. Endpoint retargeting and
prepared certificate production are covered there by axiom guards, rather than
concrete semantic applications. The semantic replay examples and count/root-count
axiom guards in
`HexSturmMathlib.Tests.Replay.Semantics`, built by `HexQuerySemantics`, additionally
exercise real-root meaning and the complete noninjective query contract. The
reduced-query module has its own axiom guards. This source review reuses these
controls; it adds no alternate conformance implementation or performance timing.
`HexSturm.Conformance` supplies the computational acceptance/refusal controls
and field/integer differential cases, including executable retargeting and
prepared counting. Its differential comparisons are not an
independent semantic oracle. The [direct frontend corpus](../sturm-direct-conformance/README.md)
supplies exact rational/noncanonical root-sign checks; inherited integer
fixtures in `HexRealRoots` remain supplementary.

The domain API keeps separate sign-law premises because intermediate guards
need only some of negativity, zero reflection, positivity and sign bounds.
Value theorems use full mathematical sign agreement and derive those laws
through `sign_spec`. Existing argument order and binder names are retained
for compatibility with current positional and named applications. The new
endpoint/domain characterizations and sign normalization improve application
without strengthening those contracts. Reduced-query axiom guards live in
the existing test module.

## Environment lint and declaration references

`HexSturmMathlib.LintTests`, included in the existing default companion-test
target, runs the Mathlib environment linters on both module roots, including
`docBlame` and `docBlameThm`. The target builds without an owned lint finding.
This complements the individual declaration assessments and their module
hashes; a clean linter alone does not establish API quality.

The current [compiled reference assessment](zero-references.md) resolves all 144
manifest declarations within 270 constants attributed by Lean to the audited
modules. 8 source-written structure fields have separate API dispositions;
118 further constants have ancestor metadata: 117 elaborator artifacts and
one explicitly assessed source-written private constructor. Of these, 11 have known
foreign bases; none has an unresolved ancestor. The classification uses the
source manifest and ancestors, rather than positive compiler-origin predicates.

The graph traces references to production source outside the Sturm pair,
merging known compiler aliases and selected additional constants with their
base, preserving clients through selected aliases and dropping self-edges.
Edges into aliases created outside the eleven audited modules are not collected.
It gives individual retained API purposes for all 61 public manifest declarations
without such a path in the selected imported environment. 13 have no
non-self-generated direct clients; the others have pair/evidence references.
Every private helper has a path to a public manifest declaration. The recorded
terminals have no downstream production path, so that reachability alone is
not a claim that the helper has a production client.

Source-path and module-name rules determine user roles, including semantic
adapters; these are audited conventions, rather than Lake target membership. A named executable-test exception handles `TrivialChecks`; production
modules such as SignDet’s `NodeChecks` remain production. The imported table
covers all 381 tracked Hex production modules with a
root-package transitive import path to Sturm: 13 pair modules and 368 downstream
modules. It distinguishes all imported
sources from named dependency/toolchain modules and rejects unresolved or
ambiguous source paths. The full imported-module table and repository-wide lexical
source cross-check are retained. That supplementary search qualifies the common
names `lt`, `map`, `lower`, `upper`, `squarefree` and `scale` to avoid unrelated text;
it omits their unqualified and receiver notation. The compiled graph captures
such production references independently. Anonymous examples, registration and external
clients remain outside the compiled-reference scope. All recorded axiom sets
contain only the three standard logical axioms. All tracked root-package Lean source and assessment
bindings, role/alias tests and a checker that regenerates derived JSON and
verifies disposition columns accompany the report. The compiled inventory
normalization check is idempotence against the retained inventory; it does not
rerun Lean or bind a separately retained raw inventory. Re-attestation is manual.

## Phase acceptance and remaining computational work

HexSturmMathlib records Phases 6–7. For this theorem library, public-use acceptance
treats individually assessed end-user characterizations as intentional API.
That judgement uses their stated contracts, source applications and individual
dispositions alongside production references; a compiled reference count alone
does not establish API quality. Private helpers all reach an exported interface.
Domain projections are used by coefficient-mapping proofs, and the
ordinary-kernel tests exercise equal domains across noninjective storage,
infinite endpoint normalization and the existing complete query/replay laws.
The individual assessment covers its 96
handwritten declarations, with current compiled-use dispositions, environment
lints, source bindings and ordinary-kernel examples. The chapter's live
examples and dependency references build, and its full rendered content was
inspected at desktop and narrow widths. Long record-field types are replaced
by the source-derived type signature and a description of the stored data and
proof guarantees; the Lean examples fit the narrow viewport.

The companion's computational regression, native-computation and
irreducibility/field-construction criteria are inapplicable: its
[owning SPEC](../../HexSturmMathlib/SPEC/hex-sturm-mathlib.md#conformance-and-phase-4-evidence)
and [Phase-4 policy](../../PLAN/Phase4.md) assign it no compiled
track, and it constructs no fields. Existing theorem-application observations
are diagnostic rather than computational benchmark baselines. The
[local coupling rules](../../PLAN/Conventions.md) permit acceptance
without waiting for later local phases of dependencies.

HexSturm also records Phases 6–7 through its separate
[final acceptance](../sturm-proof-acceptance.md), reusing the unchanged core
declarations and individual dispositions here, with the complete native
comparison, current imports/lints/kernel tests and manual checks. The historical
compiler capture is not relabeled as a current-main reference graph.
Publication eligibility, companion dependency pins and unrelated input phases
remain in the [publication plan](../real-closure-publication.md).

## Reproducing the retained source

The complete review checkout is preserved by the non-release audit tag
`audit/issue-10575-sturm-companion-phase7-complete`. Check out that exact tree
and fetch/build its pinned dependencies before running the checker. The checker
binds a source snapshot; it is expected to refuse later main changes.

```sh
git fetch origin tag audit/issue-10575-sturm-companion-phase7-complete
git switch --detach audit/issue-10575-sturm-companion-phase7-complete
lake build
python3 reports/sturm-declaration-review/check_bindings.py
```

The complete checkout contains the final usage bindings and both source revisions
they reference, so reproduction survives the squash merge and branch deletion.
The separate `audit/issue-10575-sturm-companion-phase7` tag retains the earlier
source-input checkpoint. These tags are evidence references, not published versions.

The retained compiler-reference capture is historical. Later changes to the
shared source-role tooling and the companion Theory rename invalidate its
current-source check; archive verification remains separate from current acceptance.
