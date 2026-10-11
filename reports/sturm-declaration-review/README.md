# Sturm proof and API review

The [computational assessment](computational.md) treats all 48 handwritten
declarations in the four production modules exported by `HexSturm`.
The [companion assessment](companion.md) treats all 78 handwritten declarations
in the seven production modules exported by `HexSturmMathlib`, including their
private helpers. Generated record projections and elaborator declarations are
not separate entries. The prepared-domain fields are assessed with their
structure. The [manifest](manifest.json) records the reviewed module hashes and
declaration names at source commit
`3052375699bc4a94b56c8b4cd839bb916c9c0a5e`. The documentation changes accompanying
this assessment do not change their definitions, statements or proof bodies.
Each module's `sha256` binds that predecessor; its `documented_sha256` identifies
the module bytes with the completed and corrected docstrings.

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

## Environment lint and declaration references

`HexSturmMathlib.LintTests`, included in the existing default companion-test
target, runs the Mathlib environment linters on both module roots, including
`docBlame` and `docBlameThm`. The target builds without an owned lint finding.
This complements the individual declaration assessments and their module
hashes; a clean linter alone does not establish API quality.

The [compiled reference assessment](zero-references.md) resolves all 126
manifest declarations within 241 constants attributed by Lean to the audited
modules. Eight source-written structure fields have separate API dispositions;
107 further constants have ancestor metadata: 106 elaborator artifacts and
one explicitly assessed source-written private constructor. Eleven have known
foreign bases; none has an unresolved ancestor. The classification uses the
source manifest and ancestors, rather than positive compiler-origin predicates.

The graph traces references to production source outside the Sturm pair,
merging known compiler aliases and selected additional constants with their
base, preserving clients through selected aliases and dropping self-edges.
Edges into aliases created outside the eleven audited modules are not collected.
It gives individual retained API purposes for all 52 public manifest declarations
without such a path in the selected imported environment. Thirteen have no
non-self-generated direct clients; the others have pair/evidence references.
Every private helper has a path to a public manifest declaration. The recorded
terminals have no downstream production path, so that reachability alone is
not a claim that the helper has a production client.

Source-path and module-name rules determine user roles, including semantic
adapters; these are audited conventions, rather than Lake target membership. A named executable-test exception handles `TrivialChecks`; production
modules such as SignDet’s `NodeChecks` remain production. The imported table
covers all 356 tracked Hex production modules with a
root-package transitive import path to Sturm: 13 pair modules and 343 downstream
modules. It distinguishes all imported
sources from named dependency/toolchain modules and rejects unresolved or
ambiguous source paths. The full imported-module table and repository-wide lexical
source cross-check are retained; anonymous examples, registration and external
clients remain outside the compiled-reference scope. All recorded axiom sets
contain only the three standard logical axioms. All tracked root-package Lean source
bindings, role/alias tests and a checker that regenerates derived JSON and
verifies disposition columns accompany the report. The compiled inventory
normalization check is idempotence against the retained inventory; it does not
rerun Lean or bind a separately retained raw inventory. Re-attestation is manual.

## Remaining phase acceptance

Both libraries record Phase 5. The prerequisite Phase-4 attestation is merged
in [#10860](https://github.com/kim-em/hex-dev/pull/10860), and the
[proof acceptance](../sturm-proof-acceptance.md) records the sorry-free build
and passing conformance. Phase 6 still requires acceptance of the declared computational regression
check and final review of these quality artifacts. A source assessment or kernel
axiom guard does not establish those requirements. The existing
chapter supplies documentation without advancing Phase 7 ahead of Phase 6.
