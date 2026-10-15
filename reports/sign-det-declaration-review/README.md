# Sign-determination companion proof and API review

The [Theory acceptance](theory-acceptance.md) completes the companion’s independent
Phases 6–7. The computational library remains at Phase 5. The source assessments
and earlier compiler captures below retain their stated checkpoints and scopes.

The [assessment](companion.md) treats all 228 handwritten declarations in the 37
production modules exported by `HexSignDetTheory`, including private helpers and the
fields of `Node.Counted`. The [manifest](manifest.json) records the current declaration names and
reviewed module hashes. Its `sha256` fields retain the source snapshot at
`7433524020514b3907653c5a3fe3b95212ae8f59`; `reviewed_sha256` binds the
current assessed modules. Nine checked-system proof
clients use the foundation acceptance API; their updated bindings are also
recorded in the foundation manifest. Generated projections and elaborator
declarations are not separate assessment entries. The computational library's earlier inventory contains 693 handwritten
declarations in 58 production modules. The foundation, replay, table, selected-sign, descriptor, completion, common-polynomial comparison, graph, root-list, prepared-handle, graph-codec, stored-coefficient, DAG-support, dependency-envelope, serialization and parser
assessments below cover 736 named declarations, including newly added APIs; the
source inventory now has an individual assessment for every inventoried named
computational declaration. The checker enforces coverage of every production
module under `HexSignDet/`; the import-only root umbrella is outside that set. Named declaration forms are those recorded and extracted by each group;
anonymous instances, constructors and fields have separate dispositions. These individual tables supply proof/API assessment; the final companion
attestation above and the core’s final computational acceptance are separate.

The per-group source bindings are review snapshots checked locally, rather
than automatic CI currency checks. The complete handle-review source is
preserved by `audit/issue-10575-sign-det-handles-reviewed-v2`; that historical
reference is retained. Current byte bindings include the separately reviewed
DAG documentation, guard and checker changes. Changed inputs cause the
checker to refuse the current bindings; updating them requires assessment
of the changed inputs. The three handle modules have exact namespace checks. The nine DAG-support
and four codec modules use the shared namespace-aware extractor; older groups
retain their own naming conventions. The declaration-list check covers the declaration forms listed
in those records, while the file hashes bind the complete source bytes.

The eight integration additions have individual assessments in the descriptor,
DAG-support and graph-codec tables. The generic node-property transfer and
validated-binding laws are used by exact root restoration, including partial
predecessor readers. The 728-declaration compiler-use capture remains bound to
its earlier source checkpoint; it does not supply reference counts or axiom
inventories for these additions. Their actual uses and kernel axiom guards are
in the shared readers and existing conformance examples. No new compiler
capture, computational regression pass or core phase acceptance is claimed.

## Contracts and hypotheses

The stored coefficient carrier supplies explicit operations and a sign function. It need
not have a field instance or an injective interpretation. Semantic polynomial identities
use a zero-reflecting interpretation preserving the relevant arithmetic and sign
operations. Matrix equations and context bindings retain literal equality. Domain-only
theorems work over ordered fields; general root counts, selected-root semantics and Thom
order use a real-closed target. Tau Ceti is confined to the Mathlib companion and its
semantic dependencies.

Arbitrary-certificate soundness and actual producer success have separate proof routes.
`Replay.check_support` and `check_counts` establish complete support and counts from
arbitrary accepted replay. Leaf columns or already complete child supports establish
candidate coverage before matrix count recovery. A scaled inverse and matching moments
alone cannot justify omitted columns; the existing `foundation_incomplete`
counterexample makes that distinction explicit. `query_model` derives the finite
construction premise from actual prepared root queries, and `buildPrepared_roots`
establishes producer success without an assumed query model, invertible system or
successful output.

The descriptor constructor's success criterion includes context, shape, full shared
domain and one root jointly realizing the requested word. Accepted partial encodings
still identify a unique root. Completion, selected signs, re-encoding and comparison
preserve that same selected point. General re-encoding separately requires a valid
target domain containing the source root. Full derivative words and Tau Ceti's
non-Archimedean Thom foundation supply general enumeration and strict order without
rational separators.

Tables count occurrences of ordered sign words among **distinct** roots. Repeated words
at different roots retain their counts; these counts are not polynomial root
multiplicities. Valid domains have a squarefree head, so every counted root is simple.
Empty query lists, valid root-free domains, nonzero constant heads, invalid domains,
repeated queries and zero signs keep their distinct contracts. Zero polynomial heads are
invalid shared domains.

## API polishing

The ordinary companion umbrella exports all reviewed production modules. Public
characterizations include root specification/uniqueness, copied source constraints,
exact table counts, successful constructor criteria, ordered root coverage, comparison
results, coefficient conversion and ordered embeddings. Indexed basis and tensor lemmas
preserve the literal order used by computation. Semantic hypotheses stay explicit rather
than being installed as laws on storage.

The source changes document six public characterizing lemmas, the five fields of
`Node.Counted` and fifteen private helpers. Scalar denominator clearing allows a zero
scale; its positivity is proved separately for the actual inverse encoding. Two unused
simp arguments are removed from `constraints_at_root`. `determine_convert_isSome` omits
an unused real-closedness instance, matching its domain-only proof through
`determine_isSome` and `domain_convert`. The count and root-enumeration conversion
theorems retain real-closedness. No computational operation, checker guard or
certificate contract changes.

## Validation and reference scope

The existing `HexSignDetMathlibProofProbe`, `HexRCF.SignDetFieldProofs` and
`HexSignDetMathlib.Diagnostics` modules supply representative producer,
arbitrary-replay, noncanonical-carrier and selected-root applications with
ordinary-kernel axiom guards. This review reuses those examples. Local verification
passes a full `lake build`, the companion/field-proof/probe build, the import DAG, all
406 checked admission cones, published trust scanning, copyright and manual split
checks. The full build reports no warnings in owned companion production modules. The
finite foundation controls include repeated words, empty observations/supports and an
invertible incomplete support. Mathematical probes and source assessment do not
constitute computational performance evidence.

The retained reference audit imports the full manual, field proofs, the five proof
probes, finite/root diagnostics, the integration consumer and the native realization
examples. These representative applications include the existing named consumers of
`Descriptor.buildRoots_roots`; this is not an inventory of every default target or every
repository module. It records references from compiled declaration types and bodies in
that imported environment, plus the transitive axiom sets of owned production constants.
The manifest binds the committed inventory bytes and exact dependency-lock bytes.
The machine inventory is a retained earlier snapshot, not recomputed for the
new proof-client bodies. Its original owned-module hashes remain with the
reference-audit metadata; current reviewed-module bindings are separate.
Generated constants are included in that snapshot: 450 constants, of which all
226 handwritten declarations are matched. Their transitive axiom union is exactly
`propext`, `Classical.choice` and `Quot.sound`. The 28 handwritten declarations without
compiled references are public; every private helper has a compiled user. The [helper
paths](helper-paths.json) additionally trace each private helper through generated
constants to a handwritten production declaration. A zero-reference result does not
establish dead API: tactic/elaborator registration, anonymous examples, external
consumers and unimported modules are outside this reference model. The [separate
reference assessment](zero-references.md) identifies the public characterizations
retained for downstream use rather than deleting useful public statements solely because
no compiled declaration refers to them.

## Remaining acceptance

The companion and core have completed their
[Phase-5 proof acceptance](../sign-det-proof-acceptance.md). The prerequisite
[#10861](https://github.com/kim-em/hex-dev/pull/10861) completed the
[#10377](https://github.com/kim-em/hex-dev/issues/10377) owner Phase-4 attestation.
The Theory acceptance separately discharges the companion’s final API/use,
lint, kernel and documentation requirements. Final computational acceptance,
including its applicable regression checks, remains before the core’s Phase 6. Publication still requires the
[package prerequisites](../real-closure-publication.md).

The [computational foundation assessment](core-foundation.md) separately covers
35 named core declarations and the `System` equality instance. It adds the full
`System.check_eq` guard characterization and updates the core/companion
count-recovery, table, codec, rank-basis and solve clients without changing
their statements or algorithms. The
foundation assessment is separate from the core’s remaining final acceptance.

The [counting and recursive replay assessment](core-replay.md) covers 49 named
declarations in six additional computational modules, both literal equality
instances and the source structure fields. Its leaf/split acceptance API is
used by the existing tree producer proof. This remains partial core acceptance.

The [support-induction and sparse-table assessment](core-tables.md) covers 42
named declarations, reduction equality instances and source fields in four
further modules. Producer hypotheses and root-set interpretation remain
explicit; whole-core quality and phase acceptance are still incomplete.

The [selected-query sign assessment](core-selected.md) covers 19 named
declarations and the certificate fields. Full raw/validated acceptance
characterizations replace Boolean guard unfolding in graph, finite-transport and
coefficient-substitution proofs. This remains partial core review.

The [descriptor and Thom-vector assessment](core-descriptors.md) covers 45
named declarations, the raw equality instance, nine fields and the five
input-error constructors. Full shape and arbitrary-replay acceptance
characterizations support the existing descriptor construction proofs.
This remains partial computational review.

The [completion and full-order assessment](core-completion.md) covers all 17
named declarations and both completion fields. Bidirectional acceptance laws
support the existing binding/comparison projections. This is partial
computational review; whole-library Phase-6 checks remain.

The [common-polynomial comparison assessment](core-comparison.md) covers 27
named declarations and sixteen source structure fields. Bidirectional common
product and joint re-encoding acceptance laws replace guard unfolding in
existing producer proofs. The computational source assessments are complete;
final core Phase-6 acceptance remains separate.

The supplied-replay exports `Descriptor.rootsFrom_coverage` and
`Descriptor.rootsFrom_ordered` generalize the existing producer compositions.
The producer theorems reuse them. Coverage requires accepted full replay and
extraction of the complete actual table; order alone also applies to a partial
row list. The [root-list assessment](core-root-list.md) explains the boundary.
The original reference capture retains its recorded environment. The refreshed
companion capture covers the current 228-declaration API; source review and
compiled-reference evidence remain separate.

The [literal graph and memo assessment](core-dag.md) covers 28 named
declarations, its equality instance and six fields. Validation checks every
stored entry; selection reuses accepted trees only at matching indices and
ordered queries. Literal domain transport preserves those stored trees.

The [prepared-handle and operation-transport assessment](core-handles.md)
covers 25 named declarations and both query-handle fields. Handle existence
is characterized by the original preparation call; replay uses the exact
ordinary descriptor checker. Equal-operation transport preserves literal data,
rather than substituting a merely semantically equivalent descriptor.
This remains partial computational review.

The [graph roundtrip assessment](core-graph-codec.md) covers 30 named
declarations and the six parser-bound fields. The
[stored-coefficient assessment](core-codec-coefficients.md) covers 18 named
traversals and finite-coverage laws. Both distinguish complete literal
reconstruction from arithmetic replay acceptance. The source-name checks
reuse the existing namespace-aware extractor for these groups; they are
local review snapshots rather than a new automatic CI requirement.

The earlier graph-codec and coefficient snapshots remain preserved at
`audit/issue-10575-sign-det-codec-reviewed-v3`. The retained tags are not checked by the current manifests. Their current module and
assessment archive for graph-codec uses
`audit/issue-10575-sign-det-integration-review-input-v1`; the coefficient archive
retains `audit/issue-10575-sign-det-lint-reviewed-input`.
Current byte bindings separately cover the shared documentation, guards and
extractor context. These are local checks; changed inputs require assessment
before rebinding. Complete module hashes also cover fields and anonymous instances
outside the named declaration inventory.

Changes to shared review imports such as `scripts/libgraph.py` or
`scripts/ci/check_benches_mathlib_free.py` invalidate the codec bindings.
These hashes identify the reviewed files; the extractor uses the checkout's
existing import paths. The bindings are checked locally, not by a CI-wide
currency gate.

The [DAG support assessment](core-dag-support.md) covers 74 named declarations
in nine modules, five structure fields and the entry hashing instance.
`Expansion.step_isSome` characterizes success using exactly the supplied
child lookups; the existing bounds proof uses it. Literal encoding and
structural expansion remain separate from arithmetic replay acceptance.
The namespace-aware inventory uses the shared extractor, including the
`Expansion.Valid` abbreviation. This remains partial computational review;
no performance or phase acceptance follows from it.

The DAG-support source snapshot is preserved at
`audit/issue-10575-sign-det-integration-review-input-v1`. Its archive check binds the nine reviewed modules and individual assessment
to that input commit. Current byte checks separately bind shared documentation,
guards and source-extraction helpers. Later context-file edits require assessment
before updating their current bindings; they do not move the historical module
checkpoint. Changes to a reviewed module or its assessment require a new
preserved review checkpoint. Earlier groups retain their individual assessments;
their current bindings include the reviewed manual, guard and checker changes.
The snapshots are checked locally, rather than by a new CI currency rule.

For a clone without the preserved SignDet input tags, fetch them before running the
local binding checker:

```sh
git fetch origin 'refs/tags/audit/issue-10575-sign-det-*:refs/tags/audit/issue-10575-sign-det-*'
python3 reports/sign-det-declaration-review/check_foundation_bindings.py
```

The original compiler-reference archive describes its recorded source. The
`current/` capture covers the current Theory modules; its `--current` checker
verifies their live source bindings and derived reference evidence. Earlier
reference captures remain reproducible at their preserved checkpoints.

Manifest `source_ref` without `input_revision` is a historical review reference.
With `input_revision` it identifies the byte-checked module/assessment archive;
`archive_files` explicitly limits that historical check. All `files` entries
are checked against current bytes, including context files outside the archive.

The graph-codec and stored-coefficient archives use the same module/assessment
scope. Their earlier `codec-reviewed-v3` checkpoint remains preserved. Shared
manual, conformance, index and checker files are current context bindings, so
subsequent assessed edits do not move those archives.

The shared namespace extractor retains namespaces across `mutual` blocks,
handles indentation consistently and checks explicit closing scope names.
Controls cover component-wise namespace closure, mismatched ends and all
38 qualified source names in `Codec/Value.lean`. The control input is bound
as current context; this inventory check does not assess the remaining JSON API.

The [coefficient conversion and dependency-envelope assessment](core-dependencies.md)
covers 34 named declarations, sixteen fields and literal equality/Repr instances.
`Decoded.memo_size` exposes the existing exact memo/packet cardinality and is
used by both selection-bound proofs. Versioned byte parsing, ordered result
bindings and structural dependencies remain separate from the supplied local
reader's mathematical contract. The existing nested dependency fixture is reused;
this assessment does not establish whole-pair acceptance.

The conversion/dependency modules and their individual assessments are archived
at `audit/issue-10575-sign-det-dependencies-input-v3`. Its module/assessment
archive is separate from current manual, conformance and extractor bindings.
The glob fetch command above covers this tag in a clone that lacks it.

This group binds the shared extractor, byte-precheck and codec-law definitions,
tuple/array readers, JSON scalar codecs and the JSON control input as current
context. The module archive remains separate from these assessed context files.
The glob fetch command above also fetches the dependency input tag.

The [certificate serialization and recursive producer assessment](core-serialization.md)
covers 147 named declarations across eleven modules, including the JSON scalar
classes, seven fields and six construction-error cases. `Codec.bindings_iff`
characterizes decode-time context/head/endpoint binding for node and moments and is used by the
existing false-graph reconstruction control. Literal parsing,
reconstruction and arithmetic replay remain distinct. The source extractor
includes the public JSON classes in the namespace-aware group inventory.
Whole-pair lint/reference/performance acceptance remains separate.

The earlier serialization/producer snapshot remains preserved at
`audit/issue-10575-sign-det-serialization-input-v3`. The retained tag is not checked by the current manifest. Its current module and
assessment archive uses `audit/issue-10575-sign-det-lint-reviewed-input`.
The existing SignDet tag fetch command covers both checkpoints. Current
context bindings remain separate from the module and assessment archive.

`Codec.read_nat` and `Codec.read_int` are the natural/integer scalar roundtrip
simp lemmas. The false-graph control proves decode-time bindings through
`bindings_iff`. Query lists and query polynomials are authenticated by replay.
The class inventory control uses a synthetic fixture for plain, protected,
inductive and abbreviation declaration forms.

The [decimal, Unicode, token and JSON parser assessment](core-parser.md)
covers 105 named declarations, recursive data constructors and hash instances.
`Json.readLoop_tokens` characterizes the native parser on emitted token streams
with an arbitrary suffix and a sufficient structural fuel bound accounting
for both width and depth; the actual byte-roundtrip
proof uses it. Native/reference equivalences include malformed input and
insufficient fuel. The low-level parser applies no certificate byte/depth/digit
policy; guarded certificate readers run `Codec.checkBytes`. The trusted printer reader
`Hex.RealClosure.Tower.ReprFormat.readPacket` deliberately uses the unbounded parser;
external input uses bounded byte APIs.
This completes the source declaration assessments, not whole-pair phase acceptance.

The four parser modules and their individual assessment are preserved at
`audit/issue-10575-sign-det-parser-input-v3`. The SignDet tag fetch command
above includes this checkpoint. Current certificate-policy and conformance
inputs are bound separately from the reviewed source archive.

The current lint diagnostic imports both public umbrellas and checks both
production roots, including theorem documentation. Its exact diagnostic guard
permits only three recursive equality auxiliaries and two enum identities
generated by the pinned Lean deriving handler; every additional finding fails. Source
documentation covers the moment-system fields, coefficient coverage laws and
structural node reconstruction. The endpoint roundtrip requires no zero or
equality instance on its coefficient type.

The current graph-codec, coefficient-codec and serialization assessments use
`audit/issue-10575-sign-det-lint-reviewed-input` for their module/assessment
archives. Earlier codec and serialization checkpoints remain preserved.

Current companion imports use the `HexSignDetTheory` names. The retained
Mathlib-named source archives keep their original paths and bytes; current
module records preserve `snapshot_path` for their earlier module hashes.
Family fixture roles follow literal modules in the existing Lake test targets.
Unsupported test-glob expressions fail instead of inventing a production role.

The foundation module and assessment archive uses
`audit/issue-10575-sign-det-current-reviewed-input-v8`. Original companion
snapshot paths and hashes are also checked against their recorded source commit.

## Theory acceptance

The [Theory acceptance](theory-acceptance.md) records the companion's subsequent
Phases 6–7, including explicit source parameters, current kernel checks and the
individual API-retention decisions. The older `current/` compiler capture is a
preserved v10 snapshot; default archive verification remains valid and its
current-source mode refuses the later source changes. Computational Phase-6
acceptance and publication eligibility remain separate.
