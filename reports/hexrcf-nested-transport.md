# Frozen transport through a second selected-root context

The adapter's existing `RootTransport.readWith` checks an original selected
root after its coefficient context has been rebuilt. The
[reader](../conformance/HexRCF/NestedTransport/Read.lean) uses equal supplied
coefficient maps and operation dictionaries, restores the literal descriptor,
and compares every mapped source field. The actual converted descriptor
selects the same root through the owner's `Conversion.Model.root` law.

The fixed example starts with the authenticated positive √2 parent, moves its
selected defining root into that parent, and then restores the further root
of X²−√2 over the rebuilt context. It retains the supplied exact frame and
context signature. The [frame](../conformance/HexRCF/NestedTransport/Frame.lean)
proves equality with the owner's actual descriptor serialization; the
[context](../conformance/HexRCF/NestedTransport/Context.lean) uses the owner's
`adjoin_root_eq`. This checks two concrete steps, not arbitrary provider history.

[Supplied operations](../conformance/HexRCF/NestedTransport/Operations.lean)
use the owner's `Element.fact*` dictionaries at the higher level and cached
operations in its predecessor. A literal reduction policy and direct use of
shared `DensePoly.divModMonic` are proved equal to `Context.factReduce` and
`Context.reduce`. That proof retains the original defining polynomial and
policy. It adds no division, root-search, gcd or sign algorithm. The policy
proof itself passes the ordinary kernel's producer guard.

The [joint scalar packet](../conformance-fixtures/HexRCF/nested-transport-signs.json)
provides −X, X, 1−X, 2−X and 4−X at the same selected root.
Fourteen proved rational predecessor literals supplement the existing
first-field scalar inventory. Two additional higher-level constant records
for 1 and 2 use the authenticated parent sign. These finite records are explicit premises of
this fixed-parent fixture. The owner reader independently checks the joint
packet. The [literal field laws](../conformance/HexRCF/NestedTransport/Fields.lean)
compose actual owner facts, and [restoration](../conformance/HexRCF/NestedTransport/Restore.lean)
retains exact keys/signs for later lookup without reducing the joint graph again.

The standalone root-reader acceptance additionally retains detailed missing-record
diagnostics; the full read separately checks mapped binding.

The [full root packet](../conformance-fixtures/HexRCF/nested-transport.json)
passes guarded ordinary replay and complete source binding. The
[model](../conformance/HexRCF/NestedTransport/Model.lean) uses the actual first-step
model, context equality and packing closure to construct the returned
conversion interpretation. Its root identity links the checked converted
root to the original selected root. The
[source proof](../conformance/HexRCF/NestedTransport/Ordinary.lean) derives
`∃ x : ℝ, x²=Real.sqrt 2 ∧ 1<x ∧ x<2` with the actual converted root as witness. The conversion identity links it
to the original descriptor; that descriptor supplies root membership, literal
endpoint fields and the checked √2 coefficient identity. It uses no earlier row-truth
or existential source proof.

A [fresh ordinary module](../conformance/HexRCF/NestedTransport/Ordinary.lean)
derives the root identity and source proof, rechecks actual theorem bodies,
and pins the exact standard three-axiom inventory. Every theorem in the
new conformance modules also receives a transitive axiom audit. Local scans require actual root laws, with imported constants as leaves.
A separate scan follows all project library and conformance types and bodies,
excluding earlier row-truth and existential source proofs. Only upstream
packages, which are built before this project, remain leaves. The actual acceptance/refusal kernel diagnostics
exclude native root and scalar production.

The [refusal controls](../conformance/HexRCF/NestedTransport/Controls.lean)
reject a valid different original descriptor and a self-consistent packet
with a wider endpoint as `binding`. Removing one higher-level record,
removing all records, and changing only the subject endpoint reject as
`evidence`. Removing the required predecessor literal 98/81 prevents joint
packet decoding; a zero guard rejects as `divisor`
before parsing null subject/graph data. No exception or diagnostic-string
fallback is used. A retained native emitter regenerates both packets exactly and produces the
wider-endpoint control. Production is untrusted and separate from replay.
The existing constructor renderer reproduces all three packets
and shared literal subtrees; joint constructors are split only at a dependency
boundary to meet the new-file limit.

The optional adapter remains outside the base HexRCF import. No new formula
syntax, owner proof, field instance on raw representatives or CI job is added.
This fixture does not provide general source/provider history, all-live packing,
complete root/cell coverage, automatic coefficient certification or algebraic
completeness. Source-to-guard authentication remains a frontend obligation.
No performance or scaling claim follows from this proof-acceptance example.

The [validation manifest](data/hexrcf-nested-transport/closure-context.json)
binds committed source `d7cef47198`, thirty source hashes and retained audit, admission-scan and DAG
records. The [render/producer manifest](data/hexrcf-nested-transport/final-context.json)
retains its exact source, three successful build records, three driver hashes
and six current captures. Those inputs and manual bytes are unchanged by the
dependency-scan correction. Integration completes 14,218 Lake jobs; full
rendering completes 14,169. The axiom audit checks every theorem in the new
conformance modules, including private helpers. The recursive admission scan
covers 456 roots and 1,351 local modules; its eleven tests pass. Generated
literals, DAG/umbrella, copyright, line counts, manual split and diff checks pass.

[Fixture provenance](data/hexrcf-nested-transport/final-fixture-provenance.json)
retains the native emitter and its successful output, and binds all three
regenerated JSON pairs to the same committed inputs. It is reproducibility
evidence, not proof evidence. The portable render driver and browser driver
are also hashed. The new paragraphs fit their 343-pixel narrow and 752-pixel
desktop content widths; this is no claim about overflow elsewhere in the manual.
The [initial manifest](data/hexrcf-nested-transport/context.json) and
[intermediate manifest](data/hexrcf-nested-transport/review-context.json), including
the eleven admission-checker tests, retain their separate source-bound records. Subsequent report/evidence edits do
not change the tested Lean or manual bytes. This is proof/build validation,
not a timing experiment.
