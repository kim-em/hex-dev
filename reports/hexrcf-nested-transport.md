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
first-field scalar inventory. These finite records are explicit premises of
this fixed-parent fixture. The owner reader independently checks the joint
packet. The [literal field laws](../conformance/HexRCF/NestedTransport/Fields.lean)
compose actual owner facts, and [restoration](../conformance/HexRCF/NestedTransport/Restore.lean)
retains exact keys/signs for later lookup without reducing the joint graph again.

The [full root packet](../conformance-fixtures/HexRCF/nested-transport.json)
passes guarded ordinary replay and complete source binding. The
[model](../conformance/HexRCF/NestedTransport/Model.lean) uses the actual first-step
model, context equality and packing closure to construct the returned
conversion interpretation. Its root identity links the checked converted
root to the original selected root. The
[source proof](../conformance/HexRCF/NestedTransport/Source.lean) derives
`∃ x : ℝ, x²=Real.sqrt 2 ∧ 1<x ∧ x<2` from root membership, literal endpoint
fields and the checked √2 coefficient identity. It uses no earlier row-truth
or existential source proof.

A [fresh ordinary module](../conformance/HexRCF/NestedTransport/Ordinary.lean)
re-derives the root identity and source proof, rechecks actual theorem bodies,
and pins the exact standard three-axiom inventory. Local scans require actual
root laws and exclude the earlier row/source proof references; imported
constants remain leaves. The actual acceptance/refusal kernel diagnostics
exclude native root and scalar production.

The [refusal controls](../conformance/HexRCF/NestedTransport/Controls.lean)
reject a valid different original descriptor as `binding`, missing scalar
records and changed endpoints as `evidence`, and a zero guard as `divisor`
before parsing null subject/graph data. No exception or diagnostic-string
fallback is used. The existing constructor renderer reproduces both packets
and shared literal subtrees; joint constructors are split only at a dependency
boundary to meet the new-file limit.

The optional adapter remains outside the base HexRCF import. No new formula
syntax, owner proof, field instance on raw representatives or CI job is added.
This fixture does not provide general source/provider history, all-live packing,
complete root/cell coverage, automatic coefficient certification or algebraic
completeness. Source-to-guard authentication remains a frontend obligation.
No performance or scaling claim follows from this proof-acceptance example.

The [validation manifest](data/hexrcf-nested-transport/context.json) retains
exact source hashes, successful ordinary Lake integration/render logs, the
recursive admission-checker regression result and six desktop/narrow captures.
The integration command completes 14,208 jobs; full rendering completes 14,169.
The source commit includes the tested Python regression after the Lean/render
commands, with identical Lean/manual bytes. This is proof/build validation,
not a timing experiment.
