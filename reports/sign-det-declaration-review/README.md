# Sign-determination companion proof and API review

The [assessment](companion.md) treats all 226 handwritten declarations in the 37
production modules exported by `HexSignDetMathlib`, including private helpers and the
fields of `Node.Counted`. The [manifest](manifest.json) records the names and module
hashes at source commit `7433524020514b3907653c5a3fe3b95212ae8f59`, together with the
current reviewed module hashes after polishing. Nine checked-system proof
clients use the foundation acceptance API; their updated bindings are also
recorded in the foundation manifest. Generated projections and elaborator
declarations are not separate assessment entries. The computational library's earlier inventory contains 693 handwritten
declarations in 58 production modules. The separate foundation, replay, table and selected-sign
assessments below cover 145 named declarations, including newly added APIs; the
remaining computational modules still require individual assessment. This companion review does not attest completion of the whole pair or any
release phase.

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

The companion and core record Phase 5 through their
[proof acceptance](../sign-det-proof-acceptance.md). The prerequisite
[#10861](https://github.com/kim-em/hex-dev/pull/10861) completed the
[#10377](https://github.com/kim-em/hex-dev/issues/10377) owner Phase-4 attestation.
This declaration assessment does not itself establish Phases 6–7. The separate computational declaration review, final lint/docstring/use
acceptance, applicable conformance and declared computational regression checks
remain before Phase 6. Publication still requires the
[package prerequisites](../real-closure-publication.md).

The [computational foundation assessment](core-foundation.md) separately covers
35 named core declarations and the `System` equality instance. It adds the full
`System.check_eq` guard characterization and updates the core/companion
count-recovery, table, codec, rank-basis and solve clients without changing
their statements or algorithms. The
remaining core modules and whole-pair Phase-6 checks are still outstanding.

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
