# hex-perm-group-mathlib

Correspondence between executable finite permutation groups and subgroups
of `Equiv.Perm (Fin n)`. The complete contracts, including the headline
membership/cardinality theorem and the coset conventions, are specified in
[hex-perm-group, Mathlib companion](../../HexPermGroup/SPEC/hex-perm-group.md#mathlib-companion-and-trust-boundary).

The correspondence includes sign and cycle type, ranking and uniform
supplied-index sampling, finite actions with their images and kernels,
complete set and subgroup search, blocks and primitivity, normal closure,
core and derived series, and direct and imprimitive wreath products.
Prove the universal properties and action-compatible equivalences stated
in the computational SPEC, including the `0 < n` hypothesis on the
semidirect-product equivalence for the wreath action.

The immediate dependency is `HexPermGroup`, plus Mathlib. The
graph-independent `Perm.toEquiv` and `Perm.ofEquiv` conversions live in
`HexPermGroupMathlib/Perm/Basic.lean`. This module does not install a
`Group (Hex.Perm n)` instance; that optional structure and the multiplicative
equivalence remain in `HexPermGroupMathlib/Perm.lean`. This library must not
depend on graph isomorphism or a classification database.

`HexPermGroupMathlib/Generated.lean` contains the lightweight mathematical
interface: `generated_iff_mem`, `hasOrder_iff_card`,
`generatesAll_iff_eq_top`, and their translations for a list of generators.
It imports only the computational generation/order semantics and the basic
conversions. `Word.lean`, `Order.lean` and `Kernel.lean` retain the old entry
points. The tactic adapter imports this semantic interface and uses
`Hex.PermGroup.Tactic.{Input,Goal,prepare,replay,render}`; it does not inspect
certificate representations or create packing/checker declarations itself.

The library translates the Mathlib-free kernel replay theorems and extends
the `perm_group` tactic from `HexPermGroup`, as specified in
[hex-perm-group, Kernel replay in Mathlib](../../HexPermGroup/SPEC/hex-perm-group.md#kernel-replay-in-mathlib),
and the examples of
[User-facing examples](../../HexPermGroup/SPEC/hex-perm-group.md#user-facing-examples).
Because it extends a tactic, its Phase 4 deliverable is the proof track: example
files running the kernel replay theorems and `perm_group` in
`bench/HexPermGroupMathlib/ProofProbe`, declared as its `libraries.yml`
`proof_probes` root and built by CI on every PR.

The library provides Mathlib's `Random m (Element G)` instance for every
monad `m`, built from `Group.randomElement`, which applies `Group.sampleFrom`
to the rejection sampler `randomIndex` over a `RandomGen` generator. Its
contract, specified in
[hex-perm-group, Ranking and sampling](../../HexPermGroup/SPEC/hex-perm-group.md#ranking-and-sampling),
is that, for a generator whose draws are independent and uniform on its range,
each element has probability within `2^-128` of `1 / order G`, and exactly
`1 / order G` conditional on the index draw accepting within its 128
attempts. It does not use Mathlib's `randFin`, which reduces one draw modulo
the bound and is biased. `HexPermGroupMathlib/Tests.lean` checks with a fixed
`mkStdGen` seed that draws are members and that 2000 draws reach every
element of a group of order 8.

Build-only examples in
`HexPermGroupMathlib/Tests.lean` exercise membership, exact order, stabilizers,
nonnormal-subgroup cosets, a nonfaithful induced action, minimal blocks,
normal and derived subgroups, rank/unrank and product embeddings.
Runtime conformance and compiled benchmarking belong
to `HexPermGroup`. Kernel replay of `Kernel.check` is exercised by this
library's proof probes.

`HexPermGroupMathlib/TacticTests.lean` imports only the lightweight tactic
adapter and checks all four goal forms, set and subgroup definitions, coerced
Finsets, set builders, invalid-image fallback, degrees zero and one, false
goals and the absence of the optional Hex group instance. Source replay tests
remain in `CertificateTests.lean`; computational interface tests also cover
bad canonical equalities and rollback after a kernel rejection.
