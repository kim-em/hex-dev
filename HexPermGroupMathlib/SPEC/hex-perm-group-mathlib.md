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
in the computational SPEC, including the nonempty-block hypothesis for
the faithful wreath action.

The immediate dependency is `HexPermGroup`, plus Mathlib. Extract the
graph-independent `Perm.toEquiv` and `Perm.ofEquiv` conversions from
`HexGraphIsoMathlib` when migrating that consumer. This library must not
depend on graph isomorphism or a classification database.

The library also provides the kernel replay theorems and the `perm_group`
tactic specified in
[hex-perm-group, Kernel replay in Mathlib](../../HexPermGroup/SPEC/hex-perm-group.md#kernel-replay-in-mathlib),
and the examples of
[User-facing examples](../../HexPermGroup/SPEC/hex-perm-group.md#user-facing-examples).
The correspondence modules form a correspondence-only layer, with comparator
absence class **correspondence-only-layer**. The kernel replay theorems and
`perm_group` are measured by fresh-module proof probes in
`bench/HexPermGroupMathlib/ProofProbe`, declared in `libraries.yml:
proof_probes` with a Phase 4 input family `kernel-certificates`, as specified in
[Complexity, benchmarks and placement](../../HexPermGroup/SPEC/hex-perm-group.md#complexity-benchmarks-and-placement).

Build-only examples in
`HexPermGroupMathlib/Tests.lean` exercise membership, exact order, stabilizers,
nonnormal-subgroup cosets, a nonfaithful induced action, minimal blocks,
normal and derived subgroups, rank/unrank and product embeddings.
Runtime conformance and compiled benchmarking belong
to the computational owner below. Kernel replay of `Kernel.check` is measured
by this library's proof probes.

Computational conformance owner: `HexPermGroup`.

Computational performance owner: `HexPermGroup`.
