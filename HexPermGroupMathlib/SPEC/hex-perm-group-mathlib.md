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

At activation set `correspondence_only: true`. The comparator absence class
is **correspondence-only-layer**. Build-only examples in
`HexPermGroupMathlib/Tests.lean` exercise membership, exact order, stabilizers,
nonnormal-subgroup cosets, a nonfaithful induced action, minimal blocks,
normal and derived subgroups, rank/unrank and product embeddings.
Runtime conformance and benchmarking belong
to the computational owner below.

Computational conformance owner: `HexPermGroup`.

Computational performance owner: `HexPermGroup`.
