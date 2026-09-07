# hex-perm-group-mathlib

Correspondence between executable finite permutation groups and subgroups
of `Equiv.Perm (Fin n)`. The complete contracts, including the headline
membership/cardinality theorem and the coset conventions, are specified in
[hex-perm-group, Mathlib companion](hex-perm-group.md#mathlib-companion-and-trust-boundary).

The immediate dependency is `HexPermGroup`, plus Mathlib. Extract the
graph-independent `Perm.toEquiv` and `Perm.ofEquiv` conversions from
`HexGraphIsoMathlib` when migrating that consumer. This library must not
depend on graph isomorphism or a classification database.

At activation set `correspondence_only: true`. The comparator absence class
is **correspondence-only-layer**. Build-only examples in
`HexPermGroupMathlib/Tests.lean` exercise membership, exact order, stabilizers
and nonnormal-subgroup cosets. Runtime conformance and benchmarking belong
to the computational owner below.

Computational conformance owner: `HexPermGroup`.

Computational performance owner: `HexPermGroup`.
