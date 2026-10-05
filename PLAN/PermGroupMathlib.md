# Permutation groups in Mathlib

Add a dependency on the released `hex-perm-group` library and move the
correspondence layer into Mathlib in small, independently reviewable PRs.
Keep computational algorithms, certificate soundness and proof replay in Hex.

## Ownership

| HexPermGroup | Mathlib |
| --- | --- |
| Permutation representation and operations | Conversions to `Equiv.Perm (Fin n)` |
| `Generated`, `HasOrder`, `GeneratesAll` | Correspondence with closure, cardinality and the top subgroup |
| Certificate producer, checker and soundness | Goal recognition and generating-set normalization |
| Packing, chunking and auxiliary declarations | Translation of computational conclusions |
| `perm_group` syntax, configuration, tracing and source rendering | Extension of the same syntax to Mathlib goals |
| Chains, ranking, actions and subgroup algorithms | Mathematical correspondence and universal properties |

The supported computational interface is `Hex.PermGroup.Tactic`:
`Input`, `Goal`, `Prepared`, `prepare`, `replay` and `render`. The adapter
supplies original permutations and optional canonical expressions with
round-trip equalities. Hex checks the packing transports and the certificate.
Goal replay and source rendering share one prepared result.

The semantic modules `Generated`, `Order` and `Perm.Images` do not import
the algorithms. Basic Mathlib conversions do not install a group instance
on `Hex.Perm n`. The optional group instance and multiplicative equivalence
remain separate from the initial tactic integration.

## Initial Mathlib PR

Publish the Hex preparation through the guarded release workflow before
opening this PR. Require a verified immutable release of
`leanprover/hex-perm-group`; its only Hex dependency is `HexBasic`.
Add both import roots to Mathlib's cache support.

Limit the mathematical and tactic changes to these files:

- `Mathlib/GroupTheory/Perm/Hex.lean`: basic conversions and literal-image wrapper.
- `Mathlib/GroupTheory/Perm/Hex/Generated.lean`: generation, order and full-generation translations.
- `Mathlib/Tactic/PermGroup.lean`: the Mathlib goal adapter.
- `MathlibTest/PermGroup.lean`: the supported presentations, false goals,
  edge cases, M11 and axiom checks.

Preserve existing syntax, configuration and goal forms. Normalize the
generating set once, retaining its equality to list membership. Translate
membership and order through their biconditionals, and top-subgroup goals
directly through full generation. The Mathlib patch contains no certificate
soundness proof and no packing or checker implementation.

## Subsequent correspondence PRs

After the initial PR lands, replace the corresponding companion modules
with public imports and compatibility aliases, updating the Mathlib pin in
the monorepo. Never keep parallel implementations. Subsequent migrations
also wait for their prerequisites and target Mathlib's default branch.

Migrate the remaining correspondence in dependency order: the optional
group structure and cycles; words and orbit certificates; checked groups
and containment; ranking, cosets and sampling; finite actions; complete
search; blocks and primitivity; normal closure and derived series; products
and wreath products. Each PR should transport existing Hex results rather
than repeat an algorithmic argument. Put any missing computational theorem
in Hex first and release it before adding its Mathlib translation.

## Verification

Build the monorepo, existing Mathlib tests, graph consumers, proof probes and
manual chapter. Build a fresh Mathlib-free consumer of the staged split
libraries, and compile emitted source in a separate process for both APIs.
Check failure rollback, bad canonical witnesses and the standard axiom set
(`propext`, `Classical.choice`, `Quot.sound`). Run the dependency, trust and
release-manifest checks.

Compare kernel replay on the retained M11–Co3 inputs, including classical
M11, using adjacent AB/BA arms on an automatically leased CPU. Retain all
completed samples and permit at most one unchanged rerun after an
inconclusive comparison. Each workload's mean kernel time must stay within
10% of the baseline. Keep the initial Mathlib patch free of benchmark and
certificate machinery.
