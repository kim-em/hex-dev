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

## Dependency prerequisites

Before opening the Mathlib PR, verify the dependency layout with the candidate
Mathlib dependency, rather than only building the four new modules in isolation.
Development must provide each module exactly once. Use local Lake packages for
HexBasic and HexPermGroup that point at the monorepo sources, removing the root's
competing library declarations. Keep Mathlib's inherited dependency pins in the
manifest and use Lake's package overrides for the development source providers.
Direct requirements with different pins fail Mathlib's cache manifest check. Update graph,
release and cache tooling to understand the local package descriptors, and build
both the complete monorepo and fresh released consumers with that layout.

Mathlib pins one tested Hex release. A later shared Hex release does not move
that pin automatically. Mathlib's cache currently rejects divergent direct and
transitive dependency pins. Before publishing the integration, establish a release
policy that reconciles this constraint with Hex's shared-version cross-repository
pins, or implement and verify cache support for the chosen override policy.
The release consumer check must cover a subsequent Hex release against a fixed
Mathlib pin, with unique providers and working cache support.

Audit the imports reachable from the basic correspondence and tactic. Import
only the required HexBasic modules. Helpers required by this closure belong in
Hex namespaces; optional compatibility imports can remain in other modules.
Record and test the actual exported declarations, including scoped instances,
so that importing Mathlib does not introduce Hex additions to core namespaces.
Rebuild affected consumers and refresh benchmark evidence when imports change.

Provide a toolchain-adaptation route before making the computational packages
Mathlib dependencies. Coordinate their registration in `downstream-lean4` and
any nightly exports with its current process; `lean-pr-testing-*` branches are
obsolete. The route must bring adaptations back to hex-dev and use generated,
consumer-checked exports for mirrors, without overwriting release `main` or
advancing the shared release baseline. Verify one nightly and one Lean PR
adaptation through the registered route.

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
with public imports, updating the Mathlib pin and development package layout
in the same change. Basic, Generated and Tactic become import-only shims; do
not alias an unchanged name or register the extension again. Add compatibility
aliases only for names that actually move. Never keep parallel implementations. Graph consumers must use a supported
normalization API or a companion compatibility wrapper, rather than depending
on private Mathlib adapter helpers. Subsequent migrations
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
inconclusive comparison. Pool every completed sample of each workload, including
any permitted unchanged rerun. A minor change that preserves most kernel work
does not reset this pool. Report distinct implementations separately as well;
restart a comparison only for a change expected to move the measured work.
Each pooled mean kernel time must
stay within 10% of the baseline. Keep the initial Mathlib patch free of benchmark and
certificate machinery.
