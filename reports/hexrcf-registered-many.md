# Ordered coefficients from one registered real model

`Gather.run_registered_many` preserves an ordered nonempty list of values from
`Context.ofBase provider.context.finish`. The catalog contains the rational
entry and the caller's sole inserted nonrational prefix. Insertion derives the
nonempty key path; automatic selection chooses that exact prefix at depth zero.
The original model's identity factory is derived for every coordinate. No
factory-success or independently asserted coefficient agreement is a premise.
The legacy `Gather.run_registered` is proved as the singleton case. Empty owners
retain the existing rational-first selection.

The [public adapter](../adapters/HexRCF/RealCoefficients/RegisteredGather.lean)
uses the actual catalog, gathering and model laws. It supplies native producer
semantics for arbitrary shared Boolean syntax and one real quantifier, not
source authentication or a frozen certificate. All coordinates use the same
already authenticated real prefix; no separate registrations imply joint
transcendence. Tower-extension owners are outside this specific theorem.

The [ordinary-kernel conformance](../conformance/HexRCF/RegisteredGatherConformance.lean)
uses the actual owner Liouville model. It identifies the two original coordinates
as `L = liouvilleNumber 2` and `L⁻¹`, proves successful installation directly,
and retains their ordered interpretation through gathering. The sentence
`∃ x, x² = L ∧ x² L⁻¹ = 1 ∧ 1 < x` requires a further root over the coefficient
field and produces true. Exchanging the two coordinate occurrences produces
false: `L > 1`, so `L⁻¹ < 1`. These decisions use proved real semantics and
ordinary-kernel checked provider bounds.

Standalone non-squarefree inputs test `(x² − L)² = 0` with both original domain
atoms. The `(0, 2]` existential produces true, the `(2, 3]` existential produces
false, and `(x² − L)² < 0` is false everywhere. The repeated-root test contains
no additional squarefree root atom that could conceal missing double roots.
The domain atoms belong to the sentence adapter; these checks do not exercise
the real-coefficient source reifier's `Set.Ioc` lowering.

The [compiled catalog controls](../conformance/HexRCF/GatherCatalog.lean)
reuse the existing native one-provider fixture. They execute the paired
further-root/common-root searches, reject the exchanged sentence, verify the
selected signature, and execute the standalone repeated-root and negative-square
sentences. This native fixture uses the owner's actual Liouville approximation
and progress laws. It is not asserted to be literally the noncomputable model
context used by the source-value theorems. Compiled Booleans are diagnostic
controls and supply no proof evidence.

The conformance audits retain the singleton's fourteen complete inventories and
add thirteen for the general API, ordered values, pair semantics, provider bounds
and repeated-root decisions. All twenty-seven contain exactly `propext`,
`Classical.choice` and `Quot.sound`. Verification records and source hashes are
bound in the [context record](data/hexrcf-registered-many/context.json).
Build durations are operational observations, not scientific timing or scaling
measurements. The [singleton record](hexrcf-registered-gather.md) remains bound
to its exact historical source tree; its measurements and successful logs are
not relabelled as evidence for this extension.

A bounded `rcf_constant` registration does not itself construct this total model.
These APIs do not quote frozen tactic certificates, collect all source divisor
guards or establish accepted-certificate completeness. Generic literal
context/root/row assembly, all-live packing/inverse assembly and recursive
finite-joint infinitesimal realization retain the obligations in the
[adapter inventory](hexrcf-adapter-evidence.md).
