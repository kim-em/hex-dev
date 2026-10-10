# Supplied common-field irreducibility

`CommonTactic.certify` first looks for an existing `ZPoly.CheckedIrreducible`
instance for the exact quoted polynomial. It checks that the expression evaluates
to the runtime polynomial, then uses the base tactic's ordinary proof checker:
exact type, complete permitted axiom dependencies, safety and an uncached kernel
check. Only absence of an instance enters the existing finite certificate
producers. A rejected supplied proof is terminal. Already matched source-leaf
proofs retain their previous priority.

Lean's instance search uses its instance transparency. The regression therefore
states the supplied class on the frontend's exact `DensePoly.ofCoeffs` literal;
a definition using `ofList` alone did not match that target in the experiment.
This is an existing proof-class interface, not a new irreducibility certificate
language or a new number-field representation.

The [construction module](../conformance/HexRCF/SuppliedIrreducible.lean) proves
irreducibility of `[-2,-24,169,70,-127,-70,6,8,1]` with the owner's existing
`irreducibility!` tactic and its private executable closure. Only its public
polynomial, ordinary theorems and instance are exposed. The
[fresh consumer](../conformance/HexRCF/SuppliedIrreducibleProofs.lean) has ordinary
imports and proves `∀ x, x² + α + √2 > 0` for the existing selected quartic α.
Its emitted proof retains the supplied instance. All four full inventories
contain exactly `propext`, `Classical.choice` and `Quot.sound`.

The consumer's kernel irreducibility check references the already proved theorem
rather than reducing the factorizer. Native common-field construction during
search still runs its normal algorithm. The historical
[failed factorizer-import experiment](hexrcf-common-kernel.md) attempted to run
factorization in an ordinary-import client; it remains valid historical evidence
and is not the same operation as theorem reuse.

Controls accept the exact runtime/expression pair and reject a mismatched runtime
polynomial. A synthetic admitted local class is rejected even for a quartic
whose existing certificate producer succeeds; no certificate fallback hides the
failure. The local state is restored, and normal certification then succeeds.
These synthetic terms are never retained as theorem proofs. Existing
`CertificationProofs` and `PreparedCoefficients` pass independently without
importing the supplied octic instance, preserving the original no-instance
refusal, source/divisor authentication and rollback controls.

The optional adapter's existing module and the existing `HexConformance` target
carry the change and both proof modules. No new library, workflow, job, formula
syntax or base-umbrella dependency is added. The rcf manual explains supplied
instances separately from automatic certificate coverage and retains the
existing examples. Four desktop/narrow captures inspect the changed paragraphs;
their widths fit the viewport. This is not a whole-page overflow claim.

[Source-bound records](data/hexrcf-supplied-irreducible/context.json) retain the
actual source hashes, accepted local checks, failed exploratory builds and
inspection bindings. The fresh proof-module observations, including the
6.4-second external and 7.7-second repository builds, are unpaired operational
observations, not scientific speedup or complexity measurements. No new timing
sweep, memory or generic performance claim is made.

This supplies one previously proved common polynomial through an ordinary-import
frontend. It does not establish automatic irreducibility certification, complete
algebraic source acceptance, generic frozen context/root/all-live assembly or
recursive whole-joint finite realization. #10358 remains open.
