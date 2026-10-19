# Kernel factorization and common-field quotation

The question is whether an existing kernel factorizer can remove the
common-field certificate gap for the fixed degree-eight example in
[CertificationProofs](../conformance/HexRCF/CertificationProofs.lean).
`QAdjoin.common` proposes the exact polynomial
`[-2, -24, 169, 70, -127, -70, 6, 8, 1]` from the selected quartic root and √2.
The existing finite quadratic-norm, free-witness and multi-prime producers
still decline for this literal. Their refusal is not a reducibility claim.

The existing public `bangZPolyIrred` API, exposed as `irreducibility!`, proves
this literal irreducible when the calling module imports the factorizer's
executable closure with `import all`. The experiment copies that closure from
the owner's actual `FactorPolyTests` header. It proves both `Irreducible` and
`CheckedIrreducible`. Lake passes 9,675 jobs; the target's 9.8-second observation
is an unpaired operational build, not a scientific complexity measurement.
Printed complete theorem axiom inventories contain only `propext`,
`Classical.choice` and `Quot.sound`. No compiled Boolean or admission supplies
proof evidence. This path runs full kernel factorization; it is not the
adapter's frozen certificate checker.

An ordinary import of a helper module does not make that private executable
closure available to its consumer. Lean rejects `public import all`. A carrier
with separate ordinary public imports and private `import all` directives
builds, but its normal-import consumer fails at `polynomial.factorize` during
the kernel precheck. The failed consumer's elaboration-generated admitted
terms are failed-build diagnostics, never accepted proofs.

Thus this one polynomial has an existing ordinary-kernel proof route with
privileged caller imports, but the experiment does not repair ordinary
`import HexRCF.RealCoefficients` clients or establish complete common-field
quotation. The remaining prerequisite is an ordinary-import checkable
irreducibility interface covering these presentations. The adapter does not
export private bodies, introduce another certificate language or duplicate
lower-library mathematics.

The [context and digests](data/hexrcf-common-kernel/context.json),
[successful proof source](data/hexrcf-common-kernel/OcticKernelProof.lean.txt),
[carrier source](data/hexrcf-common-kernel/KernelClosure.lean.txt),
[failed consumer source](data/hexrcf-common-kernel/OcticPublicImport.lean.txt),
[successful build](data/hexrcf-common-kernel/octic-kernel-factor-proof-checked.log.gz)
and [failed consumer build](data/hexrcf-common-kernel/octic-public-private-import-proof.log.gz)
retain the exact experiment at the historical source revision. The source
snapshots use an external Lake project requiring that Hex checkout. They are
build-only Mathlib experiments and are not executable benchmark targets.
