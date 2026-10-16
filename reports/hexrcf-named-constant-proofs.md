# Fresh importing checks for supplied pi and exp registrations

[`NamedConstantProofs`](../conformance/HexRCF/NamedConstantProofs.lean) imports
the existing caller-supplied registrations and tactic examples, then rechecks
all four actual theorem bodies using the tactic's ordinary kernel checker.
Each example's transitive project dependencies must include its actual pi or
exp registration. The complete axiom closure is exactly `propext`,
`Classical.choice` and `Quot.sound`.

The checked examples are `∀ x, x² > π−4`, `∀ x, x²+exp 1>2`,
`∃ x, x=exp 1 ∧ 2<x ∧ x<3` and the guarded coefficient `1/(4−π)` in a
positive quadratic. The original module separately rejects cancelled zero
pi denominators and deliberately uninformative zero-containing bounds.
The importing audit validates those four positive proof bodies; it does not
claim a new evaluation of every negative control.

At source `05732a9e1b`, the 11,150-job build passes in 1 min 53.612 s,
peak 8.2 GiB/no swap. The original theorem module rebuilt in 30 s and its
fresh importing audit in 29 s. These are shared-host build observations,
including startup and reused dependencies, not a matched timing study.
All own builds are serial under a hard aggregate 32 GiB cap, with swap
disabled and two Lean threads. The [source-bound record](data/hexrcf-named-constant-proofs/context.json)
retains exact file hashes and raw output.

This adds fresh consumer evidence to existing finite successes. It supplies
no new pi/e approximation procedure, requested-width, convergence or relative
transcendence law, and no general named-constant root algorithm. Full #10358
remains open for its remaining authentication, strict replay, completeness,
realization and runtime/evidence obligations.
