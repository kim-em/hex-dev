# Fresh importing checks for supplied pi and exp registrations

[`NamedConstantProofs`](../conformance/HexRCF/NamedConstantProofs.lean) traverses
the dependencies of the four existing caller-registered tactic goals and
rechecks all 42 reachable theorem bodies in their original `NamedConstants`
module, including auxiliary proofs, with fresh ordinary-kernel declarations.
Each goal must depend on its actual pi or exp registration. The complete
transitive axiom closure is exactly `propext`, `Classical.choice` and
`Quot.sound`. Imported library bodies are not all re-added. The exact original
module theorem inventory is retained in the
[current source-bound record](data/hexrcf-named-constant-proofs/revision/context.json).

The goals are `∀ x, x² > π−4`, `∀ x, x²+exp 1>2`,
`∃ x, x=exp 1 ∧ 2<x ∧ x<3` and a positive quadratic with guarded
coefficient `1/(4−π)`. The original module separately rejects cancelled
zero pi denominators and deliberately uninformative zero-containing bounds.
The importing audit's positive body coverage does not claim a new evaluation
of every negative control.

At source `d2627df9111717a92029321280b2b92955e095d8`, the deep audit is included
in the 11,783-job compatibility selection and final 11,765-job audit/manual
selection. Complete logs and exact source hashes, including the current
Lake file, are linked from the record. The audit uses `maxHeartbeats := 12000000`
and `maxRecDepth := 32768`. Own builds are serial under a shared hard 32 GiB cap,
with no swap and two Lean threads. Build times include reused dependencies
and are not matched timing or scaling studies.

The earlier [record at 05732a9e1b](data/hexrcf-named-constant-proofs/context.json)
retains the 11,150-job build and its four top-level proof checks. That evidence
does not establish the 42-body auxiliary audit; the current record does.
Metadata/DAG/umbrella/copyright/line/admission/relative-link/diff checks pass
with the scopes recorded in the combined evidence.

These are supplied-registration finite successes. The adapter adds no pi/e
approximation procedure, requested-width, convergence or relative transcendence
law, and no general named-constant root algorithm. Full #10358 remains open
for its remaining authentication, replay, completeness, realization and
runtime/evidence obligations.
