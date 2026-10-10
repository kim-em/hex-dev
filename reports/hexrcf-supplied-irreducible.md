# Supplied common-field irreducibility

`CommonTactic.certify` binds the quoted expression to the runtime polynomial
before either certification route. It then looks for an existing
`ZPoly.CheckedIrreducible` instance for that exact literal and uses the base
ordinary proof checker: exact type, complete permitted axiom dependencies,
safety and an uncached kernel check. Only absence of an instance enters the
existing finite certificate producers. Rejected proofs and instance-search
resource errors are terminal. Already matched source-leaf proofs retain their
previous priority.

Lean's instance search uses its instance transparency. The regression states
the supplied class on the frontend's exact `DensePoly.ofCoeffs` literal;
`ofList` alone did not match that target in the experiment. If all certificate
producers refuse, the diagnostic prints the exact class target and literal
spelling. This uses the existing proof-class interface and number-field
representation.

The [construction module](../conformance/HexRCF/SuppliedIrreducible.lean) proves
irreducibility of `[-2,-24,169,70,-127,-70,6,8,1]` with the owner's existing
`irreducibility!` tactic and its private executable closure. Its public
polynomial, ordinary theorems and scoped instance are exposed. The
[fresh consumer](../conformance/HexRCF/SuppliedIrreducibleProofs.lean) imports it
alongside the legacy certification proofs and verifies that the instance is
inactive before `open scoped Hex.RCF.SuppliedIrreducible`. It proves
`∀ x, x² + α + √2 > 0` for the existing selected quartic α with ordinary imports.
Both the emitted proof and direct certification retain the supplied instance.
All four full inventories contain exactly `propext`, `Classical.choice` and
`Quot.sound`.

The consumer's kernel irreducibility check references the already proved theorem
rather than reducing the factorizer. Native common-field construction during
search still runs its normal algorithm. The historical
[failed factorizer-import experiment](hexrcf-common-kernel.md) attempted to run
factorization in an ordinary-import client and remains separate evidence.

Controls accept the exact runtime/expression pair and reject mismatches on both
routes with the binding diagnostic. A synthetic admitted local class is rejected
with the forbidden-axiom diagnostic even for a quartic whose certificate producer
succeeds. No fallback hides that failure. State restoration permits normal
certification afterward. These synthetic terms are never retained as theorem
proofs. Legacy no-instance refusal, original-divisor, authentication and rollback
controls pass. Diagnostic strings are asserted by tests, never used to classify
production failures or select a different solver.

The consumer passes with the default heartbeat budget and its explicit recursion
limit of 32,768. Construction retains its 8,000,000-heartbeat budget. The accepted
construction and consumer builds report 11 seconds and 7.9 seconds respectively;
the earlier consumer observation was 7.7 seconds. These are separate unpaired
operational observations, not a speedup, complexity, memory or default-budget
claim for the construction module.

The optional adapter, fresh consumer, legacy preparation controls and manual
integration pass 14,159 Lake jobs; full rendering passes 14,151. DAG, trust,
copyright, line counts, manual split, affected links and diff checks pass.
The admission scan covers 407 cones / 1,260 modules, excluding intentional RCF
negative probes checked by their actual kernel regressions. The earlier
424-cone record retains its original tree. Both proof modules extend the existing
`HexConformance` target; no library, workflow, job, formula syntax or base-umbrella
dependency is added.

Six current desktop/narrow captures inspect the contract, scoped opt-in and
limits. [Desktop](data/hexrcf-supplied-irreducible/supplied-irred-review-desktop-supplied-contract.png)
and [narrow](data/hexrcf-supplied-irreducible/supplied-irred-review-narrow-supplied-contract.png)
paragraph widths fit their viewport. This is not a whole-page overflow claim.
All six captures and four historical captures are committed for inspection.
[Records](data/hexrcf-supplied-irreducible/context.json) bind sources, decoded
logs, observed exit statuses, failed exploratory builds and captures to their
exact revisions. Earlier records are not relabeled as final-source evidence.

This supplies one previously proved common polynomial through an ordinary-import
frontend. Automatic irreducibility certification, complete algebraic source
acceptance, generic frozen context/root/all-live assembly and recursive whole-joint
finite realization remain incomplete. #10358 stays open.
