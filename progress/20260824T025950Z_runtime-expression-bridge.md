# Runtime expression bridge

## Accomplished

- Added a sealed `RuntimeEmit.Emitted` result and
  `Checked.emitResultWithin`, which return the exact quoted `Proof.Input`
  expression with its correlated Evidence expression from one saved-state
  transaction. Both expressions receive independent size and exact-type checks;
  `Checked.emitWithin` remains the evidence-only compatibility projection.
- Added transparent frontend helpers for projecting a successful checked
  `Model` and converting finite source-list membership proofs into
  `SourcesContain`.
- Extended focused frontend and runtime-emitter conformance with private
  constructor, exact input/evidence correlation, changed-input refusal,
  model/source projection, rollback, exact resource one-under, and guarded
  ordinary-axiom checks.
- Updated the current library contract and verified the focused conformance
  targets, dependency DAG and unit test, published trust surface, copyright
  headers, line limits, and clean diff formatting.

## Current frontier

The expression-level bridge needed by a typed-runtime public tactic is now
available. The public tactic itself is deliberately unchanged in this branch.

## Next step

Route `HexIntervalMathlib.Tactic` through the checked frontend model, typed
runtime rule/controller and target-terminal lineage, then install only the
pair returned by `RuntimeEmit.Checked.emitResultWithin`, correlating its input
and evidence with the current facts and goal before assignment.

## Blockers

None in the expression bridge. Its input remains the exact runtime-admitted
`Proof.Input`, so the tactic integration must quote the same source valuation
and use the new frontend membership conversion; it cannot substitute a
separately reconstructed input or Evidence claim.
