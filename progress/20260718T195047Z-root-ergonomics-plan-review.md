# Concrete real-root ergonomics plan review

## Accomplished

- Reviewed the five-item ergonomics plan against the current Sturm-chain,
  squarefree correspondence, isolation semantics, driver, dyadic conversion,
  and dense-polynomial bridge implementations.
- Traced the concrete `x^4 - 2` scratch proof to identify which proposed APIs
  actually remove its scaffolding.
- Identified a simpler Item 1 proof: propagate coprimality backward from the
  terminal constant using the existing three-term `chain_step` relation,
  avoiding a full terminal-gcd association theorem.
- Confirmed that `primitivePart`, positive pseudo-remainder scaling, and the
  explicit negation only introduce units/nonzero constants over `R[X]` and do
  not obstruct the backward argument.
- Found that Item 4's stated theorem is honest but largely redundant, omits the
  promised per-interval soundness conjunct, and does not help prove concrete
  interval bounds for the opaque existential output.
- Determined that a Horner/fold evaluation normal form is substantially more
  useful for concrete coefficient literals than a public finite-sum normal
  form.

## Current frontier

- Review is complete; no library source files were changed.
- The plan should be revised before implementation, chiefly for Item 1's proof
  strategy, Item 4's scope, and committed end-to-end conformance coverage.

## Next step

- Rewrite Item 1 around a backward `IsCoprime` induction and decide whether the
  Boolean API is a one-way certificate or a fully characterized replacement
  for `SquareFreeRat` on all degree cases.
- Replace or demote Item 4, and add a committed concise `x^4 - 2` conformance
  example that exercises Items 1--3 and the namespace alias.

## Blockers

- None.
