# Hex multivariate polynomial core proof pass

## Accomplished

- Replaced polynomial equality with the SPEC-prescribed ordered-term-list
  decision path and verified that all `Int` and `Rat` downstream kernel probes
  still reduce.
- Discharged every proof obligation in `Basic.lean`: extensionality,
  coefficient-map invariant preservation, constructor coefficient laws,
  normalized monomial addition, and `ofTerms`.
- Proved that coefficient negation preserves nonzeroness.
- Aligned `rename` and `reorder` with the reviewed SPEC by making their target
  comparators explicit arguments.

## Current frontier

The core implementation has 31 remaining explicit `sorry` placeholders, down
from 37. They are concentrated in monomial-order/arithmetic laws, polynomial
operation laws, query/evaluation/structural characterisations, and recursive
round trips.

Documentation follow-up PR #9075 carries the verified independent-review fixes
that raced with #9073's merge.

## Next step

Rebase the core commits onto current `main`, push the API milestone branch, run
the independent implementation review, and open its PR. Continue discharging
operation and monomial laws while that PR runs CI.

## Blockers

None.
