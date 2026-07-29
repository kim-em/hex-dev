# HexMvPoly order and algebra laws

## Accomplished

- Proved the `lex`, `grlex`, and `grevlex` monomial-order instances, including
  well-foundedness and compatibility with monomial multiplication.
- Completed the remaining monomial lattice, multiplication, distributivity,
  power, and partial-evaluation laws without adding `sorry`, `axiom`, or
  `native_decide`.
- Added a reusable Hex-local list API in `HexBasic/List.lean`, keeping
  `ListShim` limited to its Batteries compatibility role.
- Added kernel canaries that distinguish grlex from grevlex in three
  variables, exercise partial-evaluation collisions and cancellation, and
  guard the new proof dependencies with `#print axioms`.
- Reconciled the HexMvPoly SPEC with the proved API, including the monomial
  order law and the strong polynomial power recurrence.
- Incorporated an independent Claude Opus review, including its coverage,
  naming, theorem-orientation, API-placement, and semiring-law findings.
- Passed formatting checks, repository lints, and the full `lake build`
  (9634 jobs).

## Current frontier

The computational core's specified proof surface is implemented and the
HexMvPoly files contain no unfinished proofs. PR #9090, which this work was
stacked on, has merged.

## Next step

Rebase this law slice onto `main`, publish it as the only open HexMvPoly PR,
then implement the SymPy-backed conformance target and fixtures while its CI
runs.

## Blockers

None.
