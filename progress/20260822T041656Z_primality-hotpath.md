# hex-primality: hotPathCandidates migrated onto the committed table

## Accomplished

- `HexBerlekampZassenhaus/PrimeSelection.lean`: the 94 hand-written
  `smallPrimeCandidateOfTrial ... (by decide) (by decide)` entries are
  replaced by `tableCandidates lo hi`, a proof-carrying window into
  `Hex.Nat.primeTable` (primality from `mem_primeTable_prime`, bounds
  from the window). `smallPrimeCandidates` is the window `[3, 72)`,
  `extendedSmallPrimeCandidates` is `[72, 501)`, and
  `hotPathCandidates` remains their append, so every consumer
  (`ChoosePrimeData`, `Modular/PrimePlan`, bench, conformance) is
  untouched.
- `hotPathPrimeValues_nodup` now follows from `primeTable_sorted`;
  `mem_hotPathCandidates_prime` from the window ranges plus the
  structure field; `exists_mem_hotPathCandidates_of_prime` from
  `mem_primeTable_of_prime`. The `Fin 501` decide and the
  `maxRecDepth` overrides on those proofs are gone; the three length
  `#guard`s (19/75/94) pin contents and order.
- `libraries.yml`: `HexBerlekampZassenhaus` deps gain `HexPrimality`.
- One downstream proof (`choosePrimeData?_factorsModP_berlekamp_form`)
  needed a `maxRecDepth` bump because incidental reductions now walk
  the 1229-entry table. Full tree build green; `check_dag.py` passes.

## Current frontier

This is the migration the SPEC calls the proof that the table is the
right shape: the 94-entry list is now a view, with no loss.

## Next step

Order.lean (milestone 2a): the multiplicative-order development.

## Blockers

Stacked on the table PR.
