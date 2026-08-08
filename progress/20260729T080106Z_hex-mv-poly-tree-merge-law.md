# Hex multivariate polynomial tree-merge integration

## Accomplished

- Proved the per-key lookup semantics of the generic
  `Std.ExtTreeMap.mergeWith?` operation.
- Factored the proof through reusable distinct-source `foldl`/`alter` lemmas,
  keeping the public specification independent of polynomial details.
- Refactored `MvPoly.add` to use the size-biased, deletion-capable tree-map
  merge directly.
- Reproved `coeff_add` from the generic lookup theorem, substantially
  simplifying the former list-fold proof.
- Rebuilt the kernel tests and reran the DAG and published trust-surface
  checks successfully.

## Current frontier

- Addition now has the intended tree-level implementation and retains the
  canonical no-explicit-zero invariant without a cleanup traversal.
- The core API PR has passed all build stages and is running its final
  conformance/oracle gate.
- Eleven pre-existing proof obligations remain in the core implementation.

## Next step

- Land the follow-up tree-map/addition commit after the core PR auto-merges and
  obtain the required independent review before merging its PR.
- Continue with `coeff_mul` and the monomial split uniqueness infrastructure.

## Blockers

- None.
