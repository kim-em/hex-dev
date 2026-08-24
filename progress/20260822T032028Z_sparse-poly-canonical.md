# hex-sparse-poly: canonical construction (milestone 1 complete)

## Accomplished

- `addTerm`: ordered-`List` insert specification, the invariant
  preservation proof (`addTermList_canonical`), the coefficient
  description (`coeff_addTerm` via `addCoeff`), and the in-place
  `addTermImpl` (binary-search `lowerBound` plus one erase/set/insert/
  push splice) behind a proved `@[csimp]` equality
  (`addTermList_splice` + `lowerBound_spec`).
- `ofTerms` as the fold-of-`addTerm` specification, its no-algebra
  coefficient description (`coeff_ofTerms_addCoeff`), the SPEC's
  `coeff_ofTerms` under `hzero`, and the stable sort-and-combine
  `ofTermsImpl` (`List.mergeSort` + `combineRun`) behind a proved
  `@[csimp]` equality, with the stability argument
  (`filter_exp_mergeSort` from core's `sublist_mergeSort`).
- `monomial`, `C`, `X`, `One`, the `#sp[…]` literal, and their
  coefficient lemmas.
- `HexSparsePoly/KernelTests.lean` (in the `HexReleaseTests` globs):
  `decide +kernel` probes for the whole SPEC kernel-exposure closure
  from a downstream module.

All proofs complete; zero `sorry` in the library.

## Current frontier

Milestone 1 of `HexSparsePoly/SPEC/hex-sparse-poly.md` is done.

## Next step

Milestone 2 (`HexSparsePoly/Arith.lean`): `add` as a linear merge,
`neg`/`sub`/`scale`/`mulMonomial`, `mul` as the pairwise-product
specification (its `@[csimp]` twin waits for the Phase-4
sparse-multiplication bench), `pow`, the operator instances, and the
ring laws.

## Blockers

None.
