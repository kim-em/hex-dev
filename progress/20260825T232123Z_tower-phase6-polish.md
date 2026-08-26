# Tower pair Phase-6 polish (docstrings, #9419 deletions, SPEC notes)

## Accomplished

- Deleted the dead declarations from #9419 after re-verifying zero
  consumers on this base: `elemMajorant`, `Factor.yun?` (plus its
  `#guard`; the SPEC's factor surface names only `factor?`,
  `checkFactorization`, `Factorization`, so `yun?` was not public API),
  `evalBlocks_set`, `relation_eval_top`, `oneLevel_size`,
  `list_prod_pow`, `factorRaw_sorted`, `trans_preserves`.
- SPEC notes: added `SMul Rat (Elem T)` to the tower SPEC instance list
  with the qsmul-pinning sentence; recorded in the companion SPEC that
  `Factorization.Sound` derives no-associates from monicity plus strict
  `factorsSorted`.
- Docstrings: FactorGeneric/Trager.lean (52), Yun.lean (30 + module
  docstring), ArithmeticCore/Basic.lean (26), ArithmeticCore/Field.lean
  (3), FactorGeneric/Product.lean (15 + module docstring),
  NormCore/Basic.lean (13), Norm.lean (6, incl. the five toPolynomial
  simp lemmas), public stragglers (`polynomialIrreducible_iff`,
  `dim_pos`, `factorSquarefree_isSome`, `isIrreducible_nil_iff`),
  Complete.lean module docstring, and the Tower's flagged gaps
  (`foldl_array_size`, `convolveRow_size`, `reduceCoeffs_size`,
  `def raw`, section headers for the RawElem/Coeff instance groups).
  Removed the empty `namespace Norm` stub in companion Norm.lean and
  the two unused simp arguments in companion Basic.lean.
- Judged exempt: the three rfl unfolding lemmas (`conjugateMap_apply`,
  `conjugateHom_apply`, `embedding_apply`), one-line instances
  delegating to documented operation defs, and the private compiled
  `#guard` regression fixtures.
- Verified: `lake build HexNumberFieldTower HexNumberFieldTowerMathlib
  HexConformance` green, `scripts/check_dag.py` clean,
  `git diff --check` clean.

## Current frontier

Branch `wave/tower-mathlib-phase6` (not pushed) carries eleven commits:
the #9419 deletions, the SPEC notes, seven docstring commits by area,
and the simp-argument cleanup.

## Next step

Open the PR for this branch (deletions commit body closes #9419), then
the remaining Phase-6 exit-bar items for the pair: performance
regression check against the last benchmark baseline, and the
`done_through` bump to 6 once the whole exit bar is met.

## Blockers

None. Pre-existing repo-wide warnings (deprecated `if_pos`/`if_neg`,
`letI`-style linter hints) were left alone as out of scope; the
un-swept companion files (Flatten, Split, Complete, Basic, Adjoin,
Factor) still have undocumented *private* helpers that the Phase-2
review did not flag.
