# HexPolyFpMathlib Phase 6 and Phase 7

## Accomplished

**Phase 6 (proof polishing), `done_through` 5 → 6.**

- Documented `fpPolyEquiv_apply` and `fpPolyEquiv_symm_apply`, the two public
  theorems the library exported without a docstring. Every other public
  declaration already had one.
- Implemented the three cleanups filed as
  https://github.com/kim-em/hex-dev/issues/9372, having first confirmed each
  against the source:
  - Dropped `coeff_toMathlibPolynomial_equiv`. Its left-hand side was
    syntactically identical to `coeff_toMathlibPolynomial`'s and its
    right-hand side was undone by `HexModArithMathlib.ZMod64.equiv_apply`,
    which is itself `@[simp]`; `simpNF` flagged it. Its only occurrence
    outside its own declaration was the re-export list in
    `HexBerlekampMathlib/Irreducibility.lean`, which loses one name.
  - `coeff_toMathlibPolynomial` now delegates to `coeff_fpPolyToPolynomial`
    instead of repeating its ten-line proof behind a `show`. Both public
    names stay: `coeff_fpPolyToPolynomial` has to exist before `fpPolyEquiv`
    does, because all four of the equivalence's fields use it.
  - Removed the no-op `open scoped HexPolyFpMathlib` from
    `HexGFqMathlib/Subfield.lean` and `HexGFqMathlib/Primitivity.lean`.
- Dropped the unused `universe u` and the `open Polynomial` the file never
  relied on; every reference in it is already fully qualified.
- Adjudicated the remaining zero-reference public declarations rather than
  deleting them. `fpPolyToPolynomial` and `coeff_fpPolyToPolynomial` are the
  pre-equivalence layer the `fpPolyEquiv` fields are proved from, and
  `fpPolyEquiv_symm_apply` is the backward half of a complete `@[simp]`
  apply/symm-apply pair.
- The performance-regression exit criterion does not apply: the library's SPEC
  declares it a `correspondence-only-layer` with no external comparator, and it
  ships no bench or conformance target. No `sorry`, no `axiom`, no
  `native_decide`. It exposes no irreducibility or field-construction claim of
  its own; those live in `hex-berlekamp-mathlib` and `hex-gfq-*`.
- Mathlib's `#lint` (14 default linters plus `docBlameThm`, run from a
  throwaway `HexPolyFpMathlib/LintTests.lean` that was deleted before
  committing) reported 4 errors in 21 declarations before and reports 0 in 20
  after.

**Phase 7 (user-facing documentation), `done_through` 6 → 7.**

- Authored the `# The Mathlib correspondence` section (tag
  `hex-poly-fp-mathlib`) in `HexManual/Chapters/HexPolyFp.lean`, which did not
  exist. `scripts/check_phase7.py` requires the companion's Phase 7 deliverable
  in its computational partner's chapter rather than in a chapter of its own.
  The section pulls fifteen docstrings out of the library: the equivalence and
  the `Bounds`-versus-primality boundary at the top, then subsections for the
  named forward map with its coefficient and monicity lemmas, the transport
  family, and the `CommRing` instance.
- Two live code blocks make the `commRing` design point concrete: `f * g` is
  `DensePoly.mul f g` by `rfl` under the instance, and `ring` closes a binomial
  identity over `FpPoly p` directly. Transporting a `CommRing` along
  `fpPolyEquiv` instead would give a correct instance whose multiplication is
  Mathlib's, and no executable convolution would run.
- Recorded the re-export: `HexBerlekampMathlib` still exports every name in the
  section, so old call sites spelling them `HexBerlekampMathlib.foo` resolve.
- Extended the chapter's cross-references with the executable/Mathlib boundary
  in the direction the other chapters state it.
- `HexPolyFpMathlib/README.md` already exists and conforms to
  `SPEC/readme.md`; its quickstart names only `fpPolyEquiv`, which is
  unaffected by the Phase 6 edits.

## Adjudication: the open feature issues do not block the bumps

A review of the branch argued that `done_through` 6 and 7 are premature while
https://github.com/kim-em/hex-dev/issues/9370 (the inverse transport family,
including the two-sided `dvd_iff`) and
https://github.com/kim-em/hex-dev/issues/9371 (degree and `leadingCoeff`
ownership) are open. Considered and declined; the bumps stand.

The family precedent is that documented absent surface does not block Phase 7.
`HexGF2Mathlib` is at 7 with no `Field` instance on `GF2n` and no
`EuclideanDomain` instance, both recorded in its SPEC and its chapter section;
`HexGFqMathlib` is at 7 with the primitivity glue absent. Phase 6's exit
criteria are about the quality of the surface that exists, not about its
extent: the linter is clean, docstring coverage meets the
`SPEC/design-principles.md` rule, and the dead declarations are adjudicated.
The Phase 2 scaffolding review that filed 9370 and 9371 classified both as
additive work rather than as blocking gaps, and the issues are the tracked
mechanism for them. The chapter's transport section now names 9370 at the
point where a reader would notice the forward-only `dvd`, so the gap is
documented where it bites rather than left to be rediscovered.

## Current frontier

`libraries.yml` records `HexPolyFpMathlib.done_through: 7`, so `status.py`
lists it under "Fully done". `check_dag.py`, `check_phase7.py`,
`check_phase4.py` and `release/check_manual_split.py` all pass. A full
`lake build` (9818 jobs, 6m8s) is green, and `lake build HexManual` is green
with the new section and emits no warnings from the chapter.

## Next step

`HexBerlekampMathlib` is the obvious follow-on: it is still at
`done_through: 3`, it is the library that re-exports this one's names, and its
`FactorTactics` chapter is already in the manual.

## Blockers

None.
