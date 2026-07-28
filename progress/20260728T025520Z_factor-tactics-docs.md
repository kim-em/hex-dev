# Factor tactics and documentation cleanup

## Accomplished

- Documented `factor_poly` as both a term elaborator and a tactic, with a
  `Polynomial ℤ` tactic example.
- Made the executable and Mathlib tactic providers introduce the same
  `scalar`, `factors`, `factors_mul`, and `factors_irred` locals, and added
  regression coverage for both Mathlib coefficient domains.
- Removed the unnecessary manual `z` helper; the existing `ZMod64` `OfNat`
  instance now supplies the example's literals directly.
- Rewrote the `ZPoly.factorize` docstring in ordinary API language with Verso
  name roles, and added the rendered-name requirement to
  `SPEC/writing-style.md`.
- Replaced the polynomial-factorization `factorize_headline*` theorem family
  with `factorize_normalized`, including the positive-leading conclusion, and
  updated its README, SPEC, and manual references.
- Removed nearby `headline`, `contract`, issue-number, and `axiom cone` wording
  from polynomial-factorization declarations and documentation.
- Opened #9022 for the repository-wide docstring audit and #9023 for the
  repository-wide declaration-name audit.
- Confirmed that unconditional factorization correctness is proved through
  the trial backstop, while lattice success without fallback remains tracked
  by #8369 and #8370.
- Ran the factor tactic tests, focused factorization/manual builds, the full
  `lake build`, and `git diff --check` successfully.

## Current frontier

The requested local factor-tactics, factorization naming, and documentation
changes are complete and build successfully.

## Next step

Carry out the full-library audits in #9022 and #9023; pursue #8369 and #8370
for the separate conditional lattice-completeness theorem programme.

## Blockers

None.
