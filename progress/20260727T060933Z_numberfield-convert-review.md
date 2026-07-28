# HexNumberField conversion review follow-up

## Accomplished

- Confirmed the independent conversion review reproduced the cross-factor
  precision issue already fixed on the refreshed branch.
- Inlined the factor-selection worker into public `AlgebraicRoot.exact?`, so
  callers cannot invoke it with a polynomial unrelated to the enclosing
  factorization.
- Documented the uniqueness argument supplied by enclosing-polynomial Mahler
  precision.
- Added a near-collision regression for `(X² - 2)(70X - 99)`, whose rational
  root lies inside the linear factor's old coarse disc around `sqrt 2`.
- Rebuilt `HexNumberField.Convert` successfully.

## Current frontier

The conversion review's blocking and API-soundness findings are addressed.
The remaining certificate sorries in `Basic` are Phase 1 propositional
obligations; earlier attempts confirmed that the compiled guards do not yet
reduce through the deeper gcd/isolation kernel paths under `by decide`.

## Next step

Push this conversion follow-up and begin the fixed-field multiplication
operator/minimal-polynomial implementation on a new stacked branch.

## Blockers

None.
