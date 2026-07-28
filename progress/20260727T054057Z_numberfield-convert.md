# HexNumberField root exactification

## Accomplished

- Added canonical conversion from `AlgebraicNumber` to its fixed-field
  generator coordinates and to the factorization-lazy `AlgebraicRoot` view.
- Implemented checked lazy-root exactification by factoring the enclosing
  polynomial, rechecking primitive/sign/degree/irreducibility/squarefreeness
  certificates, isolating each candidate factor, and selecting the one whose
  root disc meets the input representative.
- Routed the selected factor through `AlgebraicNumber.ofNormalized?` so the
  returned canonical number uses the deterministic stored representative.
- Added the total `AlgebraicRoot.exact` wrapper with the specified loud
  fallback.
- Added compiled regressions for irreducible exactification, removal of an
  irrelevant factor from `(X² - 2)(X - 3)`, and canonical zero conversion.
- Added `Convert.lean` to the public umbrella and rebuilt `HexNumberField`.

## Current frontier

Lazy-root exactification is executable and tested. Fixed-field element
canonicalization still needs the multiplication-operator minimal-polynomial
path required by `QAdjoin.toAlgebraicNumber?`.

## Next step

Publish this focused milestone, obtain its asynchronous review, then implement
the fixed-field multiplication-matrix/minimal-polynomial stage.

## Blockers

None.
