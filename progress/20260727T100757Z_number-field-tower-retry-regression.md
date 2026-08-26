# Tower recovery retry regression

## Accomplished

- Added the focused review's concrete cyclotomic regression with
  `theta = zeta + zeta^6` and `alpha = zeta^4 - zeta^5 - zeta^6` for a
  seventh root of unity.
- Certified exact isolations for both algebraic inputs and checked that shift
  `+1` produces a full-degree candidate whose recovery gcd is nonlinear,
  while the same two-step search continues and accepts shift `-1`.
- Updated the conformance pin and PARI oracle to the sharpened
  `choose(d, 2) + 1` nonzero-shift enumeration.
- Built the tower conformance module and emitter, reproduced the committed
  fixture byte for byte, passed all nine PARI cases, compiled the oracle, and
  passed `git diff --check`.

## Current frontier

The retry branch now has a direct executable regression. The degree-six exact
isolation adds roughly one minute to a cold conformance elaboration; its larger
recursion and exponentiation thresholds are scoped to that single fixture.

## Next step

Publish the rebased conformance branch and return to the
`HexNumberFieldMathlib` companion scaffold.

## Blockers

None.
