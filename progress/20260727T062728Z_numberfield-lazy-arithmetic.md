# HexNumberField lazy arithmetic

## Accomplished

- Added bivariate addition and multiplication eliminants over `ZPoly`, plus
  reciprocal, `X`-factor removal, and reflected-root transformations.
- Added reusable square-free eliminant normalization and certified root
  selection at the eliminant separation depth.
- Implemented checked and total lazy addition, subtraction, multiplication,
  inversion, and division, including the specified zero cases.
- Added a sound-by-construction reciprocal complex-ball routine and explicit
  guard-bit budgets for addition, multiplication, and inversion.
- Exposed canonical `AlgebraicNumber` arithmetic through lazy operations
  followed by exactification.
- Added compiled checks for eliminant values and all five operations on
  `sqrt 2`, including selected zero/positive embeddings and normalized output
  polynomials.
- Rebuilt `HexNumberField.Lazy` and the umbrella `HexNumberField` target.

## Current frontier

The executable lazy arithmetic surface from the SPEC is complete. Six
propositional reflection lemmas remain as explicit Phase 1 proof obligations;
there are no data-level sorries in the new module.

## Next step

Publish this as a stacked milestone, start its independent review monitor, and
begin the candidate-disambiguation and polynomial-root layer while reviews run.

## Blockers

None.
