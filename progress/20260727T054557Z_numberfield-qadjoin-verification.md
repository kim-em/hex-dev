# HexNumberField fixed-field verification follow-up

## Accomplished

- Exposed `ZPoly.toRatPoly`, closing the first cross-module reduction boundary
  used by the public fixed-field reduction path.
- Removed the bespoke `QAdjoin` Boolean equality and now derive the lawful
  `BEq`/`LawfulBEq` pair from canonical-coordinate `DecidableEq`.
- Added the public `eq_iff_coeffs` characterization needed by companion field
  proofs.
- Made fixed-field zero and one direct canonical records instead of rebuilding
  and reducing the rational modulus on every use.
- Reused `ZPoly.X` in canonical algebraic-number zero recognition.
- Confirmed the inferred `LawfulBEq` instance and rebuilt
  `HexNumberField.QAdjoin`.

## Current frontier

The fixed-field review's correctness/API findings are addressed. Exposing
`toRatPoly` alone does not make the entire rational polynomial remainder or
squarefree decision kernel-reducible; their deeper implementation boundaries
remain separate proof-engineering work rather than executable defects.

## Next step

Push the follow-up and propagate it through the approximation and conversion
branches before continuing fixed-field minimal-polynomial work.

## Blockers

None.
