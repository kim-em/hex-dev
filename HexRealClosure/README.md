# Rational selected-root expressions

`Root.validate` checks a `Hex.SignDet.RawDescriptor Rat Nat` against its exact
context version. An `Expression d` stores a rational polynomial evaluated at the
real root selected by `d`. Its arithmetic is polynomial arithmetic; distinct
expressions can have the same value. `Expression.sign?` uses checked joint sign
determination. `Expression.inverse?` computes a gcd/cofactor split and a scaled
Bézout candidate, then checks its product at the selected root. A successful
inverse has a proof of its real value in `HexRealClosureMathlib.Basic`.

```lean
let d ← Root.validate 7 raw
let a : Expression d := ⟨DensePoly.ofCoeffs #[0, 1]⟩
let sign ← a.sign?.toOption
let inverse ← a.inverse?.toOption
```

Both sign and inverse expose producer errors. `inverse?` returns `none` for a
checked zero and also when its product check does not accept the candidate.
`Expression.transport` accepts checked `SignDet.Reencoding` evidence; its real
value is preserved. `Root.validate_context` rejects raw evidence from another
context version. These interfaces do not yet supply canonical-zero storage or
total field operations.

Run `lake build HexRealClosure.Tests HexRealClosureMathlib` and
`python3 HexRealClosure/verify.py` from the repository root. The test uses
`(X²−2)(X−3)` with the root in `(1,2)`, plus a non-monic definition and a
checked factor split. The Python oracle computes exact arithmetic in ℚ(√2)
independently of Lean.

For existing canonical number-field arithmetic and conversions, see the
[number-field chapter](../HexManual/Chapters/HexNumberField.lean) and
[real-algebraic chapter](../HexManual/Chapters/HexRealAlgebraic.lean).
