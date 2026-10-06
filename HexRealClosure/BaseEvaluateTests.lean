/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseEvaluate
public meta import HexRealClosure.BaseEvaluate

public section

namespace Hex.RealClosure.BaseContext.FieldEmbedding.Tests

private abbrev Two := RationalFn (RationalFn Rat)

private def require (accepted : Bool) (message : String) : IO Unit :=
  unless accepted do throw (IO.userError message)

/-- Exercise native substitution on canonical fractions in two variables and
lift the exchange below a third variable. -/
def check : IO Unit := do
  let x : Two := RationalFn.C RationalFn.X
  let y : Two := RationalFn.X
  let three : Two := RationalFn.C (RationalFn.C 3)
  let exchange := swap Rat
  let expression := (x * y + three) / (x - y)
  require (exchange.value expression == (y * x + three) / (y - x))
    "adjacent exchange changed rational-function arithmetic"
  require (exchange.value (exchange.value expression) == expression)
    "two exchanges did not recover the canonical fraction"
  require (exchange.value (x / y) == y / x)
    "adjacent exchange moved a denominator into the wrong variable"
  require (exchange.value (0⁻¹ : Two) == 0)
    "adjacent exchange changed totalized zero inversion"
  require (exchange.value (x - x) == 0)
    "adjacent exchange lost canonical cancellation"
  let extended := exchange.rationalFunctions
  let oldX := RationalFn.C x
  let oldY := RationalFn.C y
  let newest : RationalFn Two := RationalFn.X
  require (extended.value ((newest + oldX) / (newest - oldY)) ==
      (newest + oldY) / (newest - oldX))
    "lifting the exchange moved the third variable"

end Hex.RealClosure.BaseContext.FieldEmbedding.Tests

#eval Hex.RealClosure.BaseContext.FieldEmbedding.Tests.check
