/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexReflect

/-!
Test provider registrations for the `HexReflect` conformance module. They
recognize only `Fin 11` and `Fin 13`, so every other carrier keeps the
integer coefficient provider.
-/

namespace Hex.ReflectConformance

open Lean Meta Hex.Reflect

private def finExpr (n : Nat) : Lean.Expr := mkApp (mkConst ``Fin) (mkNatLit n)

/-- A provider whose evidence does not prove the coefficient laws. It applies
only to `Fin 11`. -/
def bogusCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.bogusCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := do
    unless ring.type == finExpr 11 do return none
    let p ← intCoeffProvider ring
    return some (.coefficients { p with
      id := { name := `Hex.ReflectConformance.bogusCoefficients }
      laws := mkConst ``True.intro })

/-- A second provider of the same priority for `Fin 13`. -/
def rivalCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.rivalCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := do
    unless ring.type == finExpr 13 do return none
    let p ← intCoeffProvider ring
    return some (.coefficients { p with
      id := { name := `Hex.ReflectConformance.rivalCoefficients } })

/-- A third provider of the same priority for `Fin 13`. -/
def otherCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.otherCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := do
    unless ring.type == finExpr 13 do return none
    let p ← intCoeffProvider ring
    return some (.coefficients { p with
      id := { name := `Hex.ReflectConformance.otherCoefficients } })

attribute [hex_reflect_provider] bogusCoefficients rivalCoefficients otherCoefficients

end Hex.ReflectConformance
