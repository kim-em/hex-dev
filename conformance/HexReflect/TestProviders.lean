/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexReflect

/-!
Test provider registrations for the `HexReflect` conformance modules. Each
recognizes one small carrier, so every other carrier keeps the integer
coefficient provider:

* `Fin 11`: evidence whose laws do not prove `CoeffLaws`;
* `Fin 13`: two providers of equal priority, an ambiguity;
* `Fin 19`: evidence whose `LawfulBEq` field is not an instance;
* `Fin 23`: a recognized request the provider declines;
* `Rat`: rational coefficients interpreted by the identity, the only
  non-integer coefficient representation exercised by the tests.
-/

namespace Hex.ReflectConformance

open Lean Meta Hex.Reflect

private def finExpr (n : Nat) : Lean.Expr := mkApp (mkConst ``Fin) (mkNatLit n)

private def onCarrier (ring : CarrierRequest) (carrier : Lean.Expr)
    (k : Lean.Meta.Sym.SymM (ProviderOutcome Evidence)) :
    Lean.Meta.Sym.SymM (ProviderOutcome Evidence) := do
  if ring.type == carrier then k else return .notApplicable

/-- A provider whose evidence does not prove the coefficient laws. -/
def bogusCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.bogusCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := onCarrier ring (finExpr 11) do
    let p ← intCoeffProvider ring
    return .success (.coefficients { p with
      id := { name := `Hex.ReflectConformance.bogusCoefficients }
      laws := mkConst ``True.intro }) Budget.zero

/-- A second provider of the same priority for `Fin 13`. -/
def rivalCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.rivalCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := onCarrier ring (finExpr 13) do
    let p ← intCoeffProvider ring
    return .success (.coefficients { p with
      id := { name := `Hex.ReflectConformance.rivalCoefficients } }) Budget.zero

/-- A third provider of the same priority for `Fin 13`. -/
def otherCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.otherCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := onCarrier ring (finExpr 13) do
    let p ← intCoeffProvider ring
    return .success (.coefficients { p with
      id := { name := `Hex.ReflectConformance.otherCoefficients } }) Budget.zero

/-- A provider whose `LawfulBEq` evidence is not an instance, although its
laws are correct. -/
def malformedInstanceCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.malformedInstanceCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := onCarrier ring (finExpr 19) do
    let p ← intCoeffProvider ring
    return .success (.coefficients { p with
      id := { name := `Hex.ReflectConformance.malformedInstanceCoefficients }
      lawfulBEqInst := mkConst ``True.intro }) Budget.zero

/-- A provider that recognizes `Fin 23` and declines it. -/
def decliningCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.decliningCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := onCarrier ring (finExpr 23) do
    return .declined (.unsupportedSourceType ring.type) Budget.zero

/-- Rational coefficients, mapped from the reflected integers by the cast and
interpreted in `Rat` by the identity. -/
theorem ratCoeffLaws : CoeffLaws (C := Rat) (α := Rat) Int.cast id where
  interp_ofInt _ := rfl
  interp_zero := rfl
  interp_add _ _ := rfl

/-- The rational coefficient provider for the carrier `Rat`. -/
def ratCoefficients : Registration where
  id := { name := `Hex.ReflectConformance.ratCoefficients }
  capability := .commRingNormalize
  priority := 10
  recognize ring := onCarrier ring (mkConst ``Rat) do
    let ratType := mkConst ``Rat
    let zeroInst ← Lean.Meta.Sym.synthInstance (mkApp (mkConst ``Zero [.zero]) ratType)
    let addInst ← Lean.Meta.Sym.synthInstance (mkApp (mkConst ``Add [.zero]) ratType)
    let beqInst ← Lean.Meta.Sym.synthInstance (mkApp (mkConst ``BEq [.zero]) ratType)
    let lawfulBEqInst ← Lean.Meta.Sym.synthInstance
      (mkApp2 (mkConst ``LawfulBEq [.zero]) ratType beqInst)
    let intCastInst ← Lean.Meta.Sym.synthInstance (mkApp (mkConst ``IntCast [.zero]) ratType)
    return .success (.coefficients {
      id := { name := `Hex.ReflectConformance.ratCoefficients }
      coeffType := ratType
      zeroInst, addInst, beqInst, lawfulBEqInst
      ofInt := mkApp2 (mkConst ``Int.cast [.zero]) ratType intCastInst
      interp := mkApp (mkConst ``id [.succ .zero]) ratType
      laws := mkConst ``ratCoeffLaws }) Budget.zero

attribute [hex_reflect_provider] bogusCoefficients rivalCoefficients otherCoefficients
  malformedInstanceCoefficients decliningCoefficients ratCoefficients

end Hex.ReflectConformance
