/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerTransport
public import HexRealClosureMathlib.TowerUnion

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A finite validated tower over its canonical base restricts to the
relative algebraic subfield of any supplied real closed model. -/
@[expose] noncomputable def baseRestrict {B : Type} [Lean.Grind.Field B]
    [DecidableEq B] {sign : B → Int}
    [DecidableEq K] [IsRealClosed K]
    (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (suffix : Suffix (Context.base base)) :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := f.toAlgebra
    Model suffix.context (Union.Carrier B K) := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := f.toAlgebra
  exact ((Model.base base f hsign).extend suffix).restrictUnion
    (extend_base_algebraic base f hsign suffix)

/-- Restriction preserves each value of the complete validated suffix after
inclusion into the original ambient field. -/
@[simp] theorem baseRestrict_value {B : Type} [Lean.Grind.Field B]
    [DecidableEq B] {sign : B → Int}
    [DecidableEq K] [IsRealClosed K]
    (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (suffix : Suffix (Context.base base)) :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := f.toAlgebra
    ∀ a : suffix.context.Value,
      ((baseRestrict base f hsign suffix).value a : K) =
        ((Model.base base f hsign).extend suffix).value a := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := f.toAlgebra
  intro a
  rfl

/-- The restricted tower model uses the prescribed base algebra map after
every validated root in the original suffix. -/
theorem baseRestrict_embed {B : Type} [Lean.Grind.Field B]
    [DecidableEq B] {sign : B → Int}
    [DecidableEq K] [IsRealClosed K]
    (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (suffix : Suffix (Context.base base)) :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := f.toAlgebra
    ∀ a : (Context.base base).Value,
      (baseRestrict base f hsign suffix).value (suffix.embed a) =
        algebraMap B (Union.Carrier B K) a.stored := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := f.toAlgebra
  intro a
  apply Subtype.ext
  change ((Model.base base f hsign).extend suffix).value (suffix.embed a) = f a.stored
  exact extend_base_embed base f hsign suffix a

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.baseRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.baseRestrict

/-- info: 'Hex.RealClosure.Tower.Model.baseRestrict_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.baseRestrict_embed

/-- info: 'Hex.RealClosure.Tower.Model.baseRestrict_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.baseRestrict_value
