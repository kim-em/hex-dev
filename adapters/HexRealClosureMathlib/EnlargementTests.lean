/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseBound
public import HexRealClosureMathlib.Union

public section

namespace Hex.RealClosure

open scoped Hex.OrderedFn.Infinitesimal
attribute [local instance 2000] Field.toGrindField

/-- The real closure of an old algebraic ambient remains algebraic over the
mapped rational infinitesimal field after enlargement. -/
noncomputable example (old : Ambient Rat) [DecidableEq old.Carrier] :
    letI : Algebra Rat old.Carrier := old.inclusion.toAlgebra
    let next := Ambient.infinitesimal old.Carrier
    letI : Algebra (Hex.RationalFn Rat) next.Carrier :=
      (Ambient.mappedHom (algebraMap Rat old.Carrier) next).toAlgebra
    Algebra.IsAlgebraic (Hex.RationalFn Rat) next.Carrier := by
  letI : Algebra Rat old.Carrier := old.inclusion.toAlgebra
  letI : Algebra.IsAlgebraic Rat old.Carrier := ⟨fun x => old.algebraic x⟩
  exact Ambient.mapped_algebraic Rat old.Carrier (Ambient.infinitesimal old.Carrier)

/-- The same enlargement uses the native rational-function dictionaries of a
validated infinitesimal coefficient base. -/
noncomputable example (old : Ambient (Hex.RationalFn Rat))
    [DecidableEq old.Carrier] :
    letI : Field (Hex.RationalFn Rat) := HexPolyMathlib.fieldOfGrind
    let next := Ambient.infinitesimal old.Carrier
    letI : Field (Hex.RationalFn (Hex.RationalFn Rat)) :=
      HexPolyMathlib.fieldOfGrind
    letI : Algebra (Hex.RationalFn (Hex.RationalFn Rat)) next.Carrier :=
      (Ambient.mappedNativeHom HexPolyMathlib.toGrind_fieldOfGrind
        old.inclusion next).toAlgebra
    Algebra.IsAlgebraic (Hex.RationalFn (Hex.RationalFn Rat)) next.Carrier := by
  letI : Field (Hex.RationalFn Rat) := HexPolyMathlib.fieldOfGrind
  letI : Algebra (Hex.RationalFn Rat) old.Carrier := old.inclusion.toAlgebra
  letI : Algebra.IsAlgebraic (Hex.RationalFn Rat) old.Carrier :=
    ⟨fun x => old.algebraic x⟩
  exact Ambient.mappedNative_algebraic HexPolyMathlib.toGrind_fieldOfGrind
    old.inclusion inferInstance (Ambient.infinitesimal old.Carrier)

/-- The parameter is known infinitesimal only over the rational base. The
local algebraic bound extends this inequality to every positive element of
the relative algebraic closure of that base inside the same ambient field. -/
noncomputable example {B : Type} [Field B] [LinearOrder B]
    [IsStrictOrderedRing B] [DecidableEq B]
    (mid : Ambient (Hex.RationalFn B)) :
    letI : Algebra B mid.Carrier := (Ambient.coefficientHom mid).toAlgebra
    ∀ x : Union.Carrier B mid.Carrier, 0 < x →
      mid.inclusion (Hex.RationalFn.X : Hex.RationalFn B) <
        Union.inclusion (B := B) (R := mid.Carrier) x := by
  letI : Algebra B mid.Carrier := (Ambient.coefficientHom mid).toAlgebra
  intro x hx
  let f : B →+* Union.Carrier B mid.Carrier := algebraMap B _
  let e : Union.Carrier B mid.Carrier →+* mid.Carrier :=
    (Union.inclusion (B := B) (R := mid.Carrier)).toRingHom
  have hδ (b : B) (hb : 0 < f b) :
      mid.inclusion Hex.RationalFn.X < e (f b) := by
    have hb' : 0 < b :=
      (Union.base_lt (Ambient.coefficientHom_strictMono mid) 0 b).mp (by simpa using hb)
    exact Ambient.X_lt_coefficient mid b hb'
  have he : StrictMono e := fun a b h => (Union.inclusion_lt a b).mpr h
  exact infinitesimal_lt_algebraic f Union.algebraic e he
    (mid.inclusion Hex.RationalFn.X) hδ x hx

end Hex.RealClosure
