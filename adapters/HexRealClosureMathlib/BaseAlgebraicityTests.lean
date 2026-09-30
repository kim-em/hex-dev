/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseBound

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

/-- The local algebraic bound transfers an infinitesimal over the old base
to every positive element of its algebraic real closure. -/
noncomputable example (old : Ambient (Hex.RationalFn Rat))
    [DecidableEq old.Carrier] (next : Ambient (Hex.RationalFn old.Carrier))
    (x : old.Carrier) (hx : 0 < x) :
    next.inclusion (Hex.RationalFn.X : Hex.RationalFn old.Carrier) <
      Ambient.coefficientHom next x := by
  letI : Algebra (Hex.RationalFn Rat) old.Carrier := old.inclusion.toAlgebra
  have halg : ∀ y : old.Carrier, IsAlgebraic (Hex.RationalFn Rat) y :=
    fun y => old.algebraic y
  apply infinitesimal_lt_algebraic old.inclusion old.monotone halg
    (Ambient.coefficientHom next) (Ambient.coefficientHom_strictMono next)
    (next.inclusion Hex.RationalFn.X) ?_ x hx
  intro b hb
  have hpositive : 0 < old.inclusion b := by
    simpa only [old.inclusion.map_zero] using old.monotone hb
  exact Ambient.X_lt_coefficient next _ hpositive

end Hex.RealClosure
