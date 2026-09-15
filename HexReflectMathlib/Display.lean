/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib
public import HexReflect
public import HexReflectMathlib.Residue
public meta import Lean
public meta import Mathlib.Tactic.NormNum

public section

namespace HexReflectMathlib

open Hex
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

universe u

variable {C : Type} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
  {k : Nat} {F : Type u} [CommRing F]

/-- Evaluate one displayed term directly in the source atoms. -/
theorem eval_cons (ι : C →+* F) (v : Fin k → F)
    (t : List Nat × C) (ts : MvPoly.Kernel.PolyList C) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (MvPoly.Kernel.denote (cmp := Mono.grevlex) (t :: ts)) =
      ι t.2 * (∏ i : Fin k, v i ^ t.1.getD i.val 0) +
        HexMvPolyMathlib.eval₂MathlibHom ι v (MvPoly.Kernel.denote (cmp := Mono.grevlex) ts) := by
  rw [MvPoly.Kernel.denote, map_add]
  congr 1
  change MvPolynomial.eval₂ ι v
    (HexMvPolyMathlib.equiv (cmp := Mono.grevlex)
      (MvPoly.monomial (MvPoly.Kernel.mono k t.1) t.2)) = _
  rw [HexMvPolyMathlib.equiv_apply, HexMvPolyMathlib.toMvPolynomial_monomial,
    MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
  simp only [HexMvPolyMathlib.monoEquiv_apply, MvPoly.Kernel.get_mono]

/-- Evaluation of the empty term list. -/
theorem eval_nil (ι : C →+* F) (v : Fin k → F) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (MvPoly.Kernel.denote (cmp := Mono.grevlex) []) = 0 := map_zero _

/-- A signed representative used only for displaying a residue coefficient. -/
@[expose] def signedResidue (p c : Nat) : Int :=
  if p < c + c then (c : Int) - p else c

/-- Signed display preserves the interpretation in characteristic `p`. -/
theorem residue_signed (p : Nat) [Hex.ZMod64.Bounds p] {F : Type*}
    [CommRing F] [CharP F p] (c : Nat) :
    residueHom p F (Hex.ZMod64.ofNat p c) = (signedResidue p c : F) := by
  change residueHom p F (c : Hex.ZMod64 p) = _
  rw [map_natCast]
  unfold signedResidue
  split <;> simp

public meta section

open Lean Meta

/-- Simplify only the evaluation syntax when displaying a condition. No local
hypothesis or field-specific identity changes the polynomial denominator. -/
def displayPolynomial (d : Expr) (extraUnfold : Array Name := #[]) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for name in #[``residue_signed, ``eval_cons, ``eval_nil, ``Fin.prod_univ_succ,
      ``Fin.prod_univ_zero, ``Int.cast_zero, ``Int.cast_one, ``Int.cast_neg,
      ``Int.cast_ofNat, ``one_mul, ``mul_one, ``zero_mul, ``mul_zero,
      ``zero_add, ``add_zero, ``pow_zero, ``pow_one,
      ``neg_add_eq_sub, ``map_intCast, ``map_natCast, ``map_zero, ``map_one, ``map_neg, ``neg_mul, ``neg_one_mul, ``Fin.val_zero, ``Fin.val_succ, ``List.getD_cons_zero, ``List.getD_cons_succ,
      ``Int.coe_castRingHom] do
    thms ← thms.addConst name
  for decl in extraUnfold do thms ← thms.addDeclToUnfold decl
  thms ← thms.addConst ``List.map_cons
  thms ← thms.addConst ``List.map_nil
  thms ← thms.addDeclToUnfold ``Hex.Reflect.ctxValuation
  thms ← thms.addDeclToUnfold ``Lean.RArray.get
  thms ← thms.addConst ``sub_eq_add_neg (inv := true)
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let methods := Simp.mkDefaultMethodsCore #[]
  let pre : Simp.Simproc := fun e => do
    if e.isAppOfArity ``signedResidue 2 then
      let args := e.getAppArgs
      if !e.hasFVar && !e.hasMVar then
        let some p ← (Meta.evalNat args[0]!).run | return .continue
        let some c ← (Meta.evalNat args[1]!).run | return .continue
        let value : Int := if p < c + c then (c : Int) - p else c
        return .visit { expr := toExpr value, proof? := some (← mkEqRefl e) }
    if !e.hasFVar && !e.hasMVar && e.getAppNumArgs == 2 &&
        (e.isAppOf ``Nat.ble || e.isAppOf ``Nat.blt || e.isAppOf ``Nat.beq) then
      let args := e.getAppArgs
      let some a ← (Meta.evalNat args[0]!).run | return .continue
      let some b ← (Meta.evalNat args[1]!).run | return .continue
      let value : Bool := if e.isAppOf ``Nat.ble then a ≤ b else if e.isAppOf ``Nat.blt then a < b else a == b
      return .visit { expr := toExpr value, proof? := some (← mkEqRefl e) }
    methods.pre e
  return (← Simp.mainCore d ctx {} { methods with pre }).1

/-- Normalize closed numeral conditions, allowing carrier and instance parameters. -/
def closedNormNum (p : Expr) : MetaM (Option Expr) := do
  if p.hasMVar then return none
  -- Type and instance parameters do not make a numeral condition symbolic.
  -- A source value variable still keeps the default normalizer out.
  for fvar in (collectFVars {} p).fvarIds do
    let type ← inferType (mkFVar fvar)
    unless (← whnf type).isSort || (← isClass? type).isSome do return none
  -- `norm_num`'s simplification step knows this even without CharZero.
  try
    let_expr Ne α _ _ := p | return none
    let proof ← mkAppOptM ``one_ne_zero #[α, none, none, none]
    if ← isDefEq (← inferType proof) p then return some proof
  catch _ => pure ()
  try
    let ⟨true, proof⟩ ← Mathlib.Meta.NormNum.deriveBool p | return none
    return some proof
  catch _ => return none


end

end HexReflectMathlib
