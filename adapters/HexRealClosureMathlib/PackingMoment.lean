/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingQuery

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K]

/-- Original packing keys along the actual binary-power recursion, including
its final odd-exponent product. The predecessor obligations follow each key. -/
@[expose] def PowerData (entries : List (Packing context)) (read : E → K)
    (p : Hex.DensePoly (Element context)) (n : Nat) : Prop :=
  if n = 0 then True else if n = 1 then True else
    ProductData entries read p p ∧ PowerData entries read (p * p) (n / 2) ∧
      (if n % 2 = 0 then True else ProductData entries read ((p * p).natPow (n / 2)) p)
termination_by n
decreasing_by omega

/-- Lift every reached square and product of the native exponentiation tree. -/
theorem lift_power (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p : Hex.DensePoly (Element context)) (n : Nat)
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : PowerData entries read p n) :
    Transport.PowerData (fun a : Element context => eval read x a.polynomial) p n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    rw [PowerData] at data
    rw [Transport.PowerData]
    by_cases empty : n = 0
    · simp only [empty, ↓reduceIte] at data ⊢
    · rw [ite_eq_right empty] at data ⊢
      by_cases unit : n = 1
      · simp only [unit, ↓reduceIte] at data ⊢
      rw [ite_eq_right unit] at data ⊢
      refine ⟨lift_product entries read zero x p p equations data.1,
        ih (n / 2) (by omega) (p * p) data.2.1, ?_⟩
      by_cases even : n % 2 = 0
      · simp only [even, ↓reduceIte]
      · rw [ite_eq_right even] at data ⊢
        exact lift_product entries read zero x _ p equations data.2.2

/-- Original packing keys in the actual left-associated moment product fold. -/
@[expose] def FoldData (entries : List (Packing context)) (read : E → K) :
    List (Hex.DensePoly (Element context)) → Hex.DensePoly (Element context) → Prop
  | [], _ => True
  | p :: ps, initial => ProductData entries read initial p ∧ FoldData entries read ps (initial * p)

/-- Lift each actual accumulator product of the retained fold. -/
theorem lift_fold (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (xs : List (Hex.DensePoly (Element context)))
    (initial : Hex.DensePoly (Element context))
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : FoldData entries read xs initial) :
    Transport.FoldData (fun a : Element context => eval read x a.polynomial) xs initial := by
  induction xs generalizing initial with
  | nil => exact trivial
  | cons p ps ih =>
    exact ⟨lift_product entries read zero x initial p equations data.1,
      ih (initial * p) data.2⟩

/-- Every original power and accumulator product in an unreduced moment row. -/
structure MomentData (entries : List (Packing context)) (read : E → K)
    (qs : List (Hex.DensePoly (Element context))) (es : List Nat) : Prop where
  powers : ∀ pair ∈ qs.zip es, PowerData entries read pair.1 pair.2
  products : FoldData entries read ((qs.zip es).map (fun (q, k) => q.natPow k)) 1

/-- Assemble the moment's finite arithmetic from retained packing equations. -/
theorem lift_moment (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (qs : List (Hex.DensePoly (Element context))) (es : List Nat)
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : MomentData entries read qs es) :
    Transport.MomentData (fun a : Element context => eval read x a.polynomial) qs es :=
  ⟨fun pair member => lift_power entries read zero x pair.1 pair.2 equations (data.powers pair member),
    lift_fold entries read zero x _ 1 equations data.products⟩

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_power

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_fold

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_moment
