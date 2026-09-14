/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Kernel
public import HexReflect.Proof
public import HexMvPolyMathlib.Aeval

public section

namespace HexReflectMathlib.Kernel

open Hex Hex.Reflect Hex.Reflect.Kernel Hex.MvPoly.Kernel
open scoped HexMvPolyMathlib
attribute [local instance 2000] Ring.toGrindRing

private theorem zeroExp_getD (k j : Nat) : (zeroExp k).getD j 0 = 0 := by
  induction k generalizing j with
  | zero => simp [zeroExp]
  | succ k ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

theorem unitExp_getD (k i j : Nat) (hj : j < k) :
    (unitExp k i).getD j 0 = if j = i then 1 else 0 := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => simpa only [unitExp, List.getD_cons_succ, Nat.succ_ne_zero, ite_false]
          using zeroExp_getD k j
    | succ i =>
      cases j with
      | zero => simp [unitExp]
      | succ j => simpa only [unitExp, List.getD_cons_succ, Nat.succ.injEq]
          using ih i j (by omega)

theorem mono_unitExp (k i : Nat) (hi : i < k) :
    mono k (unitExp k i) = Mono.unit ⟨i, hi⟩ := by
  apply Vector.ext
  intro j hj
  let j' : Fin k := ⟨j, hj⟩
  change (mono k (unitExp k i))[j'] = (Mono.unit ⟨i, hi⟩)[j']
  rw [get_mono, unitExp_getD k i j hj, Mono.getElem_unit]
  simp [j', Fin.ext_iff]

theorem denote_atom (k i : Nat) (hi : i < k) :
    denote (cmp := Mono.grevlex) (atom k i) =
      (MvPoly.X ⟨i, hi⟩ : MvPoly k Int Mono.grevlex) := by
  simp only [atom, denote, mono_unitExp k i hi, MvPoly.add_zero]
  rfl

theorem denote_constant (k : Nat) (z : Int) :
    denote (cmp := Mono.grevlex) (constant k z) =
      (MvPoly.C z : MvPoly k Int Mono.grevlex) := by
  rw [constant, denote_smul, denote_one, MvPoly.mul_one]

theorem denote_power (k : Nat) (p : PolyList Int) (n : Nat) (hp : Canonical k p) :
    denote (cmp := Mono.grevlex) (power k p n) =
      (denote (cmp := Mono.grevlex) p : MvPoly k Int Mono.grevlex) ^ n := by
  induction n with
  | zero => simpa only [power, pow_zero] using
      (denote_one (n := k) (κ := Int) (cmp := Mono.grevlex))
  | succ n ih =>
    rw [power, denote_mul _ _ (canonical_power k p n hp).1 hp.1, ih, pow_succ]

variable {F : Type u} [CommRing F]

/-- The sealed atom environment's evaluation homomorphism. -/
noncomputable abbrev hom (k : Nat) (ctx : Lean.RArray F) :
    MvPoly k Int Mono.grevlex →+* F :=
  HexMvPolyMathlib.eval₂MathlibHom (Int.castRingHom F) (ctxValuation ctx k)

theorem eval_C (k : Nat) (ctx : Lean.RArray F) (z : Int) :
    hom k ctx (MvPoly.C z) = (z : F) := by
  change hom k ctx (z : MvPoly k Int Mono.grevlex) = (z : F)
  exact map_intCast (hom k ctx) z

theorem eval_smul (k : Nat) (ctx : Lean.RArray F) (z : Int) (p : PolyList Int) :
    hom k ctx (denote (cmp := Mono.grevlex) (smul z p)) =
      (z : F) * hom k ctx (denote (cmp := Mono.grevlex) p) := by
  rw [denote_smul, map_mul, eval_C]

/-- Interpretation of the structurally replayed reflected syntax. -/
theorem eval_ringList (k : Nat) (ctx : Lean.RArray F) (e : RingExpr)
    (h : RingExpr.varBound e ≤ k) :
    hom k ctx (denote (cmp := Mono.grevlex) (ringList k e)) = e.denote ctx := by
  induction e with
  | num z | intCast z =>
    rw [ringList, denote_constant]
    simp [hom, HexMvPolyMathlib.eval₂MathlibHom, HexMvPolyMathlib.equiv_apply,
      HexMvPolyMathlib.toMvPolynomial_C, Lean.Grind.CommRing.Expr.denote,
      Lean.Grind.CommRing.denoteInt_eq]
    all_goals exact map_intCast (MvPolynomial.eval₂Hom (Int.castRingHom F) (ctxValuation ctx k)) z
  | natCast z =>
    rw [ringList, denote_constant]
    simp [hom, HexMvPolyMathlib.eval₂MathlibHom, HexMvPolyMathlib.equiv_apply,
      HexMvPolyMathlib.toMvPolynomial_C, Lean.Grind.CommRing.Expr.denote]
  | var i =>
    rw [ringList, denote_atom k i (by simp only [RingExpr.varBound] at h; omega)]
    simp [hom, HexMvPolyMathlib.eval₂MathlibHom, HexMvPolyMathlib.equiv_apply,
      HexMvPolyMathlib.toMvPolynomial_X, Lean.Grind.CommRing.Expr.denote, Lean.Grind.CommRing.Var.denote, ctxValuation]
  | add a b ha hb =>
    rw [ringList, denote_add, map_add, ha (by simp [RingExpr.varBound] at h; omega),
      hb (by simp [RingExpr.varBound] at h; omega)]
    rfl
  | sub a b ha hb =>
    rw [ringList, denote_sub, map_sub, ha (by simp [RingExpr.varBound] at h; omega),
      hb (by simp [RingExpr.varBound] at h; omega)]
    rfl
  | mul a b ha hb =>
    rw [ringList, denote_mul _ _ (canonical_ringList k a).1 (canonical_ringList k b).1,
      map_mul, ha (by simp [RingExpr.varBound] at h; omega),
      hb (by simp [RingExpr.varBound] at h; omega)]
    rfl
  | neg a ha =>
    rw [ringList, denote_neg, map_neg, ha h]
    rfl
  | pow a n ha =>
    rw [ringList, denote_power k _ n (canonical_ringList k a), map_pow, ha h]
    rfl

/-- An entry's quoted polynomial is defined by its canonical list. The only
computational premise is structural list equality, not equality of trees. -/
theorem eval_checked (k : Nat) (ctx : Lean.RArray F) (e : RingExpr) (p : PolyList Int)
    (hbound : RingExpr.varBound e ≤ k)
    (h : beq (ringList k e) p = true) :
    hom k ctx (denote (cmp := Mono.grevlex) p) = e.denote ctx := by
  rw [← beq_eq_true_iff.mp h]
  exact eval_ringList k ctx e hbound

end HexReflectMathlib.Kernel
