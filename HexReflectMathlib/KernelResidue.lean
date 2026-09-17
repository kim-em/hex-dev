/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflectMathlib.Kernel
public import HexReflectMathlib.Residue
public import HexReflect.KernelResidue
public import HexMvPolyMathlib.KernelResidue

public section

namespace HexReflectMathlib.Kernel

open Hex Hex.Reflect Hex.Reflect.Kernel Hex.MvPoly.Kernel
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

variable (p : Nat) [Hex.ZMod64.Bounds p]

/-- The sealed environment's evaluation in characteristic `p`. -/
noncomputable abbrev homMod {F : Type u} [CommRing F] [CharP F p]
    (k : Nat) (ctx : Lean.RArray F) : MvPoly k (Hex.ZMod64 p) Mono.grevlex →+* F :=
  HexMvPolyMathlib.eval₂MathlibHom (residueHom p F) (ctxValuation ctx k)

theorem denote_constantMod (k : Nat) (z : Int) :
    denoteMod p (cmp := Mono.grevlex) (constantMod p k z) =
      (MvPoly.C (z : Hex.ZMod64 p) : MvPoly k (Hex.ZMod64 p) Mono.grevlex) := by
  cases z with
  | ofNat n =>
    rw [constantMod, denoteMod_smulMod p n (oneMod_canonical p k), denoteMod_oneMod, mul_one]
    rfl
  | negSucc n =>
    rw [constantMod, denoteMod_negMod p (smulMod_canonical p (n + 1) (oneMod_canonical p k)),
      denoteMod_smulMod p (n + 1) (oneMod_canonical p k), denoteMod_oneMod, mul_one]
    change -(MvPoly.C ((n + 1 : Nat) : Hex.ZMod64 p)) = MvPoly.C (-((n + 1 : Nat) : Hex.ZMod64 p))
    symm
    apply HexMvPolyMathlib.equiv.injective
    simp [HexMvPolyMathlib.equiv_apply, HexMvPolyMathlib.toMvPolynomial_C]

theorem denote_atomMod (hp : 1 < p) (k i : Nat) (hi : i < k) :
    denoteMod p (cmp := Mono.grevlex) (atomMod p k i) =
      (MvPoly.X ⟨i, hi⟩ : MvPoly k (Hex.ZMod64 p) Mono.grevlex) := by
  simp only [atomMod, Nat.blt_eq.mpr hp, ↓reduceIte, denoteMod, toResidues,
    CoeffMap.map, List.map_cons, List.map_nil, denote, mono_unitExp k i hi, MvPoly.add_zero]
  rfl

theorem denote_powerMod (k : Nat) (a : PolyList Nat) (n : Nat) (ha : CanonicalMod p k a) :
    denoteMod p (cmp := Mono.grevlex) (powerMod p k a n) =
      (denoteMod p (cmp := Mono.grevlex) a : MvPoly k (Hex.ZMod64 p) Mono.grevlex) ^ n := by
  induction n with
  | zero => simpa only [powerMod, pow_zero] using
      (denoteMod_oneMod p (n := k) (cmp := Mono.grevlex))
  | succ n ih =>
    rw [powerMod, denoteMod_mulMod p (canonical_powerMod p k a n ha) ha, ih, pow_succ]

variable {F : Type u} [CommRing F] [CharP F p]

/-- Natural-residue replay agrees with the original ring expression. -/
theorem eval_ringListMod (hp : 1 < p) (k : Nat) (ctx : Lean.RArray F) (e : RingExpr)
    (h : RingExpr.varBound e ≤ k) :
    homMod p k ctx (denoteMod p (cmp := Mono.grevlex) (ringListMod p k e)) = e.denote ctx := by
  induction e with
  | num z | intCast z =>
    rw [ringListMod, denote_constantMod]
    change homMod p k ctx (z : MvPoly k (Hex.ZMod64 p) Mono.grevlex) = _
    rw [map_intCast]
    simp [Lean.Grind.CommRing.Expr.denote, Lean.Grind.CommRing.denoteInt_eq]
  | natCast z =>
    rw [ringListMod, denote_constantMod]
    change homMod p k ctx ((z : Int) : MvPoly k (Hex.ZMod64 p) Mono.grevlex) = _
    rw [map_intCast]
    simp [Lean.Grind.CommRing.Expr.denote]
  | var i =>
    rw [ringListMod, denote_atomMod p hp k i (by simp only [RingExpr.varBound] at h; omega)]
    simp [homMod, HexMvPolyMathlib.eval₂MathlibHom, HexMvPolyMathlib.equiv_apply,
      HexMvPolyMathlib.toMvPolynomial_X, Lean.Grind.CommRing.Expr.denote,
      Lean.Grind.CommRing.Var.denote, ctxValuation]
  | add a b ha hb =>
    rw [ringListMod, denoteMod_addMod p (canonical_ringListMod p k a) (canonical_ringListMod p k b),
      map_add, ha (by simp [RingExpr.varBound] at h; omega), hb (by simp [RingExpr.varBound] at h; omega)]
    rfl
  | sub a b ha hb =>
    rw [ringListMod, denoteMod_subMod p (canonical_ringListMod p k a) (canonical_ringListMod p k b),
      map_sub, ha (by simp [RingExpr.varBound] at h; omega), hb (by simp [RingExpr.varBound] at h; omega)]
    rfl
  | mul a b ha hb =>
    rw [ringListMod, denoteMod_mulMod p (canonical_ringListMod p k a) (canonical_ringListMod p k b),
      map_mul, ha (by simp [RingExpr.varBound] at h; omega), hb (by simp [RingExpr.varBound] at h; omega)]
    rfl
  | neg a ha =>
    rw [ringListMod, denoteMod_negMod p (canonical_ringListMod p k a), map_neg, ha h]
    rfl
  | pow a n ha =>
    rw [ringListMod, denote_powerMod p k _ n (canonical_ringListMod p k a), map_pow, ha h]
    rfl

/-- Structural equality identifies a quoted residue polynomial with an entry. -/
theorem eval_checkedMod (hp : 1 < p) (k : Nat) (ctx : Lean.RArray F) (e : RingExpr)
    (a : PolyList Nat) (hbound : RingExpr.varBound e ≤ k)
    (h : beq (ringListMod p k e) a = true) :
    homMod p k ctx (denoteMod p (cmp := Mono.grevlex) a) = e.denote ctx := by
  rw [← beq_eq_true_iff.mp h]
  exact eval_ringListMod p hp k ctx e hbound

end HexReflectMathlib.Kernel
