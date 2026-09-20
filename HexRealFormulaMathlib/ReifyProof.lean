/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.Normalization
public import HexReflectMathlib.Carrier
public import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring

@[expose] public section

/-! Proof interfaces for coordinate projection and positive denominator clearing. -/

namespace Hex.RealFormula

open scoped HexMvPolyMathlib

/-- Project a sealed polynomial environment into one binder scope. Coordinates
outside that scope are set to zero, rather than becoming new parameters. -/
def Poly.project (σ : Fin m → Option (Fin n)) (p : Poly m) : Poly n :=
  MvPoly.subst (fun i => (σ i).elim 0 MvPoly.X) p

theorem Poly.project_correct (σ : Fin m → Option (Fin n)) (p : Poly m) (ρ : Fin n → ℝ) :
    (p.project σ).eval ρ = p.eval (fun i => (σ i).elim 0 ρ) := by
  unfold project eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial,
    HexMvPolyMathlib.toMvPolynomial_subst,
    ← HexMvPolyMathlib.eval₂_toMvPolynomial]
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.bind₁ _ _) =
    MvPolynomial.eval₂Hom _ _ _
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 2
  funext i
  cases σ i <;> simp

/-- Source comparisons use the same orientation as integer atom differences. -/
def Cmp.rel (c : Cmp) (a b : ℝ) : Prop :=
  match c with
  | .eq => a = b | .ne => a ≠ b | .lt => a < b
  | .le => a ≤ b | .gt => b < a | .ge => b ≤ a

theorem Cmp.clear_correct (c : Cmp) {a b p : ℝ} {d : Nat}
    (hd : 0 < d) (hp : (a - b) * d = p) : c.toProp p ↔ c.rel a b := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hd'
  rw [← hp, mul_comm]
  cases c <;> simp [toProp, rel, mul_neg_iff, mul_nonpos_iff, sub_eq_zero,
    hd', hd0, hd'.le, not_lt_of_ge hd'.le, not_le_of_gt hd']

namespace Denominator

theorem leaf (a : ℝ) : a * (1 : Nat) = a := by simp

theorem scalar {a : ℝ} {n : Int} {d : Nat} (h : Mathlib.Meta.NormNum.IsRat a n d) :
    a * d = n := by
  rw [h.to_raw_eq]
  exact div_mul_cancel₀ _ h.den_nz

theorem negative {a : ℝ} {n d : Nat} (h : a * d = (Int.negOfNat n : ℤ)) :
    a * d = -(n : ℝ) := by simpa using h

theorem natural {a : ℝ} {n d : Nat} (h : a * d = (Int.ofNat n : ℤ)) :
    a * d = (n : ℝ) := by simpa using h

theorem add {a b p q : ℝ} {d e : Nat} (ha : a * d = p) (hb : b * e = q) :
    (a + b) * (d * e : Nat) = p * e + q * d := by
  rw [← ha, ← hb, Nat.cast_mul]; ring

theorem sub {a b p q : ℝ} {d e : Nat} (ha : a * d = p) (hb : b * e = q) :
    (a - b) * (d * e : Nat) = p * e - q * d := by
  rw [← ha, ← hb, Nat.cast_mul]; ring

theorem mul {a b p q : ℝ} {d e : Nat} (ha : a * d = p) (hb : b * e = q) :
    (a * b) * (d * e : Nat) = p * q := by
  rw [← ha, ← hb, Nat.cast_mul]; ring

theorem neg {a p : ℝ} {d : Nat} (ha : a * d = p) : (-a) * d = -p := by
  rw [← ha]; ring

theorem pow {a p : ℝ} {d : Nat} (ha : a * d = p) (k : Nat) :
    a ^ k * (d ^ k : Nat) = p ^ k := by
  rw [← ha, Nat.cast_pow, mul_pow]

theorem div_pos {a b p : ℝ} {d e k : Nat} (ha : a * d = p)
    (hb : b * e = k) (hk : 0 < k) :
    (a / b) * (d * k : Nat) = p * e := by
  have hb0 : b ≠ 0 := by
    intro h
    have : (k : ℝ) = 0 := by simpa [h] using hb.symm
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)) this
  rw [Nat.cast_mul, ← hb, ← ha]
  calc a / b * ((d : ℝ) * (b * e)) = (a / b * b) * (d * e) := by ring
       _ = (a * d) * e := by rw [div_mul_cancel₀ _ hb0]; ring

theorem div_neg {a b p : ℝ} {d e k : Nat} (ha : a * d = p)
    (hb : b * e = -(k : ℝ)) (hk : 0 < k) :
    (a / b) * (d * k : Nat) = (-p) * e := by
  have h := div_pos (neg ha) (a := -a) (b := -b)
    (by simpa using congrArg Neg.neg hb) hk
  simpa using h

end Denominator

/-- Transport a reified scoped proof to the caller's arbitrary free valuation. -/
theorem Scoped.transport (p : Scoped n) (a b : Fin n → ℝ) (source : Prop)
    (hab : a = b) (h : p.toProp a ↔ source) : p.toProp b ↔ source := hab ▸ h

theorem Scoped.imp_correct (p q : Scoped n) (ρ : Fin n → ℝ) :
    (p.imp q).toProp ρ ↔ (p.toProp ρ → q.toProp ρ) := by
  simp [imp, toProp, imp_iff_not_or]

theorem Scoped.iff_correct (p q : Scoped n) (ρ : Fin n → ℝ) :
    (p.iff q).toProp ρ ↔ (p.toProp ρ ↔ q.toProp ρ) := by
  simp [iff, toProp, imp_correct, iff_def]

end Hex.RealFormula
