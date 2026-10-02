/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormula
public import HexMvPolyMathlib.Correspondence
public import Mathlib.Basic.Real.Basic

public section

/-! Real interpretation of the shared formula syntax, without implicit closure. -/

namespace Hex.RealFormula

open scoped HexMvPolyMathlib

/-- The six real comparisons, always against zero. -/
@[expose] def Cmp.toProp (c : Cmp) (x : ℝ) : Prop :=
  match c with
  | .eq => x = 0 | .ne => x ≠ 0
  | .lt => x < 0 | .le => x ≤ 0 | .gt => 0 < x | .ge => 0 ≤ x

/-- Real polynomial evaluation casts each integer coefficient. -/
@[expose] noncomputable def Poly.eval (p : Poly n) (ρ : Fin n → ℝ) : ℝ :=
  MvPoly.eval₂ (Int.castRingHom ℝ) ρ p

/-- Atom interpretation. -/
@[expose] def Atom.toProp (a : Atom n) (ρ : Fin n → ℝ) : Prop :=
  a.cmp.toProp (a.p.eval ρ)

/-- Pointwise Boolean semantics with exactly the declared free valuation. -/
@[expose] def QF.toProp (p : QF n) (ρ : Fin n → ℝ) : Prop :=
  match p with
  | .atom a => a.toProp ρ
  | .tt => True | .ff => False
  | .not p => ¬p.toProp ρ
  | .and p q => p.toProp ρ ∧ q.toProp ρ
  | .or p q => p.toProp ρ ∨ q.toProp ρ

/-- Append one real value after all existing parameters and outer binders. -/
@[expose] def append (ρ : Fin n → ℝ) (x : ℝ) (i : Fin (n + 1)) : ℝ :=
  if h : i.val < n then ρ ⟨i.val, h⟩ else x

/-- Prefix interpretation proceeds from the outermost binder. -/
@[expose] def Prenex.toProp (p : Prenex n) (ρ : Fin n → ℝ) : Prop :=
  match p with
  | .matrix p => p.toProp ρ
  | .quant .existsReal p => ∃ x : ℝ, p.toProp (append ρ x)
  | .quant .forallReal p => ∀ x : ℝ, p.toProp (append ρ x)

theorem Cmp.complement_correct (c : Cmp) (x : ℝ) :
    c.complement.toProp x ↔ ¬c.toProp x := by
  cases c <;> simp [complement, toProp, not_lt, not_le]

theorem QF.nnfWith_correct (p : QF n) (neg : Bool) (ρ : Fin n → ℝ) :
    (p.nnfWith neg).toProp ρ ↔ if neg then ¬p.toProp ρ else p.toProp ρ := by
  induction p generalizing neg with
  | atom a => cases neg <;> simp [nnfWith, toProp, Atom.toProp, Cmp.complement_correct]
  | tt | ff => cases neg <;> simp [nnfWith, toProp]
  | not p ih => cases neg <;> simp [nnfWith, toProp, ih]
  | and p q ihp ihq | or p q ihp ihq =>
    cases neg <;> simp [nnfWith, toProp, ihp, ihq, imp_iff_not_or]

theorem QF.nnf_correct (p : QF n) (ρ : Fin n → ℝ) :
    p.nnf.toProp ρ ↔ p.toProp ρ := by
  simpa [nnf] using nnfWith_correct p false ρ

theorem QF.imp_correct (p q : QF n) (ρ : Fin n → ℝ) :
    (p.imp q).toProp ρ ↔ (p.toProp ρ → q.toProp ρ) := by
  simp [imp, toProp, imp_iff_not_or]

theorem QF.iff_correct (p q : QF n) (ρ : Fin n → ℝ) :
    (p.iff q).toProp ρ ↔ (p.toProp ρ ↔ q.toProp ρ) := by
  simp [iff, toProp, imp_correct, iff_def]

theorem Poly.rename_correct (σ : Fin n → Fin m) (p : Poly n) (ρ : Fin m → ℝ) :
    Poly.eval (MvPoly.rename Mono.lex σ p) ρ = p.eval (ρ ∘ σ) := by
  unfold eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial,
    HexMvPolyMathlib.toMvPolynomial_rename, MvPolynomial.eval₂_rename,
    HexMvPolyMathlib.eval₂_toMvPolynomial]

theorem QF.rename_correct (σ : Fin n → Fin m) (p : QF n) (ρ : Fin m → ℝ) :
    (p.rename σ).toProp ρ ↔ p.toProp (ρ ∘ σ) := by
  induction p with
  | atom a =>
    change a.cmp.toProp (Poly.eval (MvPoly.rename Mono.lex σ a.p) ρ) ↔ _
    rw [Poly.rename_correct]
    rfl
  | tt | ff => rfl
  | not p ih => exact not_congr ih
  | and p q ihp ihq => exact and_congr ihp ihq
  | or p q ihp ihq => exact or_congr ihp ihq

theorem QF.lift_correct (p : QF n) (ρ : Fin n → ℝ) (x : ℝ) :
    p.lift.toProp (append ρ x) ↔ p.toProp ρ := by
  simpa [lift, Function.comp_def, append] using
    p.rename_correct Fin.castSucc (append ρ x)

theorem append_extend (σ : Fin n → Fin m) (ρ : Fin m → ℝ) (x : ℝ) :
    append ρ x ∘ extend σ = append (ρ ∘ σ) x := by
  funext i
  by_cases h : i.val < n <;> simp [extend, append, h]

theorem Prenex.rename_correct (σ : Fin n → Fin m) (p : Prenex n) (ρ : Fin m → ℝ) :
    (p.rename σ).toProp ρ ↔ p.toProp (ρ ∘ σ) := by
  induction p generalizing m with
  | matrix p => exact p.rename_correct σ ρ
  | quant q p ih =>
    cases q <;> simp only [rename, toProp]
    · exact exists_congr fun x => by rw [ih, append_extend]
    · exact forall_congr' fun x => by rw [ih, append_extend]

end Hex.RealFormula
