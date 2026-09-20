/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.Semantics

public section

/-! Exact rational evaluation and list-form kernel interpretation. -/

namespace Hex.RealFormula

open scoped HexMvPolyMathlib

-- Keep list denotation on the computational library's integer instance.
local instance (priority := 3000) : Lean.Grind.Semiring Int :=
  Lean.Grind.instCommRingInt.toCommSemiring.toSemiring

theorem Poly.evalRat_cast (p : Poly n) (q : Fin n → ℚ) :
    ((MvPoly.eval₂ (Int.castRingHom ℚ) q p : ℚ) : ℝ) = p.eval (fun i => (q i : ℝ)) := by
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  change (Rat.castHom ℝ) (MvPolynomial.eval₂ (Int.castRingHom ℚ) q
    (HexMvPolyMathlib.toMvPolynomial p)) = _
  rw [MvPolynomial.eval₂_comp_left]
  change MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (q i : ℝ))
    (HexMvPolyMathlib.toMvPolynomial p) = _
  exact HexMvPolyMathlib.eval₂_toMvPolynomial _ _ p

theorem Cmp.evalRat_correct (c : Cmp) (q : ℚ) :
    c.evalRat q = true ↔ c.toProp (q : ℝ) := by
  cases c <;> simp [evalRat, toProp]

theorem QF.evalRat_correct (p : QF n) (q : Fin n → ℚ) :
    p.evalRat q = true ↔ p.toProp (fun i => (q i : ℝ)) := by
  induction p with
  | atom a =>
    change a.cmp.evalRat _ = true ↔ a.cmp.toProp _
    rw [Cmp.evalRat_correct]
    exact iff_of_eq (congrArg a.cmp.toProp (Poly.evalRat_cast a.p q))
  | tt | ff => simp [evalRat, toProp]
  | not p ih => simp [evalRat, toProp, Bool.eq_false_iff, ih]
  | and p q ihp ihq | or p q ihp ihq => simp [evalRat, toProp, ihp, ihq]

/-- Closed quantifier-free truth agrees with exact rational evaluation.
This theorem makes no assertion about rational quantification. -/
theorem QF.evalRat_closed (p : QF 0) (ρ : Fin 0 → ℝ) :
    p.evalRat Fin.elim0 = true ↔ p.toProp ρ := by
  have h : (fun i : Fin 0 => ((Fin.elim0 i : ℚ) : ℝ)) = ρ :=
    funext fun i => Fin.elim0 i
  rw [evalRat_correct, h]

namespace Kernel

/-- Real interpretation of an integer term list uses list arithmetic only. -/
@[expose] noncomputable def evalPoly (ρ : List ℝ) : MvPoly.Kernel.PolyList Int → ℝ
  | [] => 0
  | (m, c) :: ts => (c : ℝ) * MvPoly.Kernel.evalMono ρ m + evalPoly ρ ts

theorem evalPoly_denote (p : MvPoly.Kernel.PolyList Int) (ρ : List ℝ)
    (hρ : ρ.length = n) (hp : ∀ t ∈ p, t.1.length = n) :
    evalPoly ρ p = Poly.eval (MvPoly.Kernel.denote p) (fun i : Fin n => ρ.getD i.val 0) := by
  unfold Poly.eval
  rw [MvPoly.Kernel.denote_eq_ofTerms]
  rw [MvPoly.eval₂_ofTerms (f := Int.castRingHom ℝ)
    (x := fun i : Fin n => ρ.getD i.val 0) (by simp) (by intros; simp)]
  induction p with
  | nil => rfl
  | cons t ts ih =>
    simp only [evalPoly, List.map_cons, List.foldl_cons]
    rw [zero_add, List.foldl_add_eq_add_foldl,
      MvPoly.Kernel.evalMono_eq_prod hρ (hp t (List.mem_cons_self ..)),
      ih (fun u hu => hp u (List.mem_cons_of_mem _ hu))]
    rfl

/-- Raw list semantics. Correctness of decoding requires the explicit arity check. -/
@[expose] def Body.toProp (p : Body) (ρ : Fin n → ℝ) : Prop :=
  match p with
  | .atom p c => c.toProp (evalPoly (List.ofFn ρ) p)
  | .tt => True | .ff => False
  | .not p => ¬p.toProp ρ
  | .and p q => p.toProp ρ ∧ q.toProp ρ
  | .or p q => p.toProp ρ ∨ q.toProp ρ

/-- Successful decoding preserves raw list semantics. -/
theorem Body.decode_correct (p : Body) (φ : RealFormula.QF n) (ρ : Fin n → ℝ)
    (h : p.decode n = some φ) : p.toProp ρ ↔ φ.toProp ρ := by
  induction p generalizing φ with
  | atom p c =>
    simp only [decode] at h
    split at h
    · rename_i hv
      have hp : ∀ t ∈ p, t.1.length = n := by
        simpa only [List.all_eq_true, beq_iff_eq] using hv
      cases h
      simp only [toProp, RealFormula.QF.toProp, Atom.toProp,
        MvPoly.Kernel.denote_normalize]
      rw [evalPoly_denote p _ List.length_ofFn hp]
      have hval : (fun i : Fin n => (List.ofFn ρ).getD i.val 0) = ρ := by
        funext i
        simp [List.getD_eq_getElem?_getD, i.isLt]
      rw [hval]
    · contradiction
  | tt | ff => cases h; rfl
  | not p ih =>
    cases hd : p.decode n with
    | none => simp [decode, hd] at h
    | some p' =>
      simp [decode, hd] at h
      subst φ
      exact not_congr (ih _ hd)
  | and p q ihp ihq | or p q ihp ihq =>
    cases hp : p.decode n <;> cases hq : q.decode n <;> simp [decode, hp, hq] at h
    subst φ
    first | exact and_congr (ihp _ hp) (ihq _ hq)
          | exact or_congr (ihp _ hp) (ihq _ hq)

/-- The versioned kernel object is interpreted at its declared arity. -/
@[expose] def QF.toProp (p : QF) (ρ : Fin p.arity → ℝ) : Prop := p.body.toProp ρ

end Kernel

theorem QF.kernel_correct (p : QF n) (ρ : Fin n → ℝ) :
    p.toKernel.toProp ρ ↔ p.toProp ρ :=
  Kernel.Body.decode_correct p.kernelBody p ρ p.decode_kernelBody

end Hex.RealFormula
