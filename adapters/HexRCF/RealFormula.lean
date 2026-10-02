/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.ReifyProof
public import HexRealFormulaMathlib.Variables
public import HexRCF.Decision

public section

/-! Explicit translations between the shared real language and univariate RCF. -/

namespace Hex.RCF.RealFormula

open Hex.RealFormula
open scoped HexMvPolyMathlib

/-- Expand the dense integer coefficient array in the shared coordinate. -/
@[expose] def ofPoly (p : ZPoly) : Poly 1 :=
  ((List.range p.size).map fun i =>
    MvPoly.C (p.coeff i) * (MvPoly.X 0 : Poly 1) ^ i).sum

/-- Collapse a one-coordinate sparse polynomial to a dense integer polynomial. -/
@[expose] def toPoly (p : Poly 1) : ZPoly :=
  (p.termsList.map fun t => DensePoly.monomial (t.1.get 0) t.2).sum

theorem ofPoly_correct (p : ZPoly) (ρ : Fin 1 → ℝ) :
    (ofPoly p).eval ρ = Polynomial.aeval (ρ 0) (HexPolyZMathlib.toPolynomial p) := by
  change HexMvPolyMathlib.aeval ρ (ofPoly p) = _
  simp only [ofPoly, map_list_sum, List.map_map, Function.comp_def,
    map_mul, map_pow, HexMvPolyMathlib.aeval_C, HexMvPolyMathlib.aeval_X]
  rw [Polynomial.aeval_def, HexPolyMathlib.eval₂_toPolynomial]
  rw [← List.sum_toFinset _ List.nodup_range]
  congr 1
  ext i
  simp

theorem toPoly_correct (p : Poly 1) (x : ℝ) :
    Polynomial.aeval x (HexPolyZMathlib.toPolynomial (toPoly p)) =
      p.eval (fun _ => x) := by
  have hm (i : Nat) (c : Int) :
      HexPolyMathlib.toPolynomial (DensePoly.monomial i c) =
        Polynomial.monomial i c := by
    ext j
    simp [Polynomial.coeff_monomial]
  have hs (ts : List (Mono 1 × Int)) :
      Polynomial.aeval x (HexPolyMathlib.toPolynomial
        (ts.map fun t => DensePoly.monomial (t.1.get 0) t.2).sum) =
      (ts.map fun t => (t.2 : ℝ) * x ^ t.1.get 0).sum := by
    induction ts with
    | nil => simp
    | cons t ts ih => simp [HexPolyMathlib.toPolynomial_add, hm, ih]
  rw [toPoly, hs, Poly.eval, MvPoly.eval₂_eq,
    ← List.foldl_map, ← List.sum_eq_foldl]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [HexMvPolyMathlib.monoProd_eq_prod, Fin.prod_univ_one,
    HexMvPolyMathlib.monoEquiv_apply]
  rfl

/-- Preserve the six comparison operators. -/
@[expose] def ofCmp : Hex.RCF.Cmp → Hex.RealFormula.Cmp
  | .eq => .eq | .ne => .ne | .lt => .lt
  | .le => .le | .gt => .gt | .ge => .ge

@[expose] def toCmp : Hex.RealFormula.Cmp → Hex.RCF.Cmp
  | .eq => .eq | .ne => .ne | .lt => .lt
  | .le => .le | .gt => .gt | .ge => .ge

theorem ofCmp_correct (c : Hex.RCF.Cmp) (x : ℝ) :
    (ofCmp c).toProp x ↔ c.toProp x 0 := by cases c <;> rfl

theorem toCmp_correct (c : Hex.RealFormula.Cmp) (x : ℝ) :
    (toCmp c).toProp x 0 ↔ c.toProp x := by cases c <;> rfl

/-- Translate RCF Boolean syntax, expanding implication. -/
@[expose] def ofFormula : Formula → QF 1
  | .atom a => .atom ⟨ofPoly a.p, ofCmp a.cmp⟩
  | .tt => .tt | .ff => .ff
  | .not p => .not (ofFormula p)
  | .and p q => .and (ofFormula p) (ofFormula q)
  | .or p q => .or (ofFormula p) (ofFormula q)
  | .imp p q => (ofFormula p).imp (ofFormula q)

/-- Every quantifier-free formula with one coordinate is an RCF formula. -/
@[expose] def toFormula : QF 1 → Formula
  | .atom a => .atom ⟨toPoly a.p, toCmp a.cmp⟩
  | .tt => .tt | .ff => .ff
  | .not p => .not (toFormula p)
  | .and p q => .and (toFormula p) (toFormula q)
  | .or p q => .or (toFormula p) (toFormula q)

theorem ofFormula_correct (p : Formula) (ρ : Fin 1 → ℝ) :
    (ofFormula p).toProp ρ ↔ p.toProp (ρ 0) := by
  induction p with
  | atom a => exact (ofCmp_correct _ _).trans (by rw [ofPoly_correct]; rfl)
  | tt | ff => rfl
  | not p ih => exact not_congr ih
  | and p q ihp ihq => exact and_congr ihp ihq
  | or p q ihp ihq => exact or_congr ihp ihq
  | imp p q ihp ihq =>
    exact (QF.imp_correct _ _ _).trans (imp_congr ihp ihq)

theorem toFormula_correct (p : QF 1) (x : ℝ) :
    (toFormula p).toProp x ↔ p.toProp (fun _ => x) := by
  induction p with
  | atom a =>
    change (toCmp a.cmp).toProp _ 0 ↔ _
    rw [toPoly_correct]
    exact toCmp_correct _ _
  | tt | ff => rfl
  | not p ih => exact not_congr ih
  | and p q ihp ihq => exact and_congr ihp ihq
  | or p q ihp ihq => exact or_congr ihp ihq

/-- Positive-denominator polynomial for `x - q`. -/
@[expose] def bound (q : Rat) : Poly 1 :=
  MvPoly.C (Int.ofNat q.den) * MvPoly.X 0 - MvPoly.C q.num

theorem bound_correct (q : Rat) (ρ : Fin 1 → ℝ) :
    (bound q).eval ρ = (ρ 0 - (q : ℝ)) * q.den := by
  change HexMvPolyMathlib.aeval ρ (bound q) = _
  simp only [bound, map_sub, map_mul, HexMvPolyMathlib.aeval_C,
    HexMvPolyMathlib.aeval_X]
  change (Int.ofNat q.den : Int) * ρ 0 - (q.num : ℝ) = _
  change ((q.den : Int) : ℝ) * ρ 0 - (q.num : ℝ) = _
  rw [Int.cast_natCast, Rat.cast_def, sub_mul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr q.den_ne_zero)]
  ring

/-- The RCF domain uses an open lower endpoint and a closed upper endpoint. -/
@[expose] def guard (a b : Dyadic) : QF 1 :=
  .and (.atom ⟨bound a.toRat, .gt⟩) (.atom ⟨bound b.toRat, .le⟩)

theorem guard_correct (a b : Dyadic) (ρ : Fin 1 → ℝ) :
    (guard a b).toProp ρ ↔
      ρ 0 ∈ Set.Ioc (HexRealRootsMathlib.Dyadic.toReal a)
        (HexRealRootsMathlib.Dyadic.toReal b) := by
  change Hex.RealFormula.Cmp.toProp .gt _ ∧ Hex.RealFormula.Cmp.toProp .le _ ↔ _
  rw [bound_correct, bound_correct,
    Hex.RealFormula.Cmp.clear_correct .gt a.toRat.den_pos rfl,
    Hex.RealFormula.Cmp.clear_correct .le b.toRat.den_pos rfl]
  simp [Hex.RealFormula.Cmp.rel, Set.mem_Ioc, HexRealRootsMathlib.toReal_eq_cast_toRat]

/-- Translate bounded quantifiers by their half-open guards. -/
@[expose] def ofSentence : Hex.RCF.Sentence → Hex.RealFormula.Sentence
  | .forallReal p => .quant .forallReal (.matrix (ofFormula p))
  | .existsReal p => .quant .existsReal (.matrix (ofFormula p))
  | .forallIoc a b p => .quant .forallReal (.matrix ((guard a b).imp (ofFormula p)))
  | .existsIoc a b p => .quant .existsReal (.matrix (.and (guard a b) (ofFormula p)))

theorem ofSentence_correct (s : Hex.RCF.Sentence) (ρ : Fin 0 → ℝ) :
    (ofSentence s).toProp ρ ↔ s.toProp := by
  cases s <;> simp [ofSentence, Prenex.toProp, QF.toProp, QF.imp_correct,
    ofFormula_correct, guard_correct, Hex.RCF.Sentence.toProp, append]

/-- Accept exactly one remaining real quantifier and no free coordinates. -/
@[expose] def toSentence? : Hex.RealFormula.Sentence → Option Hex.RCF.Sentence
  | .quant .forallReal (.matrix p) => some (.forallReal (toFormula p))
  | .quant .existsReal (.matrix p) => some (.existsReal (toFormula p))
  | _ => none

theorem toSentence_correct {s : Hex.RealFormula.Sentence} {t : Hex.RCF.Sentence}
    (h : toSentence? s = some t) (ρ : Fin 0 → ℝ) : t.toProp ↔ s.toProp ρ := by
  cases s with
  | matrix p => simp [toSentence?] at h
  | quant q p =>
    cases p with
    | quant r p => cases q <;> simp [toSentence?] at h
    | matrix p =>
      cases q <;> simp only [toSentence?, Option.some.injEq] at h <;> subst t
      all_goals
        simp only [Hex.RCF.Sentence.toProp, Prenex.toProp, toFormula_correct]
        rfl

/-- Remove only parameters proved absent, retaining the final coordinate. -/
@[expose] def univariate? : {n : Nat} → QF (n + 1) → Option (QF 1)
  | 0, p => some p
  | n + 1, p => (p.drop? 0).bind (univariate? (n := n))

theorem univariate_correct {n : Nat} {p : QF (n + 1)} {u : QF 1}
    (h : univariate? p = some u) (ρ : Fin (n + 1) → ℝ) :
    u.toProp (fun _ => ρ ⟨n, Nat.lt_succ_self n⟩) ↔ p.toProp ρ := by
  induction n with
  | zero =>
    simp only [univariate?, Option.some.injEq] at h
    subst u
    have hv : (fun _ : Fin 1 => ρ ⟨0, Nat.lt_succ_self 0⟩) = ρ := by
      funext i
      apply congrArg ρ
      apply Fin.ext
      omega
    rw [hv]
  | succ n ih =>
    obtain ⟨v, hv, hu⟩ := Option.bind_eq_some_iff.mp h
    unfold QF.drop? at hv
    split at hv
    next hd =>
      simp only [Option.some.injEq] at hv
      subst v
      have hi := ih hu (ρ ∘ (0 : Fin (n + 2)).succAbove)
      have he : (0 : Fin (n + 2)).succAbove ⟨n, Nat.lt_succ_self n⟩ =
          ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := by ext; simp
      simpa only [Function.comp_apply, he] using hi.trans (QF.drop_correct 0 p hd ρ)
    next hd => simp at hv

/-- An innermost residue is eligible only after every symbolic parameter is absent. -/
@[expose] def residue? (q : Quantifier) (p : QF (n + 1)) : Option Hex.RCF.Sentence :=
  (univariate? p).map fun u => match q with
    | .existsReal => .existsReal (toFormula u)
    | .forallReal => .forallReal (toFormula u)

theorem residue_correct {q : Quantifier} {p : QF (n + 1)} {s : Hex.RCF.Sentence}
    (h : residue? q p = some s) (ρ : Fin n → ℝ) :
    s.toProp ↔ (Prenex.quant q (.matrix p)).toProp ρ := by
  obtain ⟨u, hu, hs⟩ := Option.map_eq_some_iff.mp h
  cases q <;> subst s
  · apply exists_congr
    intro x
    exact (toFormula_correct u x).trans (by simpa [append, Prenex.toProp] using univariate_correct hu (append ρ x))
  · apply forall_congr'
    intro x
    exact (toFormula_correct u x).trans (by simpa [append, Prenex.toProp] using univariate_correct hu (append ρ x))

/-- Certificate checking composes directly with the shared semantics. -/
theorem check_sound {s : Hex.RealFormula.Sentence} {t : Hex.RCF.Sentence}
    (h : toSentence? s = some t) (cert : Certificate) (hc : cert.check t = true)
    (ρ : Fin 0 → ℝ) : s.toProp ρ :=
  (toSentence_correct h ρ).mp (Hex.RCF.check_sound t cert hc)

/-- Run the existing RCF certificate construction on eligible shared input. -/
@[expose] def decide? (s : Hex.RealFormula.Sentence) : Option Bool :=
  (toSentence? s).bind Hex.RCF.decide

theorem decide_sound {s : Hex.RealFormula.Sentence} (h : decide? s = some true)
    (ρ : Fin 0 → ℝ) : s.toProp ρ := by
  obtain ⟨t, ht, hdec⟩ := Option.bind_eq_some_iff.mp h
  exact (toSentence_correct ht ρ).mp (Hex.RCF.decide_sound t hdec)

end Hex.RCF.RealFormula
