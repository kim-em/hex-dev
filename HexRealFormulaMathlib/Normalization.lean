/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.Semantics

@[expose] public section

/-! Scoped frontend syntax and prenex conversion with fresh appended binders. -/

namespace Hex.RealFormula

/-- The two connectives across which a fresh binder can be moved. -/
inductive Connective where
  | and | or
  deriving DecidableEq, BEq, Repr

def Connective.apply (c : Connective) (p q : QF n) : QF n :=
  match c with | .and => .and p q | .or => .or p q

def Connective.toProp (c : Connective) (p q : Prop) : Prop :=
  match c with | .and => p ∧ q | .or => p ∨ q

def Connective.dual : Connective → Connective
  | .and => .or | .or => .and

def Quantifier.dual : Quantifier → Quantifier
  | .existsReal => .forallReal | .forallReal => .existsReal

def Quantifier.toProp (q : Quantifier) (p : ℝ → Prop) : Prop :=
  match q with | .existsReal => ∃ x, p x | .forallReal => ∀ x, p x

/-- Move the right prefix out, lifting the left matrix past each fresh binder. -/
def Prenex.joinMatrix (c : Connective) (p : QF n) : Prenex n → Prenex n
  | .matrix q => .matrix (c.apply p q)
  | .quant q rest => .quant q (rest.joinMatrix c p.lift)

/-- Move the left prefix first, preserving binder order inside each operand.
Free-coordinate renaming fixes every binder already belonging to the right operand. -/
def Prenex.join (c : Connective) (p q : Prenex n) : Prenex n :=
  match p with
  | .matrix p => q.joinMatrix c p
  | .quant k rest => .quant k (rest.join c (q.rename Fin.castSucc))

/-- Frontend syntax with local binding before prenex conversion. -/
inductive Scoped : Nat → Type where
  | matrix (p : QF n) : Scoped n
  | not (p : Scoped n) : Scoped n
  | and (p q : Scoped n) : Scoped n
  | or (p q : Scoped n) : Scoped n
  | quant (q : Quantifier) (p : Scoped (n + 1)) : Scoped n
  deriving DecidableEq

def Scoped.imp (p q : Scoped n) : Scoped n := .or (.not p) q
def Scoped.iff (p q : Scoped n) : Scoped n := .and (p.imp q) (q.imp p)

def Scoped.toProp (p : Scoped n) (ρ : Fin n → ℝ) : Prop :=
  match p with
  | .matrix p => p.toProp ρ
  | .not p => ¬p.toProp ρ
  | .and p q => p.toProp ρ ∧ q.toProp ρ
  | .or p q => p.toProp ρ ∨ q.toProp ρ
  | .quant q p => q.toProp fun x => p.toProp (append ρ x)

/-- Normalize polarity on the scoped tree before moving any quantifier.
Negated quantifiers are dualized, and implication is already expanded. -/
def Scoped.toPrenexWith (neg : Bool) (p : Scoped n) : Prenex n :=
  match p with
  | .matrix p => .matrix (p.nnfWith neg)
  | .not p => p.toPrenexWith (!neg)
  | .and p q => Prenex.join (if neg then .or else .and)
      (p.toPrenexWith neg) (q.toPrenexWith neg)
  | .or p q => Prenex.join (if neg then .and else .or)
      (p.toPrenexWith neg) (q.toPrenexWith neg)
  | .quant q p => .quant (if neg then q.dual else q) (p.toPrenexWith neg)

def Scoped.toPrenex (p : Scoped n) : Prenex n := p.toPrenexWith false

theorem Connective.apply_correct (c : Connective) (p q : QF n) (ρ : Fin n → ℝ) :
    (c.apply p q).toProp ρ ↔ c.toProp (p.toProp ρ) (q.toProp ρ) := by
  cases c <;> rfl

theorem Connective.congr (c : Connective) {p q r s : Prop}
    (hp : p ↔ r) (hq : q ↔ s) : c.toProp p q ↔ c.toProp r s := by
  cases c
  · exact and_congr hp hq
  · exact or_congr hp hq

theorem Quantifier.congr (q : Quantifier) {p r : ℝ → Prop}
    (h : ∀ x, p x ↔ r x) : q.toProp p ↔ q.toProp r := by
  cases q
  · exact exists_congr h
  · exact forall_congr' h

theorem Quantifier.move_left (q : Quantifier) (c : Connective) (p : ℝ → Prop) (r : Prop) :
    q.toProp (fun x => c.toProp (p x) r) ↔ c.toProp (q.toProp p) r := by
  by_cases hr : r <;> cases q <;> cases c <;>
    simp [Quantifier.toProp, Connective.toProp, hr]

theorem Quantifier.move_right (q : Quantifier) (c : Connective) (p : Prop) (r : ℝ → Prop) :
    q.toProp (fun x => c.toProp p (r x)) ↔ c.toProp p (q.toProp r) := by
  by_cases hp : p <;> cases q <;> cases c <;>
    simp [Quantifier.toProp, Connective.toProp, hp]

theorem Prenex.quant_correct (q : Quantifier) (p : Prenex (n + 1)) (ρ : Fin n → ℝ) :
    (quant q p).toProp ρ ↔ q.toProp (fun x => p.toProp (append ρ x)) := by
  cases q <;> rfl

theorem Prenex.joinMatrix_correct (c : Connective) (p : QF n) (q : Prenex n)
    (ρ : Fin n → ℝ) :
    (q.joinMatrix c p).toProp ρ ↔ c.toProp (p.toProp ρ) (q.toProp ρ) := by
  induction q with
  | matrix q => exact c.apply_correct p q ρ
  | quant q rest ih =>
    simp only [joinMatrix, quant_correct]
    rw [Quantifier.congr q (fun x => ih p.lift (append ρ x))]
    simp_rw [QF.lift_correct]
    exact q.move_right c _ _

theorem Prenex.join_correct (c : Connective) (p q : Prenex n) (ρ : Fin n → ℝ) :
    (p.join c q).toProp ρ ↔ c.toProp (p.toProp ρ) (q.toProp ρ) := by
  induction p with
  | matrix p => exact joinMatrix_correct c p q ρ
  | quant k p ih =>
    simp only [join, quant_correct]
    rw [Quantifier.congr k (fun x => ih (q.rename Fin.castSucc) (append ρ x))]
    simp_rw [rename_correct]
    have h : ∀ x, append ρ x ∘ Fin.castSucc = ρ := by
      intro x; funext i; simp [append]
    simp_rw [h]
    exact k.move_left c _ _

theorem Scoped.toPrenexWith_correct (p : Scoped n) (neg : Bool) (ρ : Fin n → ℝ) :
    (p.toPrenexWith neg).toProp ρ ↔ if neg then ¬p.toProp ρ else p.toProp ρ := by
  induction p generalizing neg with
  | matrix p => exact p.nnfWith_correct neg ρ
  | not p ih => cases neg <;> simp [toPrenexWith, toProp, ih]
  | and p q ihp ihq | or p q ihp ihq =>
    cases neg <;> simp [toPrenexWith, Prenex.join_correct, toProp,
      Connective.toProp, ihp, ihq, imp_iff_not_or]
  | quant q p ih =>
    cases neg <;> cases q <;>
      simp [toPrenexWith, toProp, Prenex.toProp, Quantifier.toProp, Quantifier.dual, ih]

/-- Prenex normalization preserves interpretation for every free valuation. -/
theorem Scoped.toPrenex_correct (p : Scoped n) (ρ : Fin n → ℝ) :
    p.toPrenex.toProp ρ ↔ p.toProp ρ := by
  simpa [toPrenex] using p.toPrenexWith_correct false ρ

end Hex.RealFormula
