/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NativeSelection
public import HexRCF.RealCoefficients.NativeSources
public section

namespace Hex.RCF.RealCoefficients
open Hex Hex.RealClosure Hex.RealFormula

/-- Ordered coefficient identities. A coordinate refers only to an earlier
generator, so cyclic source dependencies cannot be represented. Selected roots
carry the owner's checked descriptor; inherited values need the actual origin's
real-value evidence. This is source selection, not frozen context discovery. -/
inductive SourceSelection : Nat → Type where
  | nil : SourceSelection 0
  | inherited (previous : SourceSelection n) : SourceSelection (n+1)
  | root (previous : SourceSelection n) {version : Nat} (selected : Root version) :
      SourceSelection (n+1)
  | coordinate (previous : SourceSelection n) (generator : Fin n) (polynomial : DensePoly Rat) :
      SourceSelection (n+1)

namespace SourceSelection

/-- The shared integer schema retains every selected-root constraint and
coefficient relation in the original coordinate order. -/
@[expose] def formula : SourceSelection n → RealFormula.QF n
  | .nil => .tt
  | .inherited previous => previous.formula.lift
  | .root previous selected =>
      .and previous.formula.lift (NativeSelection.selection (Fin.last _) selected.raw)
  | .coordinate previous generator polynomial =>
      .and previous.formula.lift
        (NativeSelection.relation generator.castSucc (Fin.last _) polynomial)

/-- Exactly the coordinates whose identities must come from the inherited
real interpretation rather than from a source-selection constraint. -/
@[expose] def isInherited : SourceSelection n → Fin n → Bool
  | .nil, i => Fin.elim0 i
  | .inherited previous, i => Fin.lastCases true previous.isInherited i
  | .root previous _, i => Fin.lastCases false previous.isInherited i
  | .coordinate previous _ _, i => Fin.lastCases false previous.isInherited i

/-- The real tuple described by the plan. Only inherited coordinates read the
supplied valuation. Computed coordinates use the existing rational polynomial
interpretation at their earlier generator. -/
@[expose] noncomputable def real : SourceSelection n → (Fin n → ℝ) → Fin n → ℝ
  | .nil, _ => Fin.elim0
  | .inherited previous, values =>
      RealFormula.append (previous.real (values ∘ Fin.castSucc)) (values (Fin.last _))
  | .root previous selected, values =>
      RealFormula.append (previous.real (values ∘ Fin.castSucc)) selected.real
  | .coordinate previous generator polynomial, values =>
      let earlier := previous.real (values ∘ Fin.castSucc)
      RealFormula.append earlier ((realPoly polynomial).eval (earlier generator))

/-- The generated real tuple satisfies every selected-root and coordinate
constraint, without unfolding the shared formula in client proofs. -/
theorem formula_real (selection : SourceSelection n) (values : Fin n → ℝ) :
    selection.formula.toProp (selection.real values) := by
  induction selection with
  | nil => trivial
  | inherited previous ih =>
      exact (previous.formula.lift_correct _ _).mpr (ih _)
  | root previous selected ih =>
      refine ⟨(previous.formula.lift_correct _ _).mpr (ih _), ?_⟩
      apply (NativeSelection.identity selected _ _).mpr
      simp [real, RealFormula.append]
  | coordinate previous generator polynomial ih =>
      refine ⟨(previous.formula.lift_correct _ _).mpr (ih _), ?_⟩
      apply (NativeSelection.relation_correct _ _ _ _).mpr
      simp [real, RealFormula.append]

/-- The generated tuple preserves exactly the inherited entries. -/
theorem real_inherited (selection : SourceSelection n) (values : Fin n → ℝ)
    (i : Fin n) (inherited : selection.isInherited i = true) :
    selection.real values i = values i := by
  induction selection with
  | nil => exact Fin.elim0 i
  | @inherited n previous ih =>
      revert inherited
      refine Fin.lastCases (fun _ => ?_) (fun j member => ?_) i
      · simp [real, RealFormula.append]
      · simpa [real, RealFormula.append, Function.comp_def] using
          ih (values ∘ Fin.castSucc) j (by simpa [isInherited] using member)
  | @root n previous version selected ih =>
      revert inherited
      refine Fin.lastCases (fun member => ?_) (fun j member => ?_) i
      · simp [isInherited] at member
      · simpa [real, RealFormula.append, Function.comp_def] using
          ih (values ∘ Fin.castSucc) j (by simpa [isInherited] using member)
  | @coordinate n previous generator polynomial ih =>
      revert inherited
      refine Fin.lastCases (fun member => ?_) (fun j member => ?_) i
      · simp [isInherited] at member
      · simpa [real, RealFormula.append, Function.comp_def] using
          ih (values ∘ Fin.castSucc) j (by simpa [isInherited] using member)

/-- Checked root selection and earlier-generator relations identify the entire
tuple. Merely satisfying a defining polynomial cannot substitute a conjugate. -/
theorem unique (selection : SourceSelection n) (left right : Fin n → ℝ)
    (fixed : ∀ i, selection.isInherited i = true → left i = right i)
    (first : selection.formula.toProp left) (second : selection.formula.toProp right) :
    left = right := by
  induction selection with
  | nil => exact funext (fun i => Fin.elim0 i)
  | @inherited n previous ih =>
      have earlier := ih (left ∘ Fin.castSucc) (right ∘ Fin.castSucc)
        (fun i h => fixed i.castSucc (by simpa [isInherited] using h))
        ((previous.formula.rename_correct Fin.castSucc left).mp first)
        ((previous.formula.rename_correct Fin.castSucc right).mp second)
      funext i
      refine Fin.lastCases ?_ (fun j => congrFun earlier j) i
      exact fixed (Fin.last n) (by simp [isInherited])
  | @root n previous version selected ih =>
      obtain ⟨firstPrefix, firstRoot⟩ := first
      obtain ⟨secondPrefix, secondRoot⟩ := second
      have earlier := ih (left ∘ Fin.castSucc) (right ∘ Fin.castSucc)
        (fun i h => fixed i.castSucc (by simpa [isInherited] using h))
        ((previous.formula.rename_correct Fin.castSucc left).mp firstPrefix)
        ((previous.formula.rename_correct Fin.castSucc right).mp secondPrefix)
      have last := ((NativeSelection.identity selected (Fin.last n) left).mp firstRoot).trans
        ((NativeSelection.identity selected (Fin.last n) right).mp secondRoot).symm
      exact funext (fun i => Fin.lastCases last (fun j => congrFun earlier j) i)
  | @coordinate n previous generator polynomial ih =>
      obtain ⟨firstPrefix, firstCoordinate⟩ := first
      obtain ⟨secondPrefix, secondCoordinate⟩ := second
      have earlier := ih (left ∘ Fin.castSucc) (right ∘ Fin.castSucc)
        (fun i h => fixed i.castSucc (by simpa [isInherited] using h))
        ((previous.formula.rename_correct Fin.castSucc left).mp firstPrefix)
        ((previous.formula.rename_correct Fin.castSucc right).mp secondPrefix)
      have first := (NativeSelection.relation_correct generator.castSucc (Fin.last n)
        polynomial left).mp firstCoordinate
      have second := (NativeSelection.relation_correct generator.castSucc (Fin.last n)
        polynomial right).mp secondCoordinate
      have last : left (Fin.last n) = right (Fin.last n) :=
        first.trans ((congrArg (fun x => (realPoly polynomial).eval x)
          (congrFun earlier generator)).trans second.symm)
      exact funext (fun i => Fin.lastCases last (fun j => congrFun earlier j) i)

/-- Source authentication is coordinatewise agreement with the generated
tuple. No client proof needs to unfold its nested conjunctions or renamings. -/
theorem formula_iff (selection : SourceSelection n) (values : Fin n → ℝ) :
    selection.formula.toProp values ↔ values = selection.real values := by
  constructor
  · intro meaning
    exact selection.unique values (selection.real values)
      (fun i h => (selection.real_inherited values i h).symm)
      meaning (selection.formula_real values)
  · intro same
    exact same.symm ▸ selection.formula_real values

/-- The uniqueness argument consumed by both finite true rows and universal
counterexamples. Inherited identities come from the actual origin history. -/
theorem identifies {registry : BaseContext.Registry} (context : Tower.Context registry)
    (following : context.origin.base.Realization) (selection : SourceSelection n)
    (values : Fin n → context.Value) (source : Fin n → ℝ)
    (authenticated : selection.formula.toProp source)
    (inherited : ∀ i, selection.isInherited i = true →
      context.origin.RealValue following (values i) (source i))
    (coefficients : Fin n → ℝ)
    (fixed : ∀ i, context.origin.RealValue following (values i) (source i) →
      coefficients i = source i)
    (meaning : selection.formula.toProp coefficients) : coefficients = source :=
  selection.unique coefficients source (fun i hi => fixed i (inherited i hi)) meaning authenticated

/-- Realize the generated selection and source matrix at one ordinary point.
The supplied origin history fixes inherited coordinates; the shared selection
proves every remaining identity. All supplied original guards are checked in
that same finite realization. This does not collect source guards or quote a
frozen native row, and makes no root-coverage or total-search claim. -/
theorem exists_real {registry : BaseContext.Registry} (context : Tower.Context registry)
    (following : context.origin.base.Realization) (selection : SourceSelection n)
    (values : Fin n → context.Value) (source : Fin n → ℝ)
    (authenticated : selection.formula.toProp source)
    (inherited : ∀ i, selection.isInherited i = true →
      context.origin.RealValue following (values i) (source i))
    (sample : context.Value) (matrix : RealFormula.QF (n+1)) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval (.and selection.formula.lift matrix)
      (NativeSpecialize.row context values sample (.and selection.formula.lift matrix)) = some true) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a, domain a → domain (-a) ∧ read (-a) = -read a) ∧
      (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample ∧
      (∀ q ∈ matrix.polys,
        (RepresentationSpecialize.polynomial source q).size =
          (RepresentationSpecialize.polynomial values q).size) ∧
      matrix.toProp (RealFormula.append source (read sample)) ∧
      (∀ a ∈ guards, domain a ∧ read a ≠ 0) ∧
      (∀ a r, context.origin.RealValue following a r → domain a ∧ read a = r) :=
  NativeSources.true_real context following values source selection.formula
      (selection.identifies context following values source authenticated inherited)
      sample matrix guards nonzero truth

/-- A true row for the selection and negated matrix yields a real universal
counterexample, with the same generated source authentication and guards. -/
theorem not_forall {registry : BaseContext.Registry} (context : Tower.Context registry)
    (following : context.origin.base.Realization) (selection : SourceSelection n)
    (values : Fin n → context.Value) (source : Fin n → ℝ)
    (authenticated : selection.formula.toProp source)
    (inherited : ∀ i, selection.isInherited i = true →
      context.origin.RealValue following (values i) (source i))
    (sample : context.Value) (matrix : RealFormula.QF (n+1)) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval (.and selection.formula.lift (.not matrix))
      (NativeSpecialize.row context values sample (.and selection.formula.lift (.not matrix))) = some true) :
    (¬ ∀ x : ℝ, matrix.toProp (RealFormula.append source x)) ∧
      ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
        Transport.Closed read domain ∧
        (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample ∧
        ¬ matrix.toProp (RealFormula.append source (read sample)) ∧
        (∀ a ∈ guards, domain a ∧ read a ≠ 0) :=
  NativeSources.not_forall context following values source selection.formula
    (selection.identifies context following values source authenticated inherited)
    sample matrix guards nonzero truth

end SourceSelection
end Hex.RCF.RealCoefficients
