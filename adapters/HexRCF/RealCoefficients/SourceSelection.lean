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
      (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample ∧
      matrix.toProp (RealFormula.append source (read sample)) ∧
      (∀ a ∈ guards, domain a ∧ read a ≠ 0) := by
  obtain ⟨read, domain, closed, negative, fixed, present, sizes, meaning, guarded, base⟩ :=
    NativeSources.true_real context following values source selection.formula
      (fun coefficients fixed meaning => selection.unique coefficients source
        (fun i hi => fixed i (inherited i hi)) meaning authenticated)
      sample matrix guards nonzero truth
  exact ⟨read, domain, closed, fixed, present, meaning, guarded⟩

end SourceSelection
end Hex.RCF.RealCoefficients
