/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.SourceIdentity
import HexRCF.RealCoefficients.AlgebraicCells
import HexRCF.RealCoefficients.SquareTwo
import HexRCF.SelectedRoot.Data
import HexRealClosureTheory.NativeAssemblyModels
import HexRCF.ProofEvidence
namespace Hex.RCF.SourceIdentityCases
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Term
open Hex.RealClosure.Algebraic.KernelReplay.FiniteData
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

/-- Literal rational coordinates at the actual retained predecessor. -/
def embed (q : DensePoly Rat) : Data.base.Poly :=
  DensePoly.ofCoeffs (q.coeffs.map fun r => ⟨r⟩)

theorem embed_value (q : DensePoly Rat) :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff (embed q) =
      LiteralSign.realPoly q := by
  ext i
  rw [HexPolyTheory.Interpret.coeff_interpret]
  apply (Tower.Model.base_value (BaseContext.rational Data.registry) (Rat.castHom ℝ)
    Hex.RealClosure.ratSign ((embed q).coeff i)).trans
  rw [embed, DensePoly.coeff_ofCoeffs]
  erw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : q.coeffs[i]? with
  | none =>
    erw [Option.map_none, Option.getD_none]
    simp [LiteralSign.realPoly, HexPolyTheory.Interpret.coeff_interpret,
      DensePoly.coeff, Array.getD_eq_getD_getElem?, h]
    rfl
  | some r =>
    erw [Option.map_some, Option.getD_some]
    simp [LiteralSign.realPoly, HexPolyTheory.Interpret.coeff_interpret,
      DensePoly.coeff, Array.getD_eq_getD_getElem?, h]

/-- Read the source polynomial at the descriptor selected by this actual owner. -/
theorem observed (q : DensePoly Rat) (fact : Algebraic.SignFact Data.native)
    (binding : fact.polynomial = embed q) :
    (SignType.sign ((LiteralSign.realPoly q).eval Data.selectedReal) : Int) = fact.sign := by
  exact SourceIdentity.observe Data.rational Data.lower (embed q) q (embed_value q) fact binding

syntax (name := sourceFact) "source_fact% " term : term
@[term_elab sourceFact]
unsafe def elaborateFact : TermElab := fun stx _ => do
  let polynomial ← elabTermEnsuringType stx[1] (← mkAppM ``Tower.Context.Poly #[mkConst ``Data.base])
  synthesizeSyntheticMVarsNoPostponing
  let polynomial ← instantiateMVars polynomial
  let native ← NativeChain.ofContext (mkConst ``Data.parent)
  let following ← mkAppM ``AlgebraicCells.following #[mkConst ``Data.registry]
  let models ← native.models following
  let assembly ← models.assembly native
  assembly.scalar 0 polynomial

def equationFact : Algebraic.SignFact Data.native :=
  source_fact% (embed (ZPoly.toRatPoly SquareTwo.polynomial))
def marginFact : Algebraic.SignFact Data.native :=
  source_fact% (embed (SourceIdentity.margin SquareTwo.square))

theorem equation_binding : equationFact.polynomial = embed (ZPoly.toRatPoly SquareTwo.polynomial) := by decide +kernel
theorem equation_sign : equationFact.sign = 0 := by rfl
theorem margin_binding : marginFact.polynomial = embed (SourceIdentity.margin SquareTwo.square) := by decide +kernel
theorem margin_sign : marginFact.sign = 1 := by rfl

theorem source_zero : (LiteralSign.realPoly (ZPoly.toRatPoly SquareTwo.polynomial)).IsRoot
    Data.selectedReal := by
  have sign := (observed _ equationFact equation_binding).trans equation_sign
  apply sign_eq_zero_iff.mp
  cases tagged : SignType.sign ((LiteralSign.realPoly (ZPoly.toRatPoly SquareTwo.polynomial)).eval
    Data.selectedReal) <;> simp_all

theorem source_margin : 0 < (LiteralSign.realPoly (SourceIdentity.margin SquareTwo.square)).eval
    Data.selectedReal := by
  have sign := (observed _ marginFact margin_binding).trans margin_sign
  apply sign_eq_one_iff.mp
  cases tagged : SignType.sign ((LiteralSign.realPoly (SourceIdentity.margin SquareTwo.square)).eval
    Data.selectedReal) <;> simp_all

/-- The checked source equation and margin select the embedding together. -/
theorem source_selected : Data.selectedReal = Real.sqrt 2 := by
  apply SourceIdentity.select SquareTwo.polynomial SquareTwo.square (by decide +kernel)
    (by decide +kernel) (Real.sqrt 2) Data.selectedReal SquareTwo.square_selected_root source_zero
  rw [← SourceIdentity.margin_eval]
  exact source_margin

/-- The retained literal coordinate has the selected source value without the
fixture's pre-existing square-root identity. -/
theorem coefficient : Data.original.value Data.alpha = Real.sqrt 2 := by
  rw [← Data.generator_eq]
  exact (Data.rational.root_generator (.base (BaseContext.rational Data.registry))
    Data.lower Data.frozenFrame Data.frameEncoded).trans source_selected
end Hex.RCF.SourceIdentityCases
