/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Quoted
import HexRCF.RealCoefficients.CellReuse
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

abbrev transfer := @CellReplay.Evidence.changeFormula

def matrix (left right : RealFormula.Cmp) (either negate : Bool) : QF 2 :=
  let first := QF.atom ⟨Schema.atom, left⟩
  let second := QF.atom ⟨Schema.atom, right⟩
  let pair := if either then QF.or first second else QF.and first second
  .and (if negate then .not pair else pair) (.atom ⟨0, .eq⟩)

theorem same (left right : RealFormula.Cmp) (either negate : Bool) :
    RepresentationSpecialize.prepare Schema.values Schema.formula =
      RepresentationSpecialize.prepare Schema.values (matrix left right either negate) := by
  cases either <;> cases negate <;> rfl

def evidence (left right : RealFormula.Cmp) (either negate : Bool) :=
  transfer (same left right either negate) Canonical.evidence

open Lean Meta Elab Command Term
elab "#boolean_algebraic_cells" : command => liftTermElabM do
  for (left,right,either,negate,quantifier,verdict,suffix) in #[
      (RealFormula.Cmp.lt,RealFormula.Cmp.ge,true,false,Quantifier.forallReal,true,"lt_or_ge"),
      (RealFormula.Cmp.eq,RealFormula.Cmp.ne,true,false,Quantifier.forallReal,true,"eq_or_ne"),
      (RealFormula.Cmp.lt,RealFormula.Cmp.ge,false,false,Quantifier.existsReal,false,"incompatible"),
      (RealFormula.Cmp.gt,RealFormula.Cmp.ne,false,false,Quantifier.existsReal,true,"positive"),
      (RealFormula.Cmp.le,RealFormula.Cmp.ne,false,false,Quantifier.existsReal,true,"negative"),
      (RealFormula.Cmp.gt,RealFormula.Cmp.ge,false,true,Quantifier.forallReal,false,"not_all_positive")] do
    let cmp (c : RealFormula.Cmp) := Lean.mkConst (match c with
      | .eq => ``RealFormula.Cmp.eq | .ne => ``RealFormula.Cmp.ne | .lt => ``RealFormula.Cmp.lt
      | .le => ``RealFormula.Cmp.le | .gt => ``RealFormula.Cmp.gt | .ge => ``RealFormula.Cmp.ge)
    let args := #[cmp left,cmp right,toExpr either,toExpr negate]
    let data := mkAppN (Lean.mkConst ``evidence) args
    let q := Lean.mkConst (if quantifier == .existsReal then ``Quantifier.existsReal else ``Quantifier.forallReal)
    let run ← mkAppM ``CellReplay.Evidence.run #[data,q]
    let expected ← mkAppM ``Option.some #[toExpr verdict]
    let type ← mkEq run expected
    let proof ← mkDecideProof type
    Hex.RCF.SelectedRootTests.KernelCheck.addChecked (Name.str `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean suffix)
      type proof #[``Hex.SignDet.Descriptor.ofReplay?] #[``CellReplay.Evidence.run]
    logInfo m!"checked algebraic Boolean fold {suffix}"
#boolean_algebraic_cells
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean
