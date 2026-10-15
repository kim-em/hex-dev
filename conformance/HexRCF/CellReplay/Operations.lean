/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellOperations
import HexRCF.CellReplay.Algebraic.CompleteQuote
import HexRCF.ProofEvidence
namespace Hex.RCF.RealCoefficients.CellReplayTests.Operations
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Schema
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Canonical
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Actual owner-supplied cached arithmetic, with independently checked scalar
facts. The operation equalities are the owner's theorems, not runtime claims. -/
def operations : Hex.RealClosure.Replay.Operations parent.sign :=
  ⟨Hex.RealClosure.Algebraic.Element.cachedOne Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedNeg Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedSub Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedMul Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedInv Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedDiv Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedNeg_eq Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedSub_eq Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedInv_eq Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedDiv_eq Data.reduction Data.reduction_eq Records.facts,
    Hex.RealClosure.Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq Records.facts,
    parent.sign, rfl⟩

def codec : ValueCodec parent.Value :=
  Hex.RealClosure.Algebraic.Element.signCodec Data.base.codec Records.facts

/- These ordinary proofs reuse the independently checked fixture and codec
roundtrip. They are not fresh reductions of the complete literal reader. -/
theorem checked : CellOperations.check operations parent.codec values formula [] cert
    .existsReal CompleteQuote.rootGraph CompleteQuote.cells = .ok true :=
  (CellOperations.check_eq operations parent.codec values formula [] cert .existsReal
    CompleteQuote.rootGraph CompleteQuote.cells).trans CompleteQuote.checked

theorem false_checked : CellOperations.check operations parent.codec values formula [] cert
    .forallReal CompleteQuote.rootGraph CompleteQuote.cells = .ok false :=
  (CellOperations.check_eq operations parent.codec values formula [] cert .forallReal
    CompleteQuote.rootGraph CompleteQuote.cells).trans CompleteQuote.false_checked

theorem false_refused : CellOperations.accept? operations parent.codec values formula [] cert
    .forallReal CompleteQuote.rootGraph CompleteQuote.cells = none := by
  unfold CellOperations.accept?
  rw [false_checked]

theorem guarded_checked : CellOperations.check operations parent.codec values formula [Guards.negativeOne] cert
    .existsReal CompleteQuote.rootGraph CompleteQuote.cells = .ok true :=
  (CellOperations.check_eq operations parent.codec values formula [Guards.negativeOne] cert .existsReal
    CompleteQuote.rootGraph CompleteQuote.cells).trans CompleteQuote.guarded_checked

theorem domains : ∀ d ∈ [Guards.negativeOne], original.value d ≠ 0 :=
  CellOperations.check_domains original operations parent.codec values formula [Guards.negativeOne]
    cert .existsReal CompleteQuote.rootGraph CompleteQuote.cells true guarded_checked

theorem zero_first : CellOperations.check operations codec values formula [0] cert .existsReal
    Codec.Json.Value.null Codec.Json.Value.null = .error .divisor := by
  rw [CellOperations.check_eq]
  rfl

theorem source : ∃ x : ℝ, formula.toProp (RealFormula.append (fun i => original.value (values i)) x) :=
  CellOperations.check_sound original operations parent.codec values formula [] cert
    .existsReal CompleteQuote.rootGraph CompleteQuote.cells checked

/- Execute the supplied-operation path with a strict literal coefficient
codec. Compiled checks do not establish strict rejection of missing intermediate
arithmetic records, whose owner fallback remains separately documented. -/
#eval (show IO Unit from do
  let roots := Literals.roots
  let cells := Codec.Json.arr #[Literals.sections,Literals.sectors]
  for (quantifier, expected) in #[(RealFormula.Quantifier.existsReal,true), (.forallReal,false)] do
    unless CellOperations.check operations codec values formula [] cert quantifier roots cells == .ok expected do
      throw (IO.userError "supplied-operation complete verdict changed")
  unless CellOperations.accept? operations codec values formula [] cert .forallReal roots cells == none do
    throw (IO.userError "false supplied-operation verdict accepted")
  unless CellOperations.check operations codec values formula [Guards.negativeOne,0] cert .existsReal
      Codec.Json.Value.null Codec.Json.Value.null == .error .divisor do
    throw (IO.userError "late zero original guard did not precede decoding")
  unless CellOperations.check operations codec values formula [] cert .existsReal
      roots (.arr #[]) == .error .evidence do
    throw (IO.userError "missing cell layout accepted")
  unless CellOperations.check operations codec values formula [] cert .existsReal
      roots (.arr #[.arr #[],Literals.sectors]) == .error .evidence do
    throw (IO.userError "omitted root sections accepted")
  unless CellOperations.check operations codec values formula [] {cert with context := Data.base.signature}
      .existsReal roots cells == .error .binding do
    throw (IO.userError "stale radical context accepted")
  IO.println "supplied-operation complete replay: both verdicts, guard preflight and malformed/stale packets checked")

open Lean Meta in
run_meta do
  let names := #[``RowOperations.retarget_read, ``CellOperations.prepare_eq,
    ``CellOperations.radical_eq, ``CellOperations.row_eq, ``CellOperations.pointQuery_eq,
    ``CellOperations.pointRow_eq, ``CellOperations.selected_eq, ``CellOperations.linear_eq,
    ``CellOperations.sector_eq, ``CellOperations.formulaRow_eq, ``CellOperations.formulaSector_eq,
    ``CellOperations.readCells_eq, ``CellOperations.fold_eq, ``CellOperations.read_eq,
    ``CellOperations.check_eq, ``CellOperations.accept?_iff, ``CellOperations.check_domains,
    ``CellOperations.check_sound, ``checked, ``false_checked, ``false_refused,
    ``guarded_checked, ``domains, ``zero_first, ``source]
  for name in names do
    let .thmInfo declaration ← getConstInfo name | throwError "expected theorem: {name}"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected supplied-operation proof axiom: {name}"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``CellOperations.check_eq]
  for required in #[``RootReplay.readWith_eq, ``RowOperations.retarget_read,
      ``Descriptor.changeOps_self, ``CellOperations.radical_eq,
      ``CellOperations.sector_eq, ``CellOperations.formulaSector_eq] do
    unless seen.contains required do throwError "supplied-operation equality omitted actual law: {required}"
  logInfo m!"{names.size} actual supplied-operation proof bodies kernel checked; public root/row transport laws retained"
end Hex.RCF.RealCoefficients.CellReplayTests.Operations
