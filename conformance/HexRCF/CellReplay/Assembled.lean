/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Operations
import HexRCF.RealCoefficients.AlgebraicCells
import HexRCF.RealCoefficients.CellOperations
import HexRCF.RealCoefficients.RealModel
import HexRealClosureTheory.NativeAssemblyModels
import KernelReplay.AxiomClosure
namespace Hex.RCF.RealCoefficients.CellReplayTests.Assembled
open Hex Lean Meta Elab Command Term
open Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RealClosure.Algebraic.KernelReplay
open Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
private def frozenCells : Codec.Json := .arr #[Literals.sections,Literals.sectors]
private def note (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun file => do
      file.putStrLn s!"{← IO.monoMsNow}: {message}"
      file.flush

-- Observe failure without restoring state on behalf of the quotation API.
private meta def rejected (action : MetaM Expr) : MetaM Bool :=
  fun metaContext metaState coreContext coreState => do
    try
      let _ ← action metaContext metaState coreContext coreState
      return false
    catch error =>
      if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
      return true

syntax (name := assembledSource) "#assembled_source" : command
@[command_elab assembledSource]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let base ← mkAppM ``Hex.RealClosure.NumberField.rationalModel
    #[Lean.mkConst ``Hex.RCF.SelectedRootTests.Data.registry]
  let realModel ← RealModel.build (Lean.mkConst ``Schema.parent) base
  note "ordinary-real model constructed; original source authentication begins"
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let .ok source ← Reify.prepare target | throwError "original source was not recognized"
  let values := Lean.mkConst ``Schema.values
  let .forallE _ domain _ _ ← whnf (← inferType values)
    | throwError "original coefficients are not a finite valuation"
  let valuation ← withLocalDeclD `i domain fun i => do
    let value ← mkAppM ``Tower.Model.value #[realModel,mkApp values i]
    mkLambdaFVars #[i] value
  let identity ← elabTermEnsuringType
    (← `(by funext i; fin_cases i; exact Hex.RCF.SelectedRootTests.Data.alpha_value))
    (← mkEq valuation source.valuation)
  synthesizeSyntheticMVarsNoPostponing
  let identity ← instantiateMVars identity
  let negative ← elabType (← `(∃ x : ℝ, x ^ 2 - (-Real.sqrt 2) ≥ 0 ∧
    x ^ 2 - (-Real.sqrt 2) ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let negative ← instantiateMVars negative
  let .ok negativeSource ← Reify.prepare negative
    | throwError "negative-conjugate source control was unsupported"
  unless negativeSource.coefficients.size == 1 &&
      (← isDefEq negativeSource.coefficients[0]! (← elabTerm (← `((Real.sqrt 2 : ℝ))) none)) do
    throwError "negative source did not retain its positive generator"
  let guarded ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧
    x ^ 2 - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) / (Real.sqrt 2 * Real.sqrt 2 - 2) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let guarded ← instantiateMVars guarded
  let .ok guardedSource ← Reify.prepare guarded
    | throwError "original-zero-divisor source control was unsupported"
  unless guardedSource.divisors.size == 1 do
    throwError "original zero divisor disappeared from the source control"
  note "actual closed literal context extraction begins"
  let native ← NativeChain.ofContext (Lean.mkConst ``Hex.RCF.SelectedRootTests.Data.parent)
  note s!"actual original context extracted: {native.owners.size} owners, {native.bindings.size} bindings"
  unless native.owners.size == 1 do throwError "fixed selected field lost its original owner"
  let following ← mkAppM ``AlgebraicCells.following #[Lean.mkConst ``Hex.RCF.SelectedRootTests.Data.registry]
  let models ← native.models following
  note s!"reference prefix models retained: {models.models.size}"
  let assembly ← models.assembly native
  note "actual owner assembly created; reached-operation collection begins"
  let program ← assembly.complete native.owners.size fun operations => do
    let core ← operations.core
    let empty ← mkListLit (← mkAppM ``Tower.Context.Value #[Lean.mkConst ``Schema.parent]) []
    let accept ← mkAppOptM ``CellOperations.accept? #[none, some (Lean.mkConst ``Schema.parent)]
    mkAppM' accept #[core,
      Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Operations.codec,
      Lean.mkConst ``Schema.values, Lean.mkConst ``Schema.formula, empty, Lean.mkConst ``Canonical.cert,
      Lean.mkConst ``Hex.RealFormula.Quantifier.existsReal,
      Lean.mkConst ``Literals.roots, Lean.mkConst ``frozenCells]
  note "reached operations collected; ordinary kernel acceptance begins"
  let (record,rawProof) ← checkedRecordProof program
  let statement ← mkEq program (← mkAppM ``Option.some #[record])
  let proof ← Hex.RCF.checkProof `nativeCompleteCellAcceptance statement
    (mkExpectedPropHint rawProof statement)
  let type ← inferType proof
  let _ ← auditProof proof type
  kernelCheck `__nativeCompleteCellAcceptance type proof
  note s!"original complete packet acceptance checked; record={record.getAppFn.constName!}"
  let quoted ← CellQuote.finishOperations target program rawProof realModel identity
  let name := `Hex.RCF.RealCoefficients.CellReplayTests.Assembled.source
  let quoted ← Hex.RCF.checkProof name target quoted
  let direct ← Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure.audit quoted target
  unless direct == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "direct checked-body axiom closure changed"
  addDecl (.thmDecl {name,levelParams:=[],type:=target,value:=quoted})
  let axioms ← collectAxioms name
  unless axioms.size == 3 && axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "fresh assembled source proof has unexpected axioms"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
  for required in #[``CellOperations.accept?_iff,``CompleteReplay.check_sound,
      ``Tower.Model.root,``Hex.RCF.SelectedRootTests.Data.alpha_value] do
    unless seen.contains required do throwError "fresh source proof omitted an actual bridge: {required}"
  for forbidden in #[``CompleteQuote.checked,``CompleteQuote.source,``Hex.RCF.RealCoefficients.CellReplayTests.Operations.checked,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Operations.source,``Check.source,``CellBuild.build,``ScalarPacket.build] do
    if seen.contains forbidden then throwError "fresh source proof reused fixture acceptance or a producer: {forbidden}"
  for rejectedTarget in [negative,guarded] do
    let before := (← getMCtx).decls.toList.length
    let declarations := (← getEnv).checked.get.constants.map₂.toList.length
    unless ← rejected (CellQuote.finishOperations rejectedTarget program proof realModel identity) do
      throwError "fresh packet accepted a wrong selected value or omitted original guard"
    unless (← getMCtx).decls.toList.length == before &&
        (← getEnv).checked.get.constants.map₂.toList.length == declarations do
      throwError "failed original-goal quotation leaked metavariables or proof declarations"
  note "fresh original-goal proof checked; actual records/model/source bridges and selected-value/guard refusals audited"
  logInfo "fresh original real goal proved from actual reached-record assembly; standard three axioms, no fixture acceptance theorem"
#assembled_source

end Hex.RCF.RealCoefficients.CellReplayTests.Assembled
