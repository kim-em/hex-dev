/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteReconstruction
public meta import HexRealClosureTheory.FiniteReconstruction
public meta import KernelReplay.FiniteData

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.LookupReplay
open Lean Meta Elab Command FiniteData

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"lookup replay: {message}"
      handle.flush

syntax (name := lookupReplay) "#lookup_replay" : command
@[command_elab lookupReplay]
def elaborate : CommandElab := fun _ => liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    diagnostic "read existing checked record"
    let fact ← Term.elabTerm (← `(FiniteTowerProbe.nestedEntries[0]'(by decide))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let fact ← instantiateMVars fact
    let polynomial ← mkAppM ``Packing.original #[fact]
    let entries ← mkListLit (← inferType fact) []
    let found ← mkAppM ``Packing.find #[entries, polynomial]
    let missing ← mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true)
    let leaf : Leaf := ⟨missing, ← getLCtx, ← getLocalInstances⟩
    let some lookup ← leaf.lookup? | throwError "retained lookup control lost its original key"
    let (_, some known) ← lookup.insertKnown fact #[⟨entries⟩]
      | throwError "checked insertion did not retain its closed lookup proof"
    diagnostic "checked insertion retained"
    let base := mkConst ``FiniteBaseProbe.base
    let coefficient ← mkAppM ``BaseContext.Element #[base]
    let readType ← mkArrow coefficient (mkConst ``Real)
    let extra ← mkListLit coefficient [mkConst ``FiniteBaseProbe.epsilon]
    withLocalDeclD `read readType fun read => do
      if (known.lookup.leaf.context.find? read.fvarId!).isSome then
        throwError "saved closed leaf already contains the later caller local"
      -- Cache lookup must preserve the caller's checks of other Boolean predicates.
      let calls ← IO.mkRef (#[] : Array Expr)
      let ordinary ← mkEq (mkConst ``Bool.true) (mkConst ``Bool.true)
      let ordinaryLeaf : Leaf := ⟨ordinary, ← getLCtx, ← getLocalInstances⟩
      let checks : Supplier := fun type => do
        calls.modify (·.push type)
        FiniteDataProbe.supply type
      diagnostic "ordinary Boolean fallback begin"
      let ordinaryResult ← reconstruct base (mkConst ``FiniteReconstructionProbe.following)
        read ⟨#[], #[], #[ordinaryLeaf], true, #[known]⟩ extra checks
      unless (← calls.get).contains ordinary do
        throwError "retained lookup wrapper suppressed a non-lookup Boolean check"
      kernelCheck `__ordinaryBoolean ordinaryResult.type ordinaryResult.proof
      diagnostic "ordinary Boolean fallback checked"
      -- The checked lookup is sufficient even when the caller supplies no decision.
      diagnostic "cached lookup reconstruction begin"
      let result ← reconstruct base (mkConst ``FiniteReconstructionProbe.following)
        read ⟨#[], #[], #[known.lookup.leaf], true, #[known]⟩ extra (fun _ => pure none)
      if result.type.hasFVar || result.proof.hasFVar then
        throwError "retained lookup reconstruction kept a discovery hypothesis"
      let _ ← auditProof result.proof result.type
      kernelCheck `__retainedLookupReconstruction result.type result.proof
      let fallbackCalls ← IO.mkRef (#[] : Array Expr)
      let fallback : Supplier := fun type => do
        fallbackCalls.modify (·.push type)
        if type == known.lookup.leaf.type then return some known.proof
        return none
      let fallbackResult ← reconstruct base (mkConst ``FiniteReconstructionProbe.following)
        read ⟨#[], #[], #[known.lookup.leaf], true, #[]⟩ extra fallback
      unless (← fallbackCalls.get).contains known.lookup.leaf.type do
        throwError "lookup cache miss did not reach the caller's decision procedure"
      let _ ← auditProof fallbackResult.proof fallbackResult.type
      kernelCheck `__lookupFallback fallbackResult.type fallbackResult.proof
      let extended ← mkAppM ``List.cons #[fact, known.lookup.inventory]
      let lifted := known.lookup.withInventory extended
      let liftedResult ← reconstruct base (mkConst ``FiniteReconstructionProbe.following)
        read ⟨#[], #[], #[lifted.leaf], true, #[known]⟩ extra
        (fun _ => throwError "lifted cached lookup invoked an external decision")
      let _ ← auditProof liftedResult.proof liftedResult.type
      kernelCheck `__liftedLookupReconstruction liftedResult.type liftedResult.proof
      addDecl (.thmDecl {
        name := `Hex.RealClosure.Algebraic.KernelReplay.LookupReplay.joint,
        levelParams := [], type := result.type, value := result.proof })
    logInfo "reconstruction reuses a checked lookup with no decider and preserves other Boolean checks"

end Hex.RealClosure.Algebraic.KernelReplay.LookupReplay

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: reconstruction reuses a checked lookup with no decider and preserves other Boolean checks -/
#guard_msgs in
#lookup_replay

end

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.LookupReplay.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.LookupReplay.joint
