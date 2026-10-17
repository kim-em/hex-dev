/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPrimitiveFacts
public meta import KernelReplay.GuardPrimitiveFacts
import all KernelReplay.GuardPrimitiveFacts
import all KernelReplay.GuardDescriptorReductions
import all KernelReplay.GuardDescriptorInputs

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorSupplier
open Lean Meta FiniteData GuardDescriptorInputs

structure Supply where
  setup : Setup
  supplier : Supplier
  facts : Array Expr
  hits : IO.Ref Nat
  arithmeticHits : IO.Ref Nat

/-- Use checked predecessor facts and native coefficient-position hints while
keeping the original requested predicate and ordinary kernel boundary. -/
unsafe def prepare (began : Nat) (extra : Array Name := #[]) : MetaM Supply := do
  let setup ← GuardDescriptorInputs.prepare
  let pointEquation ← mkEq setup.first.point (mkConst ``GuardInventoryReplay.firstPoint)
  kernelCheck `__sameDescriptorPredecessor pointEquation
    (mkConst ``GuardDescriptorInputs.firstPointBinding)
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let agreement := mkConst ``GuardInventoryReplay.agreement
  let indexed ← GuardCoefficientIndex.prepare began agreement
  let walk ← IO.mkRef (none : Option CoefficientWalk)
  let fallback := agreementSupplier agreement (some walk)
  let domains := origin.domains (fun type => do
    if let some proof ← indexed type then return some proof
    fallback type)
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let previous := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let environment ← getEnv
  let candidates := environment.checked.get.constants.fold (fun found name info =>
    if info.isTheorem && info.levelParams.isEmpty then found.push name else found) (#[] : Array Name)
  let modules := #[`KernelReplay.GuardDescriptorInputs, `KernelReplay.GuardDescriptorReductions,
    `KernelReplay.GuardPrimitiveFacts] ++ extra
  let mut table : PHashMap Expr Expr := {}
  let mut primitives : PHashMap Expr Expr := {}
  let mut chains : Array Expr := #[]
  let mut proofs : Array Expr := #[]
  for name in candidates do
    let _ ← bounded began
    let some index := environment.getModuleIdxFor? name | continue
    unless modules.contains environment.header.moduleNames[index.toNat]! do continue
    let info ← getConstInfo name
    table := table.insert info.type (mkConst name)
    if let some fingerprint := GuardPrimitiveFacts.key info.type then
      primitives := primitives.insert fingerprint (mkConst name)
    if info.type.getAppFn.isConstOf ``Packing.ChainData then
      chains := chains.push (mkConst name)
    proofs := proofs.push (mkConst name)
  let facts := table
  let arithmetic := primitives
  let checkedChains := chains
  let hits ← IO.mkRef (0 : Nat)
  let arithmeticHits ← IO.mkRef (0 : Nat)
  let supplier : Supplier := fun type => do
    if !type.hasFVar && !type.hasMVar then
      if type.getAppFn.isConstOf ``Packing.ChainData then
        for proof in checkedChains do
          let remaining ← bounded began
          let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
          match (← getEnv).toKernelEnv.addDecl options (.thmDecl {
              name := `__convertedSignedChain, levelParams := [], type, value := proof }) with
          | .ok _ =>
            hits.modify (· + 1)
            if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
              IO.FS.withFile path .append fun handle => do
                handle.putStrLn s!"complete signed chain converted: proof={proof.constName?} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
                handle.flush
            return some proof
          | .error (.declTypeMismatch ..) => pure ()
          | .error (.appTypeMismatch ..) => pure ()
          | .error (.exprTypeMismatch ..) => pure ()
          | .error error => ofExceptKernelException (Except.error error)
      if let some proof := facts.find? type then
        let remaining ← bounded began
        withOptions (maxHeartbeats.set · remaining) do
          kernelCheck `__retainedDescriptorPremise type proof
        hits.modify (· + 1)
        return some proof
      if let some fingerprint := GuardPrimitiveFacts.key type then
        if let some proof := arithmetic.find? fingerprint then
          let remaining ← bounded began
          withOptions (maxHeartbeats.set · remaining) do
            kernelCheck `__retainedDescriptorArithmetic type proof
          hits.modify (· + 1)
          arithmeticHits.modify (· + 1)
          return some proof
    previous type
  return ⟨setup, supplier, proofs, hits, arithmeticHits⟩

end Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorSupplier
