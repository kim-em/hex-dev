/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.KernelCheck
import HexRCF.SelectedRoot.PacketFields
import HexRCF.SelectedRoot.Packets
import HexRealClosureMathlib.KernelReplay
import Lean.Elab.Command

meta section
namespace Hex.RCF.SelectedRootTests.ReplayTools
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Command Hex Hex.RealClosure Hex.SignDet
open Hex.RealClosure.Algebraic

def readExpression (_index : Nat) (expression : Expr) : MetaM (Option Expr) := do
  let predicate ← mkAppM ``Option.isSome #[expression]
  let proposition ← mkEq predicate (mkConst ``Bool.true)
  let decisionInstance ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let reflexivity ← mkEqRefl (mkConst ``Bool.true)
  let proof := mkAppN (mkConst ``of_decide_eq_true) #[proposition, decisionInstance, reflexivity]
  let _ ← KernelReplay.auditProof proof proposition
  let proofName ← mkFreshUserName `__selectedPacketAccepted
  KernelCheck.addChecked proofName proposition proof
  unless expression.getAppFn.isConstOf ``Read.fromPacket? do
    throwError "expected a frozen scalar packet reader"
  let fact ← mkAppM ``PacketFields.restore
    (expression.getAppArgs.push (mkConst proofName))
  let _ ← KernelReplay.auditProof fact (← inferType fact)
  return some fact

def readPacket (index : Nat) : MetaM (Option Expr) := do
  let packet := mkConst (Name.str `Hex.RCF.SelectedRootTests.Packets s!"packet{index}")
  let polynomial ← mkAppM ``Prod.fst #[packet]
  let rest ← mkAppM ``Prod.snd #[packet]
  let claimed ← mkAppM ``Prod.fst #[rest]
  let graph ← mkAppM ``Prod.snd #[rest]
  readExpression index (mkAppN (mkConst ``Read.fromPacket?) #[polynomial, claimed, graph])

def rules : MetaM SimpTheorems := do
  let mut rules : SimpTheorems := {}
  for name in #[``Read.rawProgram, ``Read.rootProgramAt, ``RootReplay.readDescriptor,
      ``SignRequests.readRoot, ``Codec.readGraph, ``Element.signCodec, ``Codec.tuple,
      ``Dag.descriptor?, ``Dag.replay?, ``Dag.validate?, ``Hex.SignDet.Replay.check,
      ``Hex.SignDet.queryPoly, ``Hex.Sturm.check, ``Hex.SignedRemainderChain.check] do
    rules ← rules.addDeclToUnfold name
  for name in #[``Read.rootProgram_frozen, ``Data.signature_eq, ``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  return rules

end Hex.RCF.SelectedRootTests.ReplayTools
