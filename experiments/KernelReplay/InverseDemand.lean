/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.Inverse
public meta import KernelReplay.Inverse
public import HexRealClosure.InverseReplay
public meta import HexRealClosure.InverseReplay
import all HexRealClosure.InverseReplay
import all HexRealClosure.Packing
import all HexRealClosure.ReplayOperations
import all HexRealClosure.Algebraic
import all HexRealClosureMathlib.PackingConformance
import all HexRealClosureMathlib.CoefficientSignsConformance
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Euclid.DivGcd
import all HexPoly.Dense
import all Init.Data.Rat.Basic

import all HexRealClosure.InversePacking

import all HexSignDet.DagSelectedSigns

import all HexSignDet.Codec

import all HexSignDet.Codec.Basic

import all HexSignDet.Codec.Json

import all HexSignDet.Codec.Node

import all HexSignDet.Codec.Evidence

import all HexSignDet.Codec.Value

import all Init.Data.Array.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.InverseDemand
open CoefficientSignsConformance PackingConformance

@[expose] def invert (facts : List (InverseFact context)) (argument : Element context) : Bool :=
  decide (((Element.replayInverse facts).inv argument).sign = 1)

@[expose] def divide (entries : List (Algebraic.Packing context))
    (facts : List (InverseFact context)) : Bool :=
  decide (((Element.replayQuotient inferInstance inferInstance rfl rfl entries facts).div
    small small).sign = 1)

public meta section
open Lean Meta Elab Command

private unsafe def accepted : TermElabM Unit := do
  let initial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (InverseFact context)))) none)
  let packingInitial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (Algebraic.Packing context)))) none)
  let zero ← Term.withoutErrToSorry (Term.elabTerm (← `((0 : Element context))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let initial ← instantiateMVars initial
  let packingInitial ← instantiateMVars packingInitial
  let zero ← instantiateMVars zero
  let argument := mkConst ``PackingConformance.small
  let simpContext ← Simp.mkContext (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let zeroProgram ← withLocalDeclD `facts (← inferType initial) fun facts =>
    mkLambdaFVars #[facts] (mkApp2 (mkConst ``invert) facts zero)
  let vanished ← collectMany 0 zeroProgram #[⟨initial⟩] simpContext (fun _ _ => pure none)
  match vanished.outcome with
  | .checked false .. => pure ()
  | _ => throwError "zero inversion requested a nonzero candidate"
  unless vanished.requests.isEmpty do throwError "zero inversion requested evidence"
  let program ← withLocalDeclD `facts (← inferType initial) fun facts =>
    mkLambdaFVars #[facts] (mkApp2 (mkConst ``invert) facts argument)
  let uncovered ← collectMany 0 program #[⟨initial⟩] simpContext (fun _ _ => pure none)
  match uncovered.outcome with
  | .missing _ => pure ()
  | _ => throwError "nonzero inversion bypassed inverse-equation evidence"
  let some needed := uncovered.requests[0]? | throwError "missing inverse request"
  unless uncovered.requests.size == 1 && needed.kind == .inverse do
    throwError "wrong inverse demand"
  let some requestedArgument := needed.value | throwError "inverse request lost its operand"
  kernelCheck `__inverseDemandArgument (← mkEq requestedArgument argument) (← mkEqRefl argument)
  let packet ← InverseProbe.produce
  let some entry ← Packing.readRecord packet.packing | throwError "valid packing rejected"
  let some record ← InverseProbe.readRecord argument packet | throwError "valid inverse rejected"
  let candidate ← mkAppM ``Algebraic.Packing.Inverse.candidate #[record]
  let candidate ← mkAppM ``Eq.symm #[candidate]
  kernelCheck `__inverseDemandCandidate (← mkEq needed.polynomial (mkConst ``inverseKey)) candidate
  let fact ← mkAppM ``InverseFact.mk #[entry, record]
  let checked ← collectMany 1 program #[⟨initial⟩] simpContext (fun request _ => do
    unless request.kind == .inverse do throwError "wrong inventory demand"
    return some fact)
  match checked.outcome with
  | .checked true proof _ =>
    kernelCheck `__inverseDemandAccepted
      (← mkEq (mkAppN program (checked.inventories.map Inventory.facts)) (mkConst ``Bool.true)) proof
  | _ => throwError "checked inverse record did not replay"
  let repeated ← collectMany 0 program checked.inventories simpContext
    (fun _ _ => throwError "cached inverse replay called producer")
  match repeated.outcome with
  | .checked true .. => pure ()
  | _ => throwError "cached inverse replay failed"
  unless repeated.requests.isEmpty do throwError "cached inverse requested new evidence"
  let divided ← collectMany 2 (mkConst ``divide) #[⟨packingInitial⟩, ⟨initial⟩] simpContext
    (fun request _ => do
      if request.kind == .inverse then return some fact
      let some produced ← Packing.produce request | return none
      Packing.readRecord produced)
  match divided.outcome with
  | .checked true proof _ =>
    kernelCheck `__inverseDemandDivision
      (← mkEq (mkAppN (mkConst ``divide) (divided.inventories.map Inventory.facts))
        (mkConst ``Bool.true)) proof
  | _ => throwError "division lacked its inverse equation or product packing"
  unless divided.requests.size == 2 do throwError "wrong division dependency count"
  let some first := divided.requests[0]? | throwError "missing division inverse"
  let some second := divided.requests[1]? | throwError "missing division product"
  unless first.kind == .inverse && second.kind == .coefficient do
    throwError "division did not demand its inverse before the outer product packing"
  let cached ← collectMany 0 (mkConst ``divide) divided.inventories simpContext
    (fun _ _ => throwError "cached division called producer")
  match cached.outcome with
  | .checked true .. => pure ()
  | _ => throwError "cached checked division failed"
  unless cached.requests.isEmpty do throwError "cached division requested new evidence"
  let changedProgram ← withLocalDeclD `facts (← inferType initial) fun facts =>
    mkLambdaFVars #[facts] (mkApp2 (mkConst ``invert) facts (mkConst ``PackingConformance.literal))
  let wrongOperand ← collectMany 0 changedProgram checked.inventories simpContext
    (fun _ _ => pure none)
  match wrongOperand.outcome with
  | .missing _ => pure ()
  | _ => throwError "same-value stored operand reused another inverse equation"
  logInfo "inverse equations demanded; zero, exact operand, division dependencies and cached replay kernel checked"

syntax (name := inverseDemand) "#inverse_demand" : command
@[command_elab inverseDemand]
unsafe def elaborateDemand : CommandElab := fun _ => liftTermElabM accepted
end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- info: inverse equations demanded; zero, exact operand, division dependencies and cached replay kernel checked -/
#guard_msgs in
#inverse_demand
end Hex.RealClosure.Algebraic.KernelReplay.InverseDemand
