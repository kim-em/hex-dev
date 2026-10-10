/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteChain
public meta import HexRealClosureMathlib.FiniteChain
public import KernelReplay.FiniteBase
public meta import KernelReplay.FiniteData
import all HexRealClosure.TowerContext
import all HexRealClosure.BaseContext
import all HexRealClosureMathlib.BaseFinite
import all HexPoly.Dense
import all HexRationalFn.Basic
import all Init.Data.Array.Basic
import all Init.Data.Rat.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteChainProbe

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
local instance : Field (RationalFn (RationalFn Rat)) := HexPolyMathlib.fieldOfGrind

/-- The actual validated history of the two-infinitesimal predecessor. -/
noncomputable def following : FiniteBaseProbe.base.chain.Realization FiniteBaseProbe.registry :=
  .infinitesimal FiniteBaseProbe.first.chain (.infinitesimal FiniteBaseProbe.rational.chain
    (.real .base (.rational FiniteBaseProbe.registry) .base))

end Hex.RealClosure.Algebraic.KernelReplay.FiniteChainProbe

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteChainProbe
open Lean Meta Elab Command
open Hex.SignDet FiniteData

/-- Retain arbitrary validated descriptors and their exact encoded frames as
local inputs; the extraction test never constructs substitute roots. -/
private def withRoot (parent : Expr) (action : Expr → MetaM Unit) : MetaM Unit := do
  let arguments := (← inferType parent).getAppArgs
  let carrier := arguments[1]!
  let sign := arguments[arguments.size - 4]!
  let codec := arguments[arguments.size - 2]!
  let bindingValue := arguments.back!
  let descriptorType ← mkAppM ``Descriptor #[carrier, mkConst ``Tower.Signature, sign, bindingValue]
  withLocalDeclD `descriptor descriptorType fun descriptor => do
    withLocalDeclD `frame (mkConst ``Tower.Literal) fun frame => do
      let encoded ← mkEq (← mkAppM ``Tower.Literal.ofJson
        #[← mkAppM ``Tower.rootData #[codec, descriptor]]) (← mkAppM ``Option.some #[frame])
      withLocalDeclD `encoded encoded fun accepted => do
        action (← mkAppM ``Tower.Chain.root #[parent, descriptor, frame, accepted])

private def mustReject (action : MetaM α) : MetaM Unit := do
  let rejected ← try action *> pure false catch _ => pure true
  unless rejected do throwError "invalid native-chain input was accepted"

syntax (name := finiteChainProbe) "#finite_chain_probe" : command
@[command_elab finiteChainProbe]
def elaborate : CommandElab := fun _ => liftTermElabM do
  let base := mkConst ``FiniteBaseProbe.base
  let parent ← mkAppM ``Tower.Chain.base #[base]
  let original ← mkAppM ``Tower.Context.pack #[parent]
  let empty ← NativeChain.ofContext original
  unless empty.owners.isEmpty && empty.base == base do
    throwError "base-only extraction changed its native owner"
  let readerType ← mkArrow (← mkAppM ``BaseContext.Element #[base]) (mkConst ``Real)
  withLocalDeclD `baseReader readerType fun baseReader => do
    empty.withLevels baseReader fun levels => do
      unless levels.isEmpty do throwError "base-only extraction invented a root level"
    withRoot parent fun first => do
      withRoot first fun second => do
        let context ← mkAppM ``Tower.Context.pack #[second]
        let native ← NativeChain.ofContext context
        let firstOwner := (← inferType first).getAppArgs[1]!.getAppArgs.back!
        let secondOwner := (← inferType second).getAppArgs[1]!.getAppArgs.back!
        unless native.context == context && native.owners == #[firstOwner, secondOwner] do
          throwError "native root owners changed or were reordered"
        native.withLevels baseReader fun levels => do
          let some earlier := levels[0]? | throwError "first native level missing"
          let some later := levels[1]? | throwError "second native level missing"
          unless levels.size == 2 && earlier.read == baseReader &&
              later.read == earlier.reader &&
              levels.map (·.context) == native.owners do
            throwError "native dependency readers lost predecessor order"
          for level in levels do
            for inventory in #[level.entries, level.records, level.facts] do
              unless inventory.getAppFn.isConstOf ``List.nil do
                throwError "native extraction invented dependency evidence"
        mustReject (NativeChain.ofContext context 2)
        let chainType ← inferType second
        withLocalDeclD `opaqueChain chainType fun unknown => do
          mustReject (NativeChain.ofContext (← mkAppM ``Tower.Context.pack #[unknown]))
        let wrongType ← mkArrow (mkConst ``Rat) (mkConst ``Real)
        withLocalDeclD `wrongReader wrongType fun wrong => do
          mustReject (native.withLevels wrong fun _ => pure ())
  mustReject (NativeChain.ofContext (mkConst ``Bool.true))
  let extra ← mkListLit (← mkAppM ``BaseContext.Element #[base]) []
  let statement (read : Expr) (_ : Array FiniteData.Level) : MetaM (Array Expr) :=
    return #[← mkAppM ``Transport.Sum
      #[read, mkConst ``FiniteBaseProbe.left, mkConst ``FiniteBaseProbe.right]]
  let result ← empty.reconstruct (mkConst ``following) extra statement FiniteDataProbe.supply
    (fun _ _ => throwError "base-only reconstruction invoked a native record producer")
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteChainProbe.exists_base,
    levelParams := [], type := result.type, value := result.proof })
  logInfo "actual two-infinitesimal base and two retained root owners extracted; predecessor readers and rejection controls checked"

end Hex.RealClosure.Algebraic.KernelReplay.FiniteChainProbe

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: actual two-infinitesimal base and two retained root owners extracted; predecessor readers and rejection controls checked -/
#guard_msgs in
#finite_chain_probe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteChainProbe.exists_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteChainProbe.exists_base
