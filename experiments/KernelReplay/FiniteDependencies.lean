/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteDependencies
public meta import HexRealClosureTheory.FiniteDependencies
public import KernelReplay.FiniteJoint
public meta import KernelReplay.FiniteData
import all HexRealClosure.Algebraic
import all HexRealClosure.PackingReplay
import all HexSignDet.Descriptor
import all KernelReplay.FiniteData
import all HexRealClosureTheory.PackingArithmetic
import all HexPoly.Dense
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all Init.Prelude
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.SignCodec
import all HexRealClosure.SignRequests
import all HexSignDet.Dag
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Codec.Coefficients
import all HexRealRoots.TarskiShared
import all HexPoly.Euclid.DivGcd
import all KernelReplay.FiniteTowerProbe

private def delayedNat : Nat → Nat
  | 0 => 0
  | n + 1 => delayedNat n + 1

private def deferred (n : Nat) : Prop :=
  if delayedNat n == n then True else False

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe
open Lean Meta Elab Command

private def retain (name : Name) (type proof : Expr) : MetaM Unit := do
  let binders := (← getLCtx).getFVarIds.map mkFVar
  let type ← mkForallFVars binders type
  let proof ← mkLambdaFVars binders proof
  kernelCheck name type proof
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe ++ name,
    levelParams := [], type, value := proof })

syntax (name := finiteDependenciesProbe) "#finite_dependencies_probe" : command
@[command_elab finiteDependenciesProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let deferredType := mkApp (mkConst ``deferred) (toExpr (1024 : Nat))
  let stopped ← withOptions (fun options => maxRecDepth.set options 256) do
    FiniteData.frontier deferredType (fun type => pure (type.getAppFn.isConstOf ``deferred))
  let [leaf] := stopped.toList |
    throwError "dependency discovery did not retain one stopped native predicate"
  unless leaf.type == deferredType do
    throwError "dependency discovery evaluated a stopped native predicate"
  let owner := mkConst ``FiniteTower.first
  let readType ← mkArrow (mkConst ``Rat) (mkConst ``Real)
  let source ← mkAppM ``Element #[owner]
  let readerType ← mkArrow source (mkConst ``Real)
  withLocalDeclD `read readType fun read =>
    withLocalDeclD `reader readerType fun reader => do
      let level : FiniteData.Level := {
        context := owner
        entries := mkConst ``FiniteTowerProbe.nestedEntries
        records := mkConst ``FiniteTowerProbe.nestedSigns
        facts := ← mkListLit (← mkAppM ``InverseFact #[owner]) []
        read := read
        reader := reader }
      let nativeUnit ← mkAppOptM ``One.one #[some source, none]
      let realUnit ← mkAppOptM ``One.one #[some (mkConst ``Real), none]
      let nativePair ← mkAppM ``Prod.mk #[mkApp reader nativeUnit, mkApp reader nativeUnit]
      let realPair ← mkAppM ``Prod.mk #[realUnit, realUnit]
      let container ← mkEq (← mkAppM ``Option.some #[nativePair])
        (← mkAppM ``Option.some #[realPair])
      let containerLeaves ← FiniteData.frontier container FiniteData.dependencyBoundary
      unless !containerLeaves.isEmpty do
        throwError "container scalar discovery lost its reached equations"
      for leaf in containerLeaves do
        unless leaf.type.getAppFn.isConstOf ``Eq &&
            leaf.type.getAppArgs[0]!.isConstOf ``Real do
          throwError "container scalar discovery stopped before its real-reader equations"
        let some lowered ← level.lower leaf |
          throwError "container scalar discovery missed its demanded unit packing"
        unless lowered.size == 1 do
          throwError "container scalar discovery lost its exact unit key"
      let product ← mkAppM ``Transport.Product
        #[reader, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
      let frontier ← FiniteData.frontier product FiniteData.dependencyBoundary
      unless frontier.size == 1 do throwError "dependency boundary expanded the upper operation"
      let some leaf := frontier[0]? | throwError "dependency boundary lost the operation"
      let some required ← level.lower leaf | throwError "upper operation was not lowered"
      unless required.size == 1 do throwError "product dependency has the wrong arity"
      let expected ← mkAppM ``Packing.ProductData
        #[level.entries, read, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
      let statement ← mkEq required[0]! expected
      retain `productLowering statement (← mkEqRefl required[0]!)
      let decisions : FiniteData.Supplier := fun type => do
        let args := type.getAppArgs
        if type.getAppFn.isConstOf ``Eq && args.size == 3 && args[0]!.isConstOf ``Bool then
          FiniteDataProbe.supply type
        else pure none
      let predecessor ← FiniteData.frontier required[0]! FiniteData.dependencyBoundary decisions
      unless predecessor.size == 2 do throwError "predecessor product lost its product or accumulator sum"
      for operation in predecessor do
        let some coefficients ← operation.coefficients? |
          throwError "predecessor operation lost its original coefficient support"
        unless !coefficients.hasFVar do throwError "coefficient support depends on an unchosen reader"
      let descended ← FiniteData.descend 1 #[level] frontier decisions
      unless descended.size == 2 do throwError "recursive lowering lost a predecessor operation"
      let some productLeaf := descended[0]? | throwError "recursive lowering lost its product"
      let some coefficients ← productLeaf.coefficients? | throwError "recursive lowering lost its inputs"
      let expectedInputs ← mkListLit (mkConst ``Rat) [toExpr (1 : Rat), toExpr (2 : Rat)]
      retain `productInputs (← mkEq coefficients expectedInputs) (← mkEqRefl coefficients)
      try
        let _ ← FiniteData.descend 0 #[level] frontier decisions
        throwError "dependency lowering ignored its depth bound"
      catch error =>
        unless (← error.toMessageData.toString).startsWith "finite dependency lowering exhausted" do
          throw error
      withLocalDeclD `other readerType fun other => do
        let type ← mkAppM ``Transport.Product
          #[other, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]
        let leaf : FiniteData.Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
        unless (← level.lower leaf).isNone do
          throwError "dependency lowering used a different reader of the same type"
      let raw := mkConst ``FiniteTower.nextRaw
      let evidence ← mkAppM ``Hex.SignDet.Replay.leaf #[mkConst ``FiniteDataProbe.decodedNode]
      let original := mkConst ``FiniteTowerProbe.nestedRoot
      kernelCheck `__finiteDependencyRaw
        (← mkEq (← mkAppM ``Hex.SignDet.Descriptor.raw #[original]) raw)
        (mkConst ``FiniteTowerProbe.nestedRoot_raw)
      kernelCheck `__finiteDependencyReplay
        (← mkEq (← mkAppM ``Hex.SignDet.Descriptor.evidence #[original]) evidence)
        (mkConst ``FiniteWitness.root_evidence)
      let sourceSign ← Elab.Term.elabTerm (← `(Element.sign (context := FiniteTower.first))) none
      let targetSign ← Elab.Term.elabTerm (← `(fun x : ℝ => (SignType.sign x : Int))) none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let descriptor ← mkAppM ``Transport.Finite.DescriptorData
        #[reader, ← instantiateMVars sourceSign, ← instantiateMVars targetSign, raw, evidence]
      let descriptorLeaves ← FiniteData.frontier descriptor FiniteData.dependencyBoundary
      unless descriptorLeaves.size == 1 do throwError "descriptor boundary lost its literal replay"
      let lowerDescriptor ← FiniteData.descend 1 #[level] descriptorLeaves decisions
      let mut arithmetic := 0
      for leaf in lowerDescriptor do
        unless (← leaf.lookup?).isNone do throwError "descriptor lowering lost a retained key"
        if let some inputs ← leaf.coefficients? then
          unless ← isDefEq (← inferType inputs) (← mkAppM ``List #[mkConst ``Rat]) do
            throwError "descriptor lowering retained an algebraic coefficient operation"
          arithmetic := arithmetic + 1
      unless arithmetic > 0 do throwError "descriptor lowering lost its predecessor arithmetic"
      let noEntries ← mkListLit (← mkAppM ``Packing #[owner]) []
      let empty := { level with entries := noEntries }
      let requested (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
        let some current := levels[0]? | throwError "dependency discovery lost its level"
        return #[← mkAppM ``Transport.Product
          #[current.reader, mkConst ``FiniteDataProbe.unit, mkConst ``FiniteDataProbe.two]]
      let absent ← FiniteData.collectDependencies 0 #[empty] requested decisions
        (fun _ _ => throwError "zero-fuel dependency discovery invoked a producer")
      unless !absent.saturated && absent.requests.isEmpty do
        throwError "dependency discovery accepted missing records"
      let wrongPolynomial ← mkAppM ``DensePoly.C #[toExpr (3 : Rat)]
      let wrong ← FiniteTowerPackets.packing wrongPolynomial
      try
        let _ ← FiniteData.collectDependencies 1 #[empty] requested decisions
          (fun _ _ => pure (some wrong))
        throwError "dependency collector accepted a different original key"
      catch error =>
        unless (← error.toMessageData.toString).startsWith "finite support record binds a different key" do
          throw error
      let collected ← FiniteData.collectDependencies 1 #[empty] requested decisions
        (fun lookup _ => do
          unless lookup.request.kind == .coefficient do
            throwError "product dependency requested a different record kind"
          return some (← FiniteTowerPackets.packing lookup.request.polynomial))
      unless collected.saturated && collected.requests.size == 1 do
        throwError "dependency record insertion did not reach a fixed point"
      unless collected.leaves.size == 2 do
        throwError "dependency record insertion assumed predecessor arithmetic"
      let cached ← FiniteData.collectDependencies 0 collected.levels requested decisions
        (fun _ _ => throwError "cached dependency discovery invoked a producer")
      unless cached.saturated && cached.requests.isEmpty do
        throwError "cached dependency discovery did not replay"
      let three ← mkAppOptM ``Nat.cast #[some source, none, some (toExpr (3 : Nat))]
      let realThree ← mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some (toExpr (3 : Nat))]
      let castType ← mkEq (mkApp reader three) realThree
      let castLeaf : FiniteData.Leaf := ⟨castType, ← getLCtx, ← getLocalInstances⟩
      let some casts ← level.lower castLeaf | throwError "natural cast dependency was not lowered"
      unless casts.size == 2 do throwError "natural cast lost its key or predecessor equation"
      let keyLeaf : FiniteData.Leaf := ⟨casts[0]!, ← getLCtx, ← getLocalInstances⟩
      let some lookup ← keyLeaf.lookup? | throwError "cast dependency lost its original key"
      let expectedKey ← mkAppM ``DensePoly.C #[toExpr (3 : Rat)]
      retain `castKey (← mkEq lookup.key expectedKey) (← mkEqRefl lookup.key)
      let zero ← mkAppOptM ``Zero.zero #[some source, none]
      let realZero ← mkAppOptM ``Zero.zero #[some (mkConst ``Real), none]
      let zeroLeaf : FiniteData.Leaf := ⟨← mkEq (mkApp reader zero) realZero,
        ← getLCtx, ← getLocalInstances⟩
      let some zeroRequired ← level.lower zeroLeaf | throwError "stored zero dependency was not recognized"
      unless zeroRequired.isEmpty do throwError "stored zero dependency required a packing key"
      logInfo "dependency discovery lowered product and cast premises with unchosen readers; original operands retained"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: dependency discovery lowered product and cast premises with unchosen readers; original operands retained -/
#guard_msgs in
#finite_dependencies_probe

end Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe.productLowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteDependenciesProbe.productLowering
