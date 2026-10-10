/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteReconstruction
public meta import HexRealClosureMathlib.FiniteReconstruction
public import KernelReplay.FiniteTowerPackets
public meta import KernelReplay.FiniteTowerPackets
public import KernelReplay.FiniteJoint
public meta import KernelReplay.FiniteData
import all HexRealClosure.Algebraic
import all HexRealClosure.PackingReplay
import all HexSignDet.Descriptor
import all KernelReplay.FiniteData
import all HexRealClosureMathlib.PackingArithmetic
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

public import KernelReplay.FiniteThomWitness
public meta import KernelReplay.FiniteThomWitness
import all KernelReplay.FiniteThomWitness

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteThomJoint
open Hex.SignDet

/-- Every new packing/sign/inverse record at the rational first predecessor
uses the same exact cast; algebraic carriers receive no field instance. -/
private theorem rationalClosed : Transport.Closed FiniteDataProbe.read (fun _ => True) := by
  refine ⟨trivial, ?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros; simp [FiniteDataProbe.read]

private theorem rationalSign (q : Rat) :
    Sturm.orderSign q = (SignType.sign (FiniteDataProbe.read q) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono q).symm

private theorem firstData (entries : List (Packing FiniteTower.first))
    (signs : List (ValueSign FiniteTower.first)) (facts : List (InverseFact FiniteTower.first)) :
    Packing.Inventory.Data FiniteTower.first entries signs facts FiniteDataProbe.read := by
  apply Packing.Inventory.level_data _ _ _ _ _ (fun _ => True) rationalClosed
  intro q _
  exact ⟨trivial, (rationalSign q).symm, Rat.cast_eq_zero⟩

private theorem zero : FiniteDataProbe.read 0 = 0 := by simp [FiniteDataProbe.read]
private theorem unit : FiniteDataProbe.read 1 = 1 := by simp [FiniteDataProbe.read]

theorem root_raw : FiniteThomWitness.root.raw = FiniteThomWitness.raw := rfl

theorem root_indices : FiniteThomWitness.root.raw.indices = [1, 2] := rfl

theorem root_signs : FiniteThomWitness.root.raw.signs = [1, 1] := rfl

@[expose] def next := Context.adjoin FiniteThomWitness.root (fun _ => false)

public meta section
open Lean Meta Elab Command
syntax (name := finiteThomJoint) "#finite_thom_joint" : command
@[command_elab finiteThomJoint]
unsafe def elaborateJoint : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  -- Literal-check results are scoped to this assembly and its exact propositions.
  -- Unassigned construction premises are deferred to the structural traversal.
  let checked ← IO.mkRef ({} : Std.HashMap Expr (Option Expr))
  let decisions : FiniteData.Supplier := fun type => do
    let type ← instantiateMVars type
    if type.hasMVar then return none
    if let some proof := (← checked.get)[type]? then
      return proof
    let proof ← FiniteDataProbe.supply type
    checked.modify (·.insert type proof)
    return proof
  let owner := mkConst ``FiniteTower.first
  let next := mkConst ``next
  let nextEntries ← mkListLit (← mkAppM ``Packing #[next]) []
  let nextSigns ← mkListLit (← mkAppM ``ValueSign #[next]) []
  let nextFacts ← mkListLit (← mkAppM ``InverseFact #[next]) []
  let readerType ← mkArrow (← mkAppM ``Element #[owner]) (mkConst ``Real)
  withLocalDeclD `reader readerType fun reader => do
    let level : FiniteData.Level := {
      context := owner
      entries := mkConst ``FiniteThomWitness.entries
      records := mkConst ``FiniteThomWitness.signs
      facts := ← mkListLit (← mkAppM ``InverseFact #[owner]) []
      read := mkConst ``FiniteDataProbe.read
      reader := reader }
    let types (levels : Array FiniteData.Level) : MetaM (Array Expr) := do
      let some current := levels[0]? | throwError "full word lost its predecessor"
      let nativeUnit ← mkAppOptM ``One.one #[some (← mkAppM ``Element #[owner]), none]
      let realUnit ← mkAppOptM ``One.one #[some (mkConst ``Real), none]
      return #[← mkAppM ``Packing.Inventory.Data
        #[next, nextEntries, nextSigns, nextFacts, current.reader],
        ← mkEq (mkApp current.reader nativeUnit) realUnit]
    let discovery ← FiniteData.collectDependencies 500 #[level] types decisions
      (fun needed _ => do
        unless ← withTransparency .all (isDefEq needed.request.context owner) do
          throwError "full-word guard has a different owner"
        match needed.request.kind with
        | .coefficient => return some (← FiniteTowerPackets.packing needed.request.polynomial)
        | .valueSign =>
          let some value := needed.request.value | throwError "full-word sign lost its value"
          return some (← FiniteTowerPackets.sign value)
        | .inverse => throwError "full-word descriptor requested an inverse")
    unless discovery.saturated do throwError "complete word retained a missing native guard"
    let some actual := discovery.levels[0]? | throwError "complete word lost its inventory"
    let data ← mkAppM ``firstData #[actual.entries, actual.records, actual.facts]
    let first ← FiniteData.Prefix.ofData data (mkConst ``zero) (mkConst ``unit)
    let second ← first.extend decisions next nextEntries nextSigns nextFacts
    let (type, proof) ← FiniteData.Prefix.joint #[first, second]
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteThomJoint.exists_joint,
      levelParams := [], type, value := proof })
  logInfo "full-word dependency closure and simultaneous ordinary-real witnesses kernel checked"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
/-- info: full-word dependency closure and simultaneous ordinary-real witnesses kernel checked -/
#guard_msgs in
#finite_thom_joint

end Hex.RealClosure.Algebraic.KernelReplay.FiniteThomJoint

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteThomJoint.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteThomJoint.exists_joint
