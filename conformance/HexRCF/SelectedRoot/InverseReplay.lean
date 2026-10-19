/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.InverseReplay
import HexRCF.SelectedRoot.InverseData
import HexRCF.SelectedRoot.Packing
import HexRCF.SelectedRoot.KernelCheck

open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data
namespace Hex.RCF.SelectedRootTests.InverseReplay

structure Packet where
  entry : Algebraic.Packing native
  memo : Array (Dag.Checked base.sign base.signature lower.raw.head lower.raw.lower lower.raw.upper)
  index : Nat
  record : Algebraic.Packing.Inverse.Equation entry
  accepted : Hex.RCF.RealCoefficients.InverseReplay.check [alpha] alpha entry memo index = .ok record

def read : Option Packet := do
  let fields ← (Codec.tuple 6 Hex.RCF.SelectedRootTests.InverseData.packet).toOption
  let claim ← (fields[2].getInt?).toOption
  let entry ← Hex.RCF.SelectedRootTests.Packing.readRecord
    fields[0] fields[1] claim fields[3] fields[4]
  let graph ← (Codec.readGraph base.codec Tower.Signature.codec base.signature
    lower.raw.head lower.raw.lower lower.raw.upper fields[5]).toOption
  let memo ← graph.validate? base.sign base.signature lower.raw.head lower.raw.lower lower.raw.upper
  match accepted : Hex.RCF.RealCoefficients.InverseReplay.check [alpha] alpha entry memo graph.root with
  | .error _ => none
  | .ok record => some ⟨entry, memo, graph.root, record, accepted⟩

meta section
open Lean Meta Elab Command
elab "#check_frozen_inverse" : command => liftTermElabM do
  let type ← Term.elabType (← `(read.isSome = true))
  KernelCheck.addChecked `Hex.RCF.SelectedRootTests.InverseReplay.accepted
    (← instantiateMVars type) (← mkEqRefl (mkConst ``Bool.true))
end

#check_frozen_inverse

/-- info: 'Hex.RCF.SelectedRootTests.InverseReplay.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepted
def packet := read.get accepted

theorem source :
    packet.entry.value.denote rational.value rational.zero_iff rational.one rational.add
      rational.sub rational.mul rational.nat rational.sign = (Real.sqrt 2)⁻¹ ∧
      Real.sqrt 2 ≠ 0 := by
  apply Hex.RCF.RealCoefficients.InverseReplay.check_source rational [alpha] alpha packet.entry packet.memo packet.index
    packet.record packet.accepted (Real.sqrt 2)
  change original.value alpha = Real.sqrt 2
  exact alpha_value

theorem domains :
    ∀ divisor ∈ [alpha], divisor.denote rational.value rational.zero_iff rational.one
      rational.add rational.sub rational.mul rational.nat rational.sign ≠ 0 :=
  Hex.RCF.RealCoefficients.InverseReplay.check_domains rational [alpha] alpha packet.entry packet.memo packet.index
    packet.record packet.accepted

/-- info: 'Hex.RCF.SelectedRootTests.InverseReplay.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Hex.RCF.SelectedRootTests.InverseReplay.domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms domains
end Hex.RCF.SelectedRootTests.InverseReplay
