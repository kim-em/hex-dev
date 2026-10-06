/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.RationalRoot
public meta import KernelReplay.RationalRoot
public import HexRealClosure.SignCodec
public import HexRealClosure.SignRequests
import all HexRealClosure.Algebraic
import all HexSignDet.Descriptor
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
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteTower
open Hex.SignDet

@[expose] def firstRaw : RawDescriptor Rat Nat :=
  ⟨7, DensePoly.ofCoeffs #[-2, 0, 1], .finite 1, .finite 2, [], []⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
/-- The first actual selected root is rebuilt from native-produced literal
packets with the ordinary kernel; no native proof object is quoted. -/
@[expose] def firstRoot : Descriptor Rat Nat Sturm.orderSign 7 := rational_root% firstRaw

@[expose] def first := Context.adjoin firstRoot (fun _ => true)

theorem firstRoot_raw : firstRoot.raw = firstRaw := rfl

private theorem canReduce : first.canReduce = true := by
  rw [first.reduce_checked]
  simp only [first, Context.root_adjoin, Context.clean_adjoin, firstRoot_raw, firstRaw,
    ← Array.all_toList]
  decide +kernel

/-- Keep the actual monic reduction separate from prepared-cache construction. -/
@[expose] def reduction (p : DensePoly Rat) : DensePoly Rat :=
  (DensePoly.divModMonic p firstRaw.head (by
    change firstRaw.head.leadingCoeff = 1
    decide +kernel)).2

theorem reduction_eq : reduction = first.reduce := by
  funext p
  rw [Context.reduce, dite_eq_left canReduce]
  simp only [first, Context.root_adjoin, firstRoot_raw]
  rfl

@[expose] def variablePoly : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
@[expose] def generatorFact : SignFact first := rational_fact% first, variablePoly

/-- The actual first generator retains its literal linear polynomial. -/
@[expose] def generator : Element first :=
  Element.restore variablePoly 1 (by
    have checked := generatorFact.checked
    change first.signPoly variablePoly = 1 at checked
    exact checked) (by decide +kernel)

@[expose] def nextRaw : RawDescriptor (Element first) Nat :=
  ⟨8, DensePoly.ofCoeffs #[-generator, 0, 1], .finite 1, .finite 2, [], []⟩

/-- Bind the independently specified higher subject through the same lower
packing inventory. Replaying its construction requests the literal negation,
unit and natural-cast keys instead of running a sign producer in the kernel. -/
@[expose] def requestedRaw (entries : List (Packing first)) : RawDescriptor (Element first) Nat :=
  let negative := (Element.replayNeg (context := first) (inferInstance : Sub Rat) rfl entries).neg generator
  let unit := (Element.replayOne (context := first) (inferInstance : One Rat) rfl entries).one
  let two := (Element.replayNatCast (context := first) (inferInstance : NatCast Rat) rfl entries).natCast 2
  ⟨8, DensePoly.ofCoeffs #[negative, 0, unit], .finite unit, .finite two, [], []⟩

/-- The requested subject is the original native β subject for every inventory. -/
theorem requestedRaw_eq (entries : List (Packing first)) : requestedRaw entries = nextRaw := by
  unfold requestedRaw nextRaw
  rw [Element.replayNeg_eq (inferInstance : Sub Rat) rfl entries,
    Element.replayOne_eq (inferInstance : One Rat) rfl entries,
    Element.replayNatCast_eq (inferInstance : NatCast Rat) rfl entries]
  rfl

/-- Decode the literal base polynomial without invoking a sign producer. -/
@[expose] def readPolynomial? (packet : Codec.Json) : Option (DensePoly Rat) :=
  (Codec.readPoly ValueCodec.rat packet).toOption

/-- Decode the higher subject and graph only from supplied scalar facts;
check all arithmetic and cached signs through their typed record inventories. -/
@[expose] def readNext? (facts : List (SignFact first)) (entries : List (Packing first))
    (signs : List (ValueSign first)) (subject packet : Codec.Json) :
    Option (Descriptor (Element first) Nat Element.sign 8) := do
  let codec := Element.signCodec ValueCodec.rat facts
  let raw ← (SignRequests.readRoot codec ValueCodec.nat subject).toOption
  let graph ← (Codec.readGraph codec ValueCodec.nat 8 raw.head raw.lower raw.upper packet).toOption
  if raw = requestedRaw entries then Descriptor.readPacking? entries signs 8 raw graph
  else none

/-- Every accepted higher root retains the independently specified β subject. -/
theorem readNext?_raw (facts : List (SignFact first)) (entries : List (Packing first))
    (signs : List (ValueSign first)) (subject packet : Codec.Json)
    {root : Descriptor (Element first) Nat Element.sign 8}
    (accepted : readNext? facts entries signs subject packet = some root) :
    root.raw = nextRaw := by
  unfold readNext? at accepted
  dsimp only at accepted
  cases decoded : (SignRequests.readRoot (Element.signCodec ValueCodec.rat facts)
      ValueCodec.nat subject).toOption with
  | none => simp [decoded, bind, Option.bind] at accepted
  | some raw =>
    simp only [decoded, bind, Option.bind] at accepted
    cases graphRead : (Codec.readGraph (Element.signCodec ValueCodec.rat facts)
        ValueCodec.nat 8 raw.head raw.lower raw.upper packet).toOption with
    | none => simp [graphRead, bind, Option.bind] at accepted
    | some graph =>
      simp only [graphRead, bind, Option.bind] at accepted
      split at accepted
      next bound =>
        exact (Descriptor.readPacking_raw entries signs 8 raw graph accepted).trans
          (bound.trans (requestedRaw_eq entries))
      next => simp at accepted

/-- Extract the accepted descriptor without invoking a producer or printing proofs. -/
theorem readNext?_get_raw (facts : List (SignFact first)) (entries : List (Packing first))
    (signs : List (ValueSign first)) (subject packet : Codec.Json)
    (accepted : (readNext? facts entries signs subject packet).isSome = true) :
    ((readNext? facts entries signs subject packet).get accepted).raw = nextRaw :=
  readNext?_raw facts entries signs subject packet (Option.some_get accepted).symm

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.generatorFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms generatorFact

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.firstRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstRoot

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.firstRoot_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstRoot_raw

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.reduction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reduction_eq

end Hex.RealClosure.Algebraic.KernelReplay.FiniteTower

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.requestedRaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.requestedRaw_eq

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.readNext?_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.readNext?_raw

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.readNext?_get_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTower.readNext?_get_raw
