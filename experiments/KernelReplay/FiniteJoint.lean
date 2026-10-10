/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteWitness
public import HexSturmMathlib.Soundness
import all HexPoly.Dense
import all KernelReplay.FiniteData
import all KernelReplay.FiniteTowerProbe
import all HexRealClosure.Algebraic
import all Init.Data.Array.Basic
import all Init.Data.Rat.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteJoint
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret

private theorem closed : Transport.Closed FiniteDataProbe.read (fun _ => True) := by
  refine ⟨trivial, ?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros; simp [FiniteDataProbe.read]

private theorem cast_sign (q : Rat) :
    Sturm.orderSign q = (SignType.sign (FiniteDataProbe.read q) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono q).symm

/-- Only the rational predecessor uses global arithmetic laws. Every original
packing and cached sign is retained in the finite first-level premises. -/
theorem firstData : Packing.Inventory.Data FiniteTower.first
    FiniteTowerProbe.nestedEntries FiniteTowerProbe.nestedSigns [] FiniteDataProbe.read := by
  apply Packing.Inventory.level_data _ _ _ _ _ (fun _ => True) closed
  intro q _
  exact ⟨trivial, (cast_sign q).symm, Rat.cast_eq_zero⟩

private theorem zero : FiniteDataProbe.read 0 = 0 := by simp [FiniteDataProbe.read]
private theorem unit : FiniteDataProbe.read 1 = 1 := by simp [FiniteDataProbe.read]

/-- All first-level records use this one ordinary real point. -/
noncomputable def alpha : ℝ :=
  FiniteTower.first.finitePoint FiniteDataProbe.read zero unit firstData.descriptor

/-- Read the actual stored first-level value at the same point. -/
noncomputable def readAt (a : ℝ) (value : Element FiniteTower.first) : ℝ :=
  Packing.eval FiniteDataProbe.read a value.polynomial

private theorem read_zero : readAt alpha 0 = 0 :=
  FiniteTower.first.finiteRead_zero _ zero unit firstData.descriptor

private theorem unitKey : (Packing.find FiniteTowerProbe.nestedEntries (1 : DensePoly Rat)).isSome = true := by
  decide +kernel

private theorem read_unit : readAt alpha 1 = 1 :=
  FiniteTower.first.finiteRead_one _ zero unit firstData.descriptor
    FiniteTowerProbe.nestedEntries firstData.packings unitKey

@[expose] def next := Context.adjoin FiniteWitness.root (fun _ => false)

/-- The nested descriptor's entire finite transport data comes from its
retained packet and the first point. No algebraic-field reader laws are inputs. -/
theorem nextData : Transport.Finite.DescriptorData (readAt alpha) Element.sign
    (fun x : ℝ => (SignType.sign x : Int)) next.root.raw next.root.evidence := by
  exact Packing.lift_descriptor FiniteTowerProbe.nestedEntries FiniteTowerProbe.nestedSigns
    FiniteDataProbe.read zero unit firstData.descriptor firstData.packings firstData.signs
    FiniteWitness.root.raw FiniteWitness.root.evidence FiniteWitness.root_data

noncomputable def beta : ℝ := next.finitePoint (readAt alpha) read_zero read_unit nextData

/-- One pair of ordinary real coordinates realizes the actual retained finite
conjunction: both selected roots and all first-level packing/sign records. -/
structure Joint (a b : ℝ) : Prop where
  first : a ∈ Tarski.rootsIn
    (interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
      (Transport.polynomial FiniteDataProbe.read FiniteTower.first.root.raw.head))
    ((Transport.endpoint FiniteDataProbe.read FiniteTower.first.root.raw.lower).map (fun y : ℝ => y))
    ((Transport.endpoint FiniteDataProbe.read FiniteTower.first.root.raw.upper).map (fun y : ℝ => y))
  firstSigns : signsAt (fun y : ℝ => y) (fun _ => Iff.rfl)
    (FiniteTower.first.root.raw.queries.map (Transport.polynomial FiniteDataProbe.read)) a =
      FiniteTower.first.root.raw.signs
  packings : ∀ entry ∈ FiniteTowerProbe.nestedEntries,
    Packing.eval FiniteDataProbe.read a entry.value.polynomial =
      Packing.eval FiniteDataProbe.read a entry.original ∧
    (SignType.sign (Packing.eval FiniteDataProbe.read a entry.original) : Int) = entry.value.sign
  signs : ∀ record ∈ FiniteTowerProbe.nestedSigns,
    (SignType.sign (readAt a record.value) : Int) = record.value.sign
  second : b ∈ Tarski.rootsIn
    (interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
      (Transport.polynomial (readAt a) next.root.raw.head))
    ((Transport.endpoint (readAt a) next.root.raw.lower).map (fun y : ℝ => y))
    ((Transport.endpoint (readAt a) next.root.raw.upper).map (fun y : ℝ => y))
  secondSigns : signsAt (fun y : ℝ => y) (fun _ => Iff.rfl)
    (next.root.raw.queries.map (Transport.polynomial (readAt a))) b = next.root.raw.signs

theorem joint : Joint alpha beta := by
  have first := FiniteTower.first.finitePoint_spec _ zero unit firstData.descriptor
  have second := next.finitePoint_spec _ read_zero read_unit nextData
  refine ⟨first.1, first.2, ?_, ?_, second.1, second.2⟩
  · intro entry member
    exact entry.atPoint _ zero unit firstData.descriptor (firstData.packings entry member)
  · intro record member
    exact record.atPoint _ zero unit firstData.descriptor (firstData.signs record member)

/-- The coordinates and coefficient reader are conclusions of the retained
checked finite data, with no supplied real sign-agreement assumption. -/
theorem exists_joint : ∃ a b : ℝ, Joint a b := ⟨alpha, beta, joint⟩

end Hex.RealClosure.Algebraic.KernelReplay.FiniteJoint

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteJoint.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteJoint.exists_joint
