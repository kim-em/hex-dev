/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootReplay
public import HexRealClosureTheory.RootOrder
public import HexSignDetTheory.SelectedProducer

public section
namespace Hex.RCF.RealCoefficients.BoundarySigns
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable (model : Model parent ℝ)
variable (root : Descriptor parent.Value Signature parent.sign parent.signature)
variable (point : parent.Value)

/-- A supplied selected sign checks an ordinary point against a boundary root. -/
theorem difference (signs : SelectedSigns root [Isolation.pointQuery point]) :
    signs.value = (SignType.sign
      (root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
        - model.value point) : Int) := by
  rw [signs.value_at_root model.value model.zero_iff model.one model.add model.sub model.mul
    model.nat model.sign,
    Isolation.pointQuery_eval model.value model.zero_iff model.one model.sub]

theorem below (signs : SelectedSigns root [Isolation.pointQuery point]) (observed : signs.value = -1) :
    root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
      < model.value point := by
  have code := difference model root point signs
  rw [observed] at code
  have negative : SignType.sign
      (root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
        - model.value point) = -1 := by
    generalize h : SignType.sign (root.root model.value model.zero_iff model.one model.add
      model.sub model.mul model.nat model.sign - model.value point) = s at code ⊢
    cases s with
    | neg => rfl
    | zero => norm_num at code
    | pos => norm_num at code
  exact sub_neg.mp (sign_eq_neg_one_iff.mp negative)

theorem above (signs : SelectedSigns root [Isolation.pointQuery point]) (observed : signs.value = 1) :
    model.value point <
      root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign := by
  have code := difference model root point signs
  rw [observed] at code
  have positive : SignType.sign
      (root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
        - model.value point) = 1 := by
    generalize h : SignType.sign (root.root model.value model.zero_iff model.one model.add
      model.sub model.mul model.nat model.sign - model.value point) = s at code ⊢
    cases s with
    | neg => norm_num at code
    | zero => norm_num at code
    | pos => rfl
  exact sub_pos.mp (sign_eq_one_iff.mp positive)
/-- A root below the point produces the checked negative boundary sign. -/
theorem left_sign (model : Model parent ℝ)
    (root : Descriptor parent.Value Signature parent.sign parent.signature) (point : parent.Value)
    (less : root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
      < model.value point) :
    ∃ signs, root.buildSigns [Isolation.pointQuery point] = .ok signs ∧ signs.value = -1 := by
  obtain ⟨signs, produced⟩ := root.buildSigns_success model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv [Isolation.pointQuery point]
  refine ⟨signs, produced, ?_⟩
  rw [BoundarySigns.difference model root point signs]
  have observed := sign_eq_neg_one_iff.mpr (sub_neg.mpr less)
  rw [observed]
  rfl

/-- A root above the point produces the checked positive boundary sign. -/
theorem right_sign (model : Model parent ℝ)
    (root : Descriptor parent.Value Signature parent.sign parent.signature) (point : parent.Value)
    (less : model.value point < root.root model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign) :
    ∃ signs, root.buildSigns [Isolation.pointQuery point] = .ok signs ∧ signs.value = 1 := by
  obtain ⟨signs, produced⟩ := root.buildSigns_success model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv [Isolation.pointQuery point]
  refine ⟨signs, produced, ?_⟩
  rw [BoundarySigns.difference model root point signs]
  have observed := sign_eq_one_iff.mpr (sub_pos.mpr less)
  rw [observed]
  rfl

end Hex.RCF.RealCoefficients.BoundarySigns
