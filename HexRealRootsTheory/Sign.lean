/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Sign

/-!
# Signs of continuous nonvanishing functions

This file backports the general sign lemmas used by the Sturm development.
-/

public section

variable {α : Type*} [Zero α] [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

/-- The sign of a continuous function is continuous wherever the function is nonzero. -/
theorem ContinuousOn.sign {β : Type*} [TopologicalSpace β] {f : β → α} {s : Set β}
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => SignType.sign (f x)) s := by
  refine (continuousOn_of_forall_continuousAt fun y hy => ?_).comp' hf (Set.mapsTo_image _ _)
  obtain ⟨x, hx, rfl⟩ := hy
  exact continuousAt_sign_of_ne_zero (h0 x hx)

/-- A continuous nonvanishing function has constant sign on a preconnected set. -/
theorem IsPreconnected.sign_eq_of_continuousOn {β : Type*} [TopologicalSpace β] {f : β → α}
    {s : Set β} (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (h0 : ∀ x ∈ s, f x ≠ 0) {x y : β} (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (f x) = SignType.sign (f y) :=
  hs.constant (hf.sign h0) hx hy
