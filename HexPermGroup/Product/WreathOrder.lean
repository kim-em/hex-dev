/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.WreathMaps
public import HexPermGroup.Enumerate
public import HexPermGroup.Group.Trivial

public section

namespace Hex.PermGroup.WreathProduct

/-- Lists of functions are used only in the erased cardinality proof. The
constructor generates block copies directly and never enumerates these lists. -/
private def tuples (G : Group n) : (m : Nat) → List (Fin m → Element G)
  | 0 => [Fin.elim0]
  | m + 1 => G.enumerate.toList.flatMap fun p => (tuples G m).map (Fin.cases p)

private theorem cases_injective {α : Type} {p q : α} {f g : Fin m → α}
    (h : (Fin.cases p f : Fin (m + 1) → α) = Fin.cases q g) : p = q ∧ f = g := by
  refine ⟨by simpa using congrFun h 0, ?_⟩
  funext j
  simpa using congrFun h j.succ

private theorem tuples_nodup (G : Group n) (m : Nat) : (tuples G m).Nodup := by
  induction m with
  | zero => simp [tuples]
  | succ m ih =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro p _
      apply List.pairwise_map.mpr
      apply ih.imp
      intro f g hne he
      exact hne (cases_injective he).2
    · apply G.enumerate_nodup.imp
      intro p q hne f hf g hg he
      obtain ⟨f', _, rfl⟩ := List.mem_map.mp hf
      obtain ⟨g', _, rfl⟩ := List.mem_map.mp hg
      exact hne (cases_injective he).1

private theorem mem_tuples (G : Group n) (m : Nat) (f : Fin m → Element G) : f ∈ tuples G m := by
  induction m with
  | zero =>
    have he : f = Fin.elim0 := by funext j; exact Fin.elim0 j
    simp [tuples, he]
  | succ m ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, by simpa using G.mem_enumerate _, ?_⟩
    apply List.mem_map.mpr
    refine ⟨fun j => f j.succ, ih _, ?_⟩
    funext j
    exact Fin.cases (by simp) (fun i => by simp) j

private theorem tuples_length (G : Group n) (m : Nat) : (tuples G m).length = G.order ^ m := by
  induction m with
  | zero => simp [tuples]
  | succ m ih =>
    simp [tuples, List.length_flatMap, ih, Group.enumerate_size, List.map_const',
      List.sum_replicate_nat, Nat.pow_succ, Nat.mul_comm]

end Hex.PermGroup.WreathProduct

namespace Hex.PermGroup.Group

/-- The faithful imprimitive action has one independent base factor per
declared block, whether or not the top action is transitive. -/
theorem wreathProduct_order (G : Group n) (H : Group m) (hn : 0 < n) :
    (G.wreathProduct H hn).order = G.order ^ m * H.order := by
  let values := (WreathProduct.tuples G m).flatMap fun f => H.enumerate.toList.map (WreathProduct.pair hn f)
  have hd : values.Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro f _
      apply List.pairwise_map.mpr
      apply H.enumerate_nodup.imp
      intro h k hne he
      exact hne (WreathProduct.pair_injective hn he).2
    · apply (WreathProduct.tuples_nodup G m).imp
      intro f g hne a ha b hb he
      obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', _, rfl⟩ := List.mem_map.mp hb
      exact hne (WreathProduct.pair_injective hn he).1
  have hm (r : Element (G.wreathProduct H hn)) : r ∈ values := by
    apply List.mem_flatMap.mpr
    refine ⟨WreathProduct.base hn r, WreathProduct.mem_tuples G m _, ?_⟩
    exact List.mem_map.mpr ⟨WreathProduct.top hn r, by simpa using H.mem_enumerate _, WreathProduct.pair_factors hn r⟩
  have hl : values.length = G.order ^ m * H.order := by
    simp [values, List.length_flatMap, enumerate_size, WreathProduct.tuples_length,
      List.map_const', List.sum_replicate_nat]
  have h₁ := List.nodup_subset_length_le hd (l₂ := (G.wreathProduct H hn).enumerate.toList)
    (fun p _ => by simpa using (G.wreathProduct H hn).mem_enumerate p)
  have h₂ := List.nodup_subset_length_le (G.wreathProduct H hn).enumerate_nodup (l₂ := values) (fun p _ => hm p)
  simp only [Array.length_toList, enumerate_size, hl] at h₁ h₂
  omega

/-- No blocks give the trivial action, including when the base group itself
is nontrivial. The degree-zero top group is necessarily trivial. -/
theorem wreath_zero (G : Group n) (H : Group 0) (hn : 0 < n) : (G.wreathProduct H hn).order = 1 := by
  rw [G.wreathProduct_order H hn, Nat.pow_zero, Nat.one_mul]
  apply H.order_one.mpr
  intro p _
  apply Perm.ext
  intro i
  exact Fin.elim0 i

end Hex.PermGroup.Group
