/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Counts
public import HexSignDet.Replay

public section

/-! Support induction for the actual replay tree, conditional only on finite
moment interpretation. The companion must derive that interpretation from the
shared query soundness bridge and root/sign semantics; it is not assumed by
the executable checker and is not a replacement for that bridge. -/
namespace Hex.SignDet

/-- A finite family of length-`arity` ternary observations, with multiplicity. -/
@[expose] def Observations (arity : Nat) (xs : List (List Int)) : Prop :=
  ∀ x ∈ xs, x.length = arity ∧ ∀ v ∈ x, v = -1 ∨ v = 0 ∨ v = 1

theorem Observations.take {arity : Nat} {xs : List (List Int)}
    (h : Observations arity xs) (k : Nat) :
    Observations (min k arity) (xs.map (List.take k)) := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact ⟨by simp [(h y hy).1], fun v hv => (h y hy).2 v (List.mem_of_mem_take hv)⟩

theorem Observations.drop {arity : Nat} {xs : List (List Int)}
    (h : Observations arity xs) (k : Nat) :
    Observations (arity - k) (xs.map (List.drop k)) := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact ⟨by simp [(h y hy).1], fun v hv => (h y hy).2 v (List.mem_of_mem_drop hv)⟩

private theorem leaf_covers {arity : Nat} {xs : List (List Int)}
    (h : Observations arity xs) (ha : arity ≤ 1) :
    ∀ x ∈ xs, x ∈ leafColumns arity := by
  intro x hx
  obtain ⟨hl, hs⟩ := h x hx
  cases x with
  | nil => simp_all [leafColumns]
  | cons v vs =>
    have hv := hs v (by simp)
    have ht : vs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hl; omega)
    subst vs
    have har : arity = 1 := by simpa using hl.symm
    rcases hv with hv | hv | hv <;> simp [leafColumns, har, hv]

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

/-- Every node's literal moment vector interprets the same observations,
restricted at each balanced split. No support or count correctness is a premise. -/
@[expose] def Replay.Interprets (arity : Nat) (xs : List (List Int)) : Replay E Ctx → Prop
  | .leaf n => n.system.values = moments n.system.rows xs
  | .split n l r =>
    n.system.values = moments n.system.rows xs ∧
    l.Interprets (min (arity / 2) arity) (xs.map (List.take (arity / 2))) ∧
    r.Interprets (arity - arity / 2) (xs.map (List.drop (arity / 2)))

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Recursive support completeness and exact counts from finite moment
interpretation. The parent solve is used only after child coverage has proved
that every observation occurs among its Cartesian candidate columns. -/
theorem Replay.support_complete {sign : E → Int} {context : Ctx}
    {p : DensePoly E} {a b : Endpoint E} {qs : List (DensePoly E)}
    {t : Replay E Ctx} {xs : List (List Int)}
    (hc : t.check sign context p a b qs = true)
    (ho : Observations qs.length xs) (hm : t.Interprets qs.length xs) :
    (∀ x ∈ xs, x ∈ t.node.system.support) ∧
    counts t.node.system.columns xs = t.node.system.counts := by
  induction t generalizing qs xs with
  | leaf n =>
    have hn := (Node.check_bindings (Replay.check_node hc)).2
    have hf := hc
    simp only [Replay.check, Bool.and_eq_true, decide_eq_true_eq] at hf
    have cover : ∀ x ∈ xs, x ∈ n.system.columns.toList := by
      rw [hf.1.1.2]
      exact leaf_covers ho hf.1.1.1
    exact ⟨n.system.covers_support hn xs cover hm, n.system.counts_eq hn xs cover hm⟩
  | split n l r ihl ihr =>
    obtain ⟨hl, hr, hp⟩ := Replay.check_children hc
    obtain ⟨hm, hml, hmr⟩ := hm
    have hleft := ihl hl (by simpa only [List.length_take] using ho.take (qs.length / 2))
      (by simpa only [List.length_take] using hml)
    have hright := ihr hr (by simpa only [List.length_drop] using ho.drop (qs.length / 2))
      (by simpa only [List.length_drop] using hmr)
    have cover : ∀ x ∈ xs, x ∈ n.system.columns.toList := by
      intro x hx
      rw [hp, ← List.take_append_drop (qs.length / 2) x]
      exact mem_product (hleft.1 _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
        (hright.1 _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
    have hn := (Node.check_bindings (Replay.check_node hc)).2
    exact ⟨n.system.covers_support hn xs cover hm, n.system.counts_eq hn xs cover hm⟩

/-- The retained support contains precisely the observed conditions. In
particular, every omitted condition has zero multiplicity in the observations. -/
theorem Replay.support_iff {sign : E → Int} {context : Ctx}
    {p : DensePoly E} {a b : Endpoint E} {qs : List (DensePoly E)}
    {t : Replay E Ctx} {xs : List (List Int)}
    (hc : t.check sign context p a b qs = true)
    (ho : Observations qs.length xs) (hm : t.Interprets qs.length xs)
    (x : List Int) : x ∈ t.node.system.support ↔ x ∈ xs := by
  obtain ⟨cover, counts⟩ := t.support_complete hc ho hm
  exact ⟨t.node.system.support_subset xs counts x, cover x⟩

end Hex.SignDet
