/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- The saved ancestor's next code is exactly the corresponding prefix
of the emitting node's path, including the root at index zero. -/
theorem NodeInput.frame_prefix {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n} {target : Nat}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents) (ht : target < f.level - 1) :
    ∃ ancestor, parents.frames ctx tcLevel target = some ancestor ∧ ancestor.level ≤ n ∧
      ancestor.codes ++ [ancestor.code ctx] = f.codes.take (target + 1) := by
  have hf := h.frame.length
  have hd := h.frame.depth
  by_cases hz : target = 0
  · subst target
    obtain ⟨p, hp⟩ := h.scope.complete 1 (by omega) (by omega)
    obtain ⟨_, _, hl, hv⟩ := h.scope.valid 1 p hp
    have he := List.prefix_iff_eq_take.mp (h.scope.codes 1 p hp)
    have hlen : (p.loop.codes ctx).length = 1 := by
      have := hv.node.length
      simp only [Loop.codes, List.length_append, List.length_singleton]
      omega
    rw [hlen] at he
    refine ⟨p.loop.node, ?_, hv.node.depth, he⟩
    simp only [Parents.frames, ↓reduceIte, hp, Option.map_some]
  · obtain ⟨p, hp⟩ := h.scope.complete target (by omega) (by omega)
    obtain ⟨_, _, hl, hv⟩ := h.scope.valid target p hp
    have he := List.prefix_iff_eq_take.mp (h.scope.codes target p hp)
    have hlen : (p.loop.codes ctx).length = target := by
      have := hv.node.length
      simp only [Loop.codes, List.length_append, List.length_singleton]
      omega
    rw [hlen] at he
    have hcode := h.scope.code target p hp (by omega)
    refine ⟨p.child ctx tcLevel, ?_, ?_, ?_⟩
    · simp only [Parents.frames, hz, ↓reduceIte, hp, Option.map_some]
    · change p.loop.node.level + 1 ≤ n
      omega
    · change p.loop.codes ctx ++ [(p.child ctx tcLevel).code ctx] = _
      rw [he, hcode, List.take_succ_eq_append_getElem (by omega : target < f.codes.length)]
      rw [getElem!_pos f.codes target (by omega)]

/-- A frozen comparison's universal prefix bound supplies the concrete
ancestor witness expected by the maximum contract. -/
theorem NodeInput.code_witness {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n} {target : Nat}
    {best : Option (Key n)} (h : NodeInput G ctx tcLevel fuel first f bs fs parents)
    (ht : target < f.level - 1)
    (hb : ∀ tail : Key n, Generic.Covers (prefixKey (f.codes.take (target + 1)) tail) best) :
    Witness ctx tcLevel (parents.frames ctx tcLevel) target best := by
  obtain ⟨a, ha, hd, hp⟩ := h.frame_prefix ht
  refine ⟨a, ha, hd, Or.inr ?_⟩
  intro tail
  rw [hp]
  exact hb tail

end Hex.GraphIso.Nauty.Max
