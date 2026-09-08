/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Enumerate
public import HexPermGroupMathlib.Group
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

public section

namespace Hex.PermGroup.Group

/-- The computational rank and unrank functions form an equivalence. -/
@[expose] def rankEquiv (G : Group n) : Element G ≃ Fin G.order where
  toFun := G.rank
  invFun := G.unrank
  left_inv := G.unrank_rank
  right_inv := G.rank_unrank

/-- The same indexing identifies the corresponding Mathlib subgroup. -/
@[expose] def indexEquiv (G : Group n) : Fin G.order ≃ closure G.generators :=
  G.rankEquiv.symm.trans (Element.equiv G).toEquiv

/-- Each output element receives exactly the mass at its unique input index. -/
theorem unrank_probability (G : Group n) (source : PMF (Fin G.order)) (p : Element G) :
    (source.map G.unrank) p = source (G.rank p) := by
  classical
  rw [PMF.map_apply]
  have he (k : Fin G.order) : p = G.unrank k ↔ k = G.rank p := by
    constructor
    · intro h
      rw [h, G.rank_unrank]
    · rintro rfl
      exact (G.unrank_rank p).symm
  simp only [he]
  simp

/-- Conditional uniformity: unranking preserves uniform mass supplied on the
bounded indices. No assumption about a pseudorandom implementation is made. -/
theorem sample_uniform (G : Group n) (source : PMF (Fin G.order))
    (h : ∀ k, source k = (G.order : ENNReal)⁻¹) (p : Element G) :
    (source.map G.unrank) p = (G.order : ENNReal)⁻¹ := by
  rw [unrank_probability, h]

/-- The effect-polymorphic sampling API has the same probability contract when
its index source is a probability mass function. -/
theorem sampleWith_probability
    (draw : (bound : Nat) → 0 < bound → PMF (Fin bound)) (G : Group n) (p : Element G) :
    (sampleWith draw G) p = (draw G.order G.order_pos) (G.rank p) :=
  unrank_probability G (draw G.order G.order_pos) p

/-- Enumerated permutation values are exactly the corresponding subgroup. -/
theorem enumerate_spec (G : Group n) (e : Equiv.Perm (Fin n)) :
    e ∈ G.enumerate.map (fun p => p.val.toEquiv) ↔ e ∈ closure G.generators := by
  constructor
  · intro h
    obtain ⟨p, _, rfl⟩ := Array.mem_map.mp h
    exact generated_iff_mem.mp p.property
  · intro h
    let p : Element G := ⟨Perm.ofEquiv e, generated_iff_mem.mpr (by simpa using h)⟩
    exact Array.mem_map.mpr ⟨p, G.mem_enumerate p, Perm.toEquiv_ofEquiv e⟩

end Hex.PermGroup.Group
