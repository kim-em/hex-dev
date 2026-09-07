/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.AutOrder
import all HexGraphIsoMathlib.Encode
import all HexGraphIsoMathlib.Basic
import all HexGraphIsoMathlib.AutGroup
import all HexGraphIso.Generated

public section

namespace Hex.GraphIso.Mathlib

universe u
variable {V : Type u} [Fintype V] {n k : Nat} {G : Colored V k}

@[ext] theorem Colored.Iso.ext {f g : Colored.Iso G G}
    (h : ∀ v, f.graphIso v = g.graphIso v) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := DFunLike.ext _ _ h
      cases he
      rfl

instance : Group (Colored.Iso G G) where
  one := ⟨SimpleGraph.Iso.refl, fun _ => rfl⟩
  mul f g := ⟨g.graphIso.trans f.graphIso, fun v => (f.map_color (g.graphIso v)).trans (g.map_color v)⟩
  inv f := ⟨f.graphIso.symm, fun v => by simpa using (f.map_color (f.graphIso.symm v)).symm⟩
  mul_assoc _ _ _ := Colored.Iso.ext (fun _ => rfl)
  one_mul _ := Colored.Iso.ext (fun _ => rfl)
  mul_one _ := Colored.Iso.ext (fun _ => rfl)
  inv_mul_cancel f := Colored.Iso.ext (fun v => f.graphIso.symm_apply_apply v)

@[simp] theorem Colored.Iso.one_apply (v : V) : (1 : Colored.Iso G G).graphIso v = v := rfl
@[simp] theorem Colored.Iso.mul_apply (f g : Colored.Iso G G) (v : V) :
    (f * g).graphIso v = f.graphIso (g.graphIso v) := rfl
@[simp] theorem Colored.Iso.inv_apply (f : Colored.Iso G G) (v : V) :
    f⁻¹.graphIso v = f.graphIso.symm v := rfl

instance : MulAction (Colored.Iso G G) V where
  smul f := f.graphIso
  one_smul := Colored.Iso.one_apply
  mul_smul := Colored.Iso.mul_apply

/-- Encoding is an isomorphism of full automorphism groups. -/
def autEquiv (e : V ≃ Fin n) (G : Colored V k) [DecidableRel G.graph.Adj] :
    Colored.Iso G G ≃* Aut.group (encode e G) where
  toFun f := ⟨Perm.ofEquiv (e.symm.trans (f.graphIso.toEquiv.trans e)), isIso_of_iso e e f⟩
  invFun p := isoOfIsIso e e p.property
  left_inv f := by
    apply Colored.Iso.ext
    intro v
    change e.symm ((Perm.ofEquiv (e.symm.trans (f.graphIso.toEquiv.trans e))).get (e v)) = f.graphIso v
    simp only [Perm.get_ofEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Perm.ext
    intro v
    simp only [Perm.get_ofEquiv, Equiv.trans_apply, isoOfIsIso, decodePerm_apply,
      Equiv.apply_symm_apply]
  map_mul' f g := by
    apply Subtype.ext
    apply Perm.ext
    intro v
    change (Perm.ofEquiv (e.symm.trans ((f * g).graphIso.toEquiv.trans e))).get v =
      ((Perm.ofEquiv (e.symm.trans (f.graphIso.toEquiv.trans e))) *
        (Perm.ofEquiv (e.symm.trans (g.graphIso.toEquiv.trans e)))).get v
    simp only [Perm.mul_get, Perm.get_ofEquiv, Equiv.trans_apply]
    change e (f.graphIso (g.graphIso (e.symm v))) =
      e (f.graphIso (e.symm (e (g.graphIso (e.symm v)))))
    rw [Equiv.symm_apply_apply]

/-- Every colour-preserving automorphism belongs to the subgroup generated
by the decoded list. -/
theorem autos_complete (e : V ≃ Fin n) (G : Colored V k) [DecidableRel G.graph.Adj]
    (f : Colored.Iso G G) : f ∈ Subgroup.closure {g | g ∈ autos e G} := by
  let C := Subgroup.closure {g | g ∈ autos e G}
  have hdecode (p : Perm n) (hp : Perm.Generated (Aut.gens (encode e G)) p) :
      ∀ hi : IsIso (encode e G) (encode e G) p,
        (autEquiv e G).symm ⟨p, hi⟩ ∈ C := by
    induction hp with
    | id =>
      intro hi
      change (autEquiv e G).symm (1 : Aut.group (encode e G)) ∈ C
      rw [map_one]
      exact C.one_mem
    | @mem p hm =>
      intro hi
      apply Subgroup.subset_closure
      change isoOfIsIso e e hi ∈ (Aut.gens (encode e G)).attach.map _
      exact List.mem_map.mpr ⟨⟨p, hm⟩, List.mem_attach _ _, rfl⟩
    | @comp p q hp hq ihp ihq =>
      intro hi
      have hip := hp.isIso (fun _ hm => Aut.gens_isIso hm)
      have hiq := hq.isIso (fun _ hm => Aut.gens_isIso hm)
      have he : (⟨p.comp q, hi⟩ : Aut.group (encode e G)) =
          ⟨p, hip⟩ * ⟨q, hiq⟩ := Subtype.ext rfl
      rw [he, map_mul]
      exact C.mul_mem (ihp hip) (ihq hiq)
    | @inv p hp ih =>
      intro hi
      have hip := hp.isIso (fun _ hm => Aut.gens_isIso hm)
      have he : (⟨p.inv, hi⟩ : Aut.group (encode e G)) =
          (⟨p, hip⟩ : Aut.group (encode e G))⁻¹ := Subtype.ext rfl
      rw [he, map_inv]
      exact C.inv_mem (ih hip)
  simpa using hdecode _ (Aut.complete (encode e G) (autEquiv e G f).property)
    (autEquiv e G f).property

/-- The reported partition is exactly the full automorphism orbit relation. -/
theorem autos_sameOrbit (e : V ≃ Fin n) (G : Colored V k) [DecidableRel G.graph.Adj]
    (v w : V) :
    (Aut.orbits (encode e G))[(e v).val]! = (Aut.orbits (encode e G))[(e w).val]! ↔
      ∃ f : Colored.Iso G G, f.graphIso v = w := by
  constructor
  · exact sameOrbit_of_autos e G v w
  · rintro ⟨f, hf⟩
    apply (Aut.orbits_eq_iff_sameOrbit (encode e G) (e v) (e w)).mpr
    refine SameOrbit.intro _ (isIso_of_iso e e f) ?_
    simp only [Perm.get_ofEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
    change e (f.graphIso v) = e w
    rw [hf]

/-- Encoding preserves the full automorphism orbit quotient. -/
noncomputable def autOrbitEquiv (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] :
    MulAction.orbitRel.Quotient (Colored.Iso G G) V ≃
      MulAction.orbitRel.Quotient (Aut.group (encode e G)) (Fin n) :=
  Quotient.congr e fun v w => by
    rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, Aut.mem_orbit,
      ← Aut.orbits_eq_iff_sameOrbit, autos_sameOrbit]
    rfl

/-- The reported orbit count equals the cardinality of the Mathlib-facing
full automorphism orbit quotient. -/
theorem autNumOrbits_card (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] :
    autNumOrbits e G = Nat.card (MulAction.orbitRel.Quotient (Colored.Iso G G) V) :=
  (Aut.numOrbits_card (encode e G)).trans (Nat.card_congr (autOrbitEquiv e G)).symm

/-- The reported order equals the cardinality of the Mathlib-facing
colour-preserving automorphism group. -/
theorem autOrder_card (e : V ≃ Fin n) (G : Colored V k) [DecidableRel G.graph.Adj] :
    autOrder e G = Nat.card (Colored.Iso G G) :=
  (Aut.order_card (encode e G)).trans (Nat.card_congr (autEquiv e G).toEquiv).symm

end Hex.GraphIso.Mathlib
