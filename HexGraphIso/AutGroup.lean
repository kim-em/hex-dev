/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Autos
public import HexGraphIso.Generated
public import HexGraphIso.Nauty.Invariant.OrbitComplete
import all HexGraphIso.Autos
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Invariant.OrbitComplete

public section

namespace Hex.GraphIso

variable {n k : Nat}

namespace Aut

/-- Each checked raw array represents an element of the returned list. -/
theorem raw_mem {G : Colored n k} {γ : Array Nat} (h : γ ∈ raw G) :
    ∃ p ∈ gens G, ∀ i : Fin n, (p.get i).val = γ[i.val]! := by
  rw [raw, List.mem_map] at h
  obtain ⟨⟨δ, p⟩, hmem, rfl⟩ := h
  refine ⟨p, List.mem_map.mpr ⟨(δ, p), hmem, rfl⟩, ?_⟩
  rw [checked, List.mem_filterMap] at hmem
  obtain ⟨γ, _, hγ⟩ := hmem
  cases hp : autom? G γ with
  | none => simp [hp] at hγ
  | some q =>
    simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hγ
    obtain ⟨rfl, rfl⟩ := hγ
    exact autom?_val_get hp

theorem generated_isIso {G : Colored n k} {p : Perm n}
    (h : Perm.Generated (gens G) p) : IsIso G G p :=
  h.isIso (fun _ => gens_isIso)

/-- A forward word in the checked raw arrays is a generated permutation,
with the same action on every vertex. -/
theorem generated_word {G : Colored n k} :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ raw G) →
      ∃ p, Perm.Generated (gens G) p ∧
        ∀ v : Fin n, (p.get v).val = Nauty.applyWord w v.val
  | [], _ => ⟨Perm.id n, .id, fun v => by simp [Nauty.applyWord]⟩
  | γ :: w, hw => by
    obtain ⟨p, hp, hval⟩ := raw_mem (hw γ (List.mem_cons_self ..))
    obtain ⟨q, hq, hqval⟩ := generated_word w
      (fun δ hδ => hw δ (List.mem_cons_of_mem _ hδ))
    refine ⟨q.comp p, hq.comp (.mem hp), fun v => ?_⟩
    rw [Perm.get_comp, hqval, hval]
    rfl

/-- The search's word connectivity supplies subgroup membership, not just
an arbitrary automorphism carrying the vertex. -/
theorem generated_of_wordConn {G : Colored n k} {u v : Fin n}
    (h : Nauty.WordConn (raw G) u.val v.val) :
    ∃ p, Perm.Generated (gens G) p ∧ p.get u = v := by
  obtain ⟨w, hw, happ⟩ := h
  obtain ⟨p, hp, hval⟩ := generated_word w hw
  exact ⟨p, hp, Fin.ext ((hval u).trans happ)⟩

/-- The recorded representative is reached inside the generated subgroup. -/
theorem generated_orbits (G : Colored n k) (v : Fin n) :
    ∃ p, Perm.Generated (gens G) p ∧
      (p.get v).val = (orbits G)[v.val]! := by
  have h := (Nauty.orbConn_of_ptr (orbSound G) v.isLt).2
  obtain ⟨p, hp, hv⟩ := generated_of_wordConn
    (v := ⟨(orbits G)[v.val]!, orbits_lt G v.isLt⟩) h
  exact ⟨p, hp, congrArg Fin.val hv⟩

/-- Equal recorded representatives give an element of the generated subgroup
carrying one vertex to the other. -/
theorem generated_of_orbits_eq {G : Colored n k} {u v : Fin n}
    (h : (orbits G)[u.val]! = (orbits G)[v.val]!) :
    ∃ p, Perm.Generated (gens G) p ∧ p.get u = v := by
  obtain ⟨p, hp, hu⟩ := generated_orbits G u
  obtain ⟨q, hq, hv⟩ := generated_orbits G v
  refine ⟨q.inv.comp p, hq.inv.comp hp, ?_⟩
  have heq : p.get u = q.get v := Fin.ext (hu.trans (h.trans hv.symm))
  rw [Perm.get_comp, heq, Perm.inv_get_get]

/-- Every returned generator has its corresponding checked raw array. -/
theorem gens_mem {G : Colored n k} {p : Perm n} (h : p ∈ gens G) :
    ∃ γ ∈ raw G, ∀ i : Fin n, (p.get i).val = γ[i.val]! := by
  rw [gens, List.mem_map] at h
  obtain ⟨⟨γ, q⟩, hmem, rfl⟩ := h
  have hraw : γ ∈ raw G := List.mem_map.mpr ⟨(γ, q), hmem, rfl⟩
  refine ⟨γ, hraw, ?_⟩
  rw [checked, List.mem_filterMap] at hmem
  obtain ⟨δ, _, hδ⟩ := hmem
  cases hp : autom? G δ with
  | none => simp [hp] at hδ
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hδ
    obtain ⟨rfl, rfl⟩ := hδ
    exact autom?_val_get hp

theorem orbits_flat (G : Colored n k) :
    Nauty.Orbit.Flat (orbits G) n := by
  apply Nauty.Orbit.flat_fold (raw G) (fun _ => lt_of_mem_raw)
  · exact .ofSound (Nauty.orbSound_orbConn_init (raw G))
  · intro v hv
    have he : (Array.ofFn (n := n) fun i => i.val)[v]! = v := by
      rw [getElem!_pos _ _ (by simpa using hv)]
      simp
    simp only [he]

/-- Every generator edge has equal recorded representatives. -/
theorem orbits_raw {G : Colored n k} {γ : Array Nat} (hγ : γ ∈ raw G)
    {i : Nat} (hi : i < n) : (orbits G)[γ[i]!]! = (orbits G)[i]! := by
  have hs : Nauty.Orbit.Stable (orbits G) n (fun v => (orbits G)[v]!) :=
    orbits_flat G
  exact (Nauty.Orbit.stable_fold (raw G) (fun _ => lt_of_mem_raw) _
    (.ofSound (Nauty.orbSound_orbConn_init (raw G))) hs).2 γ hγ i hi

/-- Recorded representatives are invariant under the entire generated subgroup. -/
theorem orbits_generated {G : Colored n k} {p : Perm n}
    (h : Perm.Generated (gens G) p) (v : Fin n) :
    (orbits G)[(p.get v).val]! = (orbits G)[v.val]! := by
  have hp : ∀ v : Fin n, (orbits G)[(p.get v).val]! = (orbits G)[v.val]! := by
    apply h.induction
    · intro v; simp
    · intro q hq v
      obtain ⟨γ, hγ, hval⟩ := gens_mem hq
      rw [hval]
      exact orbits_raw hγ v.isLt
    · intro q r hq hr v
      rw [Perm.get_comp, hq, hr]
    · intro q hq v
      simpa using (hq (q.inv.get v)).symm
  exact hp v

/-- The orbit array is exactly the orbit partition of the generated subgroup. -/
theorem generated_iff_orbits_eq {G : Colored n k} {u v : Fin n} :
    (∃ p, Perm.Generated (gens G) p ∧ p.get u = v) ↔
      (orbits G)[u.val]! = (orbits G)[v.val]! := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (orbits_generated hp u).symm
  · exact generated_of_orbits_eq

end Aut

end Hex.GraphIso
