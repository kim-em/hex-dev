/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Pair
public import HexGraphIso.Nauty.Invariant.RelCover
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Correct.Generation.Pair
import all HexGraphIso.Nauty.Invariant.Orbits

public section

namespace Hex.GraphIso

variable {n k : Nat}

namespace Aut

/-- The orbit relation for the full pointwise stabilizer of a base. -/
def Orbit (G : Colored n k) (base : List (Fin n)) (u v : Fin n) : Prop :=
  ∃ p, IsIso G G p ∧ Perm.Fixes base p ∧ p.get u = v

namespace Orbit

variable {G : Colored n k} {base : List (Fin n)} {u v w : Fin n}

theorem refl (G : Colored n k) (base : List (Fin n)) (u : Fin n) : Orbit G base u u :=
  ⟨Perm.id n, IsIso.refl G, Perm.Fixes.id base, by simp⟩

theorem trans (h : Orbit G base u v) (h' : Orbit G base v w) : Orbit G base u w := by
  obtain ⟨p, hp, hpf, hpu⟩ := h
  obtain ⟨q, hq, hqf, hqv⟩ := h'
  exact ⟨q.comp p, hp.trans hq, hqf.comp hpf, by simp [hpu, hqv]⟩

theorem symm (h : Orbit G base u v) : Orbit G base v u := by
  obtain ⟨p, hp, hpf, rfl⟩ := h
  exact ⟨p.inv, hp.symm, hpf.inv, by simp⟩

end Orbit

/-- Two vertices are related by a generated automorphism in the pointwise
stabilizer of the given base. Only the resulting permutation must fix the
base; the final generator list need not be a strong generating set. -/
def Carries (G : Colored n k) (base : List (Fin n)) (u v : Fin n) : Prop :=
  ∃ p, Perm.Generated (gens G) p ∧ Perm.Fixes base p ∧ p.get u = v

namespace Carries

variable {G : Colored n k} {base : List (Fin n)} {u v w : Fin n}

theorem refl (G : Colored n k) (base : List (Fin n)) (u : Fin n) : Carries G base u u :=
  ⟨Perm.id n, .id, Perm.Fixes.id base, by simp⟩

theorem trans (h : Carries G base u v) (h' : Carries G base v w) : Carries G base u w := by
  obtain ⟨p, hp, hpf, hpu⟩ := h
  obtain ⟨q, hq, hqf, hqv⟩ := h'
  exact ⟨q.comp p, hq.comp hp, hqf.comp hpf, by simp [hpu, hqv]⟩

theorem symm (h : Carries G base u v) : Carries G base v u := by
  obtain ⟨p, hp, hpf, rfl⟩ := h
  exact ⟨p.inv, hp.inv, hpf.inv, by simp⟩

/-- A generated carrier is in particular a genuine automorphism. -/
theorem witness (h : Carries G base u v) :
    ∃ p, Perm.Generated (gens G) p ∧ IsIso G G p ∧ Perm.Fixes base p ∧ p.get u = v := by
  obtain ⟨p, hp, hfix, hval⟩ := h
  exact ⟨p, hp, generated_isIso hp, hfix, hval⟩

theorem orbit (h : Carries G base u v) : Orbit G base u v := by
  obtain ⟨p, hp, hfix, hval⟩ := h
  exact ⟨p, generated_isIso hp, hfix, hval⟩

end Carries

end Aut

namespace Nauty.Generation

/-- A cell-stabilizing array fixes every vertex in a singleton cell. -/
theorem cellStab_fixes {ptn lab γ : Array Nat} {level pos : Nat}
    (hpos : pos < lab.size) (hcell : IsCell ptn level pos 1)
    (h : CellStab ptn level lab γ) : γ[lab[pos]!]! = lab[pos]! := by
  have he := cellsPerm_singleton h hcell
  rw [getElem!_map_of_lt (fun v => γ[v]!) lab hpos] at he
  exact he.symm

private theorem word_fixes {w : List (Array Nat)} {v : Nat}
    (h : ∀ γ ∈ w, γ[v]! = v) : applyWord w v = v := by
  induction w with
  | nil => rfl
  | cons γ w ih =>
    change applyWord w γ[v]! = v
    rw [h γ (by simp)]
    exact ih (fun δ hδ => h δ (by simp [hδ]))

/-- A word in the final trace gives a generated carrier fixing the base
when its letters stabilize the active frame's singleton base cells. -/
theorem carries_word {G : Colored n k} {base : List (Fin n)} {u v : Fin n}
    {w : List (Array Nat)} (htrace : ∀ γ ∈ w, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ w, ∀ b ∈ base, γ[b.val]! = b.val)
    (hmap : applyWord w u.val = v.val) : Aut.Carries G base u v := by
  obtain ⟨p, hp, hval⟩ := Aut.generated_word (G := G) w
    (fun γ hγ => by rw [Aut.raw_eq_trace]; exact htrace γ hγ)
  refine ⟨p, hp, ?_, Fin.ext ((hval u).trans hmap)⟩
  intro b hb
  exact Fin.ext ((hval b).trans (word_fixes fun γ hγ => hfix γ hγ b hb))

/-- The powers used by an explicit pruning pair fix the active base
whenever its recorded generator does. No converse about the pair's fixed
point bitset is needed. -/
theorem carries_fmperm {G : Colored n k} {base : List (Fin n)} {γ : Array Nat}
    (htrace : γ ∈ Aut.trace G) (hfix : ∀ b ∈ base, γ[b.val]! = b.val)
    {v : Fin n} (hdrop : (fmperm γ n).2.mem v.val = false) :
    ∃ u : Fin n, u.val < v.val ∧ Aut.Carries G base v u := by
  have hraw : γ ∈ Aut.raw G := by rw [Aut.raw_eq_trace]; exact htrace
  obtain ⟨p, hp, hval⟩ := Aut.raw_mem hraw
  have hb : ∀ a, a < n → γ[a]! < n := by
    intro a ha
    rw [← hval ⟨a, ha⟩]
    exact (p.get ⟨a, ha⟩).isLt
  have hi : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
    intro a b ha hb he
    rw [← hval ⟨a, ha⟩, ← hval ⟨b, hb⟩] at he
    exact congrArg Fin.val (p.get_inj (Fin.ext he))
  obtain ⟨t, ht⟩ := fmperm_mcr hb hi v.isLt hdrop
  let u : Fin n := ⟨applyWord (List.replicate t γ) v.val, by omega⟩
  refine ⟨u, ht, carries_word ?_ ?_ rfl⟩
  · intro δ hδ
    rw [List.eq_of_mem_replicate hδ]
    exact htrace
  · intro δ hδ
    rw [List.eq_of_mem_replicate hδ]
    exact hfix

/-- A sound stored orbit pointer is a carrier in the generated stabilizer
when the trace letters fix the active base. -/
theorem carries_pointer {G : Colored n k} {base : List (Fin n)}
    {store : List (Array Nat)} {orbits : Array Nat} {v : Fin n}
    (hsound : OrbSound (OrbConn store n) orbits n)
    (htrace : ∀ γ ∈ store, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ store, ∀ b ∈ base, γ[b.val]! = b.val) :
    ∃ u : Fin n, u.val = orbits[v.val]! ∧ u.val ≤ v.val ∧ Aut.Carries G base v u := by
  obtain ⟨hle, _, hu, w, hw, hmap⟩ := hsound.2 v.val v.isLt
  exact ⟨⟨orbits[v.val]!, hu⟩, rfl, hle,
    carries_word (fun γ hγ => htrace γ (hw γ hγ))
      (fun γ hγ => hfix γ (hw γ hγ)) hmap⟩

/-- Reading the ranked carrier of a pruning pair in the base stabilizer. -/
theorem PairGenerated.carries {G : Colored n k} {base : List (Fin n)}
    {fix mcr : VSet n} (h : PairGenerated G fix mcr)
    (hbase : ∀ b ∈ base, fix.mem b.val = true)
    {v : Fin n} (hv : mcr.mem v.val = false) :
    ∃ u : Fin n, u.val < v.val ∧ Aut.Carries G base v u := by
  obtain ⟨p, hp, _, hfix, hlt⟩ := h v hv
  exact ⟨p.get v, hlt, p, hp, fun b hb => hfix b (hbase b hb), rfl⟩

end Nauty.Generation

end Hex.GraphIso
