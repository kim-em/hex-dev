/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert.CertStore
public import HexGraphIso.Nauty.Policy.KeyComplete
import all HexGraphIso.Nauty.Cert.CertAutom
import all HexGraphIso.Nauty.Cert.CanonForm
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

private theorem label_ofArray?_isSome {lab : Array Nat}
    (hsz : lab.size = n)
    (hperm : lab.toList.Perm (List.range n)) :
    ∃ l, Label.ofArray? n lab = some l := by
  have hbound : ∀ v ∈ lab, v < n := by
    intro v hv
    have hm : v ∈ lab.toList := by simpa using hv
    exact List.mem_range.mp (hperm.mem_iff.mp hm)
  have hmapval : ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)).toList.map
      Fin.val) = lab.toList := by
    refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
    rw [List.getElem_map, Array.getElem_toList, Array.getElem_map,
      Array.getElem_attach]
    exact (Array.getElem_toList _).symm
  have hnodupv : ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList.Nodup := by
    have hmv : (((lab.attach.map fun v =>
        (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
        Array (Fin n)).toList.map Fin.val).Nodup := by
      rw [hmapval]
      exact hperm.symm.nodup List.nodup_range
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hmv
    rw [List.nodup_iff_pairwise_ne]
    exact hmv.imp fun h he => h (congrArg Fin.val he)
  have hcompl : ∀ i : Fin n, i ∈ ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList := by
    intro i
    have hm : i.val ∈ lab.toList :=
      hperm.mem_iff.mpr (List.mem_range.mpr i.isLt)
    rw [← hmapval] at hm
    rcases List.mem_map.mp hm with ⟨x, hx, hxe⟩
    exact (Fin.eq_of_val_eq hxe : x = i) ▸ hx
  rw [Label.ofArray?,
    dite_eq_left (⟨hsz, hbound⟩ : lab.size = n ∧ ∀ v ∈ lab, v < n)]
  rw [Label.ofVector?, Perm.ofVector?]
  rw [dite_eq_left ⟨hnodupv, hcompl⟩]
  exact ⟨_, rfl⟩

/-- The empty graph is certified without any search. -/
theorem certifyCanon?_isSome_zero (G : Colored 0 k) :
    (certifyCanon? G).isSome := by
  rw [certifyCanon?]
  rw [ite_eq_left (by rfl)]
  obtain ⟨l, hl⟩ := label_ofArray?_isSome (canonlab_size G)
    (canonlab_perm_range G)
  dsimp only
  rw [checkCanon.eq_def, hl]
  dsimp only
  rw [ite_eq_left ?_]
  · rfl
  · refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
      ⟨?_, ?_⟩, ?_⟩
    · rfl
    · refine beq_iff_eq.mpr ?_
      rw [leafRows]
      rfl
    · exact labelColorSorted_canonlab G

/-- The certified canonicalization always succeeds. -/
theorem certifyCanon?_isSome (G : Colored n k) : (certifyCanon? G).isSome := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    exact certifyCanon?_isSome_zero G
  · exact certifyCanon?_isSome_of_keyEq G (canonSpecKey_eq_tracedKey G hn0)

/-! # Total certificate-checked canonicalization -/

/-- Certificate-checked canonicalization: the search's
answer, accepted through the single trusted `checkCanon` replay, which
always succeeds. -/
@[expose] def certifyCanon (G : Colored n k) : CanonResult n k :=
  (certifyCanon? G).get (certifyCanon?_isSome G)

theorem certifyCanon?_eq (G : Colored n k) :
    certifyCanon? G = some (certifyCanon G) :=
  (Option.some_get (certifyCanon?_isSome G)).symm

theorem certifyCanon_form (G : Colored n k) :
    (certifyCanon G).form = specCanon G := by
  have h := certifyCanon?_eq G
  rw [certifyCanon?] at h
  split at h
  · cases h
  · exact checkCanon_form h

theorem certifyCanon_relabel (G : Colored n k) :
    G.relabel (certifyCanon G).label = (certifyCanon G).form := by
  have h := certifyCanon?_eq G
  rw [certifyCanon?] at h
  split at h
  · cases h
  · exact (checkCanon_sound h).2.1.symm

/-- The search agrees with the certificate-checked answer on
every input. -/
theorem searchResult?_eq (G : Colored n k) :
    searchResult? G = some (certifyCanon G) :=
  searchResult?_eq_of_certifyCanon (certifyCanon?_eq G)

/-- The search always answers. -/
theorem searchResult?_isSome (G : Colored n k) :
    (searchResult? G).isSome := by
  rw [searchResult?_eq]
  rfl

end Hex.GraphIso.Nauty
