/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert.CanonForm
public import HexGraphIso.Nauty.Policy.PublicResult
public import HexGraphIso.Nauty.Cert.Translator
import all HexGraphIso.Nauty.Cert.CertAutom
import all HexGraphIso.Nauty.Cert.CanonForm

public section

/-!
Totality of the trace-driven candidate producer, and the reduction of
`certifyCanon?` totality to the certificate replay. With no node
budget the producer never exhausts, and its key is read off the
traced run. The transcription-side results discharge every conjunct
of `checkCanon` except the `checkKey` replay. What remains to prove
for `(certifyCanon? G).isSome` is that the replay accepts the
produced certificate against the traced key.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The key of every produced candidate is read off the traced run:
the recorded code chain with the sentinel, and the spec rows of the
traced canonical labelling. -/
theorem produceCand_key {G : Colored n k} {budget : Option Nat}
    {cert : CertNode} {B : Key n}
    (h : produceCand G budget = some (cert, B)) :
    B = ⟨(runColoredTraced G).bestCodes ++ [codeSentinel],
      leafRows { g := rowsOf G }
        (runColoredTraced G).result.canonlab⟩ := by
  rw [produceCand] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h'
      injection h' with h1 h2
      rw [← h2]

/-- A sized permutation array parses as a label. -/
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

/-- The reduction of `certifyCanon?` totality to the certificate
replay: if the produced certificate replays against the traced key,
the transcription-side results discharge every other conjunct of the
single trusted validation, so the certified canonicalization
succeeds. -/
theorem certifyCanon?_isSome_of_checkKey (G : Colored n k)
    (h : ∀ cert B, produceCand G none = some (cert, B) →
      checkKey G cert B = true) :
    (certifyCanon? G).isSome := by
  rw [certifyCanon?]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
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
  · rw [ite_eq_right (by simp; omega)]
    have hps := produceCand_none_isSome G
    rcases hp : produceCand G none with _ | ⟨cert, B⟩
    · rw [hp] at hps
      cases hps
    · dsimp only
      have hkey := h cert B hp
      have hB := produceCand_key hp
      obtain ⟨l, hl⟩ := label_ofArray?_isSome (canonlab_size G)
        (canonlab_perm_range G)
      rw [checkCanon.eq_def, hl]
      dsimp only
      rw [ite_eq_left ?_]
      · rfl
      · refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
          ⟨hkey, ?_⟩, labelColorSorted_canonlab G⟩
        refine beq_iff_eq.mpr ?_
        rw [hB]
        dsimp only
        rw [runColoredTraced_result]

end Hex.GraphIso.Nauty
