/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeComplete
import all HexGraphIso.Nauty.CertAutom
import all HexGraphIso.Nauty.CanonForm

public section

/-!
The root instance of first-path totality.

A total first-path run at the root, with any event trail, identifies the
unpruned specification key with the key the transcription installs.  The
empty graph is certified directly: its single candidate passes the
trusted check without any search.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The corrected first-path root result proves equality between the
unpruned specification key and the key installed by the transcription,
whatever event trail the run reports. -/
theorem keyEq_of_firstRun {G : Colored n k} (hn0 : n ≠ 0)
    {fs : List Nat} {best : Option Key} {eventTrail : FrameTrail}
    (hroot : FirstRun G { n := n, g := rowsOf G } 100 n (n + 2) 1 [] fs
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length best FrameTrail.empty eventTrail
      (firstPathNode { n := n, g := rowsOf G } (n + 2) 100 (n + 2) 1
        (initialPartition G).2.length
        (rootSt n (initialPartition G).1 (initialPartition G).2)).1) :
    canonSpecKey G = tracedKey G := by
  have hread := hroot.proof.node.outcome.event.read
  cases hroot.exit with
  | done returned exact =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | unwind target returned below sound payload located control =>
      cases payload with
      | first anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | canon anchor carrier =>
          exact ((Nat.not_lt_of_ge anchor.positive) below).elim
      | orbit payload =>
          exact ((Nat.not_lt_of_ge payload.positive) below).elim
  | frozen below exact freeze =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | cheap boundary returned positive atOrAbove saved exact =>
      have hinstalled : (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2).canonlevel ≠ 0 :=
        canonlevel_ne_zero_of_stInc (hread.trans exact)
      rw [stInc_final hn0 hinstalled] at hread
      rw [incMax, nodeKey_root hn0] at exact
      exact (Option.some.inj (hread.trans exact)).symm
  | exhausted returned state incumbent emptyFuel => omega

/-- First-path totality at the root fuel yields the key equality. -/
theorem keyEq_of_firstTotal (G : Colored n k) (hn0 : 0 < n)
    (h : FirstTotal G { n := n, g := rowsOf G } (n + 2) 100 (n + 2)) :
    canonSpecKey G = tracedKey G := by
  obtain ⟨fs, outBest, eventTrail, hrun, -⟩ :=
    h n 1 (initialPartition G).2.length []
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      FrameTrail.empty rfl rfl rfl hn0 (Nat.le_refl 1) rfl (by omega)
      (by omega) (Nat.le_refl 1)
      (CheapDesc.same { n := n, g := rowsOf G } 1 _)
      (orbSound_orbConn_init _) (FirstInv.root hn0) PathOk.root
  exact keyEq_of_firstRun (Nat.pos_iff_ne_zero.mp hn0) hrun

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
    · exact colorSortedCheck_canonlab G

end Hex.GraphIso.Nauty
