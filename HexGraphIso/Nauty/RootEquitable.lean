/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.EquitableFix
public import HexGraphIso.Nauty.Cert

public section

/-!
The certificate seed for refinement at the root.

`initActive` contains exactly the starts of the initial colour cells.
Consequently every cell is active and the semantic certificate invariant
needed by `refine_equitable` is vacuous at the root.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

private theorem foldActive_mono :
    ∀ (ends : List Nat) (acc : Nat × Nat) (v : Nat),
      elem acc.1 v = true →
      elem ((ends.foldl
        (fun (p : Nat × Nat) e => (insert p.1 p.2, e + 1)) acc).1) v = true
  | [], _, _, h => h
  | _ :: rest, acc, v, h => by
      rw [List.foldl_cons]
      apply foldActive_mono rest _ v
      rw [elem_insert, h]
      rfl

private theorem foldActive_head :
    ∀ (ends : List Nat) (acc : Nat × Nat), ends ≠ [] →
      elem ((ends.foldl
        (fun (p : Nat × Nat) e => (insert p.1 p.2, e + 1)) acc).1)
        acc.2 = true
  | [], _, h => absurd rfl h
  | _ :: rest, acc, _ => by
      rw [List.foldl_cons]
      apply foldActive_mono rest _ acc.2
      rw [elem_insert]
      simp

private theorem foldActive_of_later :
    ∀ (ends : List Nat) (acc : Nat × Nat) (e d : Nat),
      List.Pairwise (· < ·) ends → e ∈ ends → d ∈ ends → e < d →
      elem ((ends.foldl
        (fun (p : Nat × Nat) q => (insert p.1 p.2, q + 1)) acc).1)
        (e + 1) = true
  | [], _, _, _, _, he, _, _ => absurd he (by simp)
  | a :: rest, acc, e, d, hp, he, hd, hed => by
      rw [List.foldl_cons]
      obtain ⟨ha, hr⟩ := List.pairwise_cons.mp hp
      rcases List.mem_cons.mp he with hea | he
      · have hdr : d ∈ rest := by
          rcases List.mem_cons.mp hd with hda | hd
          · rw [hea, hda] at hed
            omega
          · exact hd
        rw [hea]
        exact foldActive_head rest _ (by
          intro hz
          rw [hz] at hdr
          cases hdr)
      · have hdr : d ∈ rest := by
          rcases List.mem_cons.mp hd with hda | hd
          · have hae := ha e he
            omega
          · exact hd
        exact foldActive_of_later rest _ e d hr he hdr hed

/-- If every cell start is marked active, the refinement certificate
invariant holds vacuously. -/
theorem certInv_of_activeCells {ctx : Ctx} {level : Nat}
    {st : RefineSt}
    (hactive : ∀ p ∈ cells st.ptn level ctx.n,
      elem st.active p.1 = true) :
    CertInv ctx level st := by
  intro p hp hinactive
  rw [hactive p hp] at hinactive
  cases hinactive

/-- Every cell in the root ordered partition is initially active. -/
theorem initial_cells_active (G : Colored n k) (hn0 : 0 < n) :
    ∀ p ∈ cells (initPtn n (n + 2) (initialPartition G).2) 1 n,
      elem (initActive (initialPartition G).2) p.1 = true := by
  intro p hp
  have hok := initial_nodeOk G hn0
  have hic := cells_isCell (by rw [hok.ptnSize]; omega) hok.ptnEnd p hp
  obtain ⟨_, hstart, _, _⟩ := hic
  have hlast : n - 1 ∈ (initialPartition G).2 := by
    have hends := initialPartition_snd_eq G
    have htotal := totalOf_classes G
    rw [hends]
    have hm := endsOf_last_mem ((List.range k).map (colorClass G)) 0
      (by omega)
    rw [htotal] at hm
    simpa using hm
  have hendsNe : (initialPartition G).2 ≠ [] := by
    intro he
    rw [he] at hlast
    cases hlast
  rw [initActive]
  rcases Decidable.em (p.1 = 0) with hzero | hzero
  · rw [hzero]
    exact foldActive_head _ _ hendsNe
  · have hstart' :
        (initPtn n (n + 2) (initialPartition G).2)[p.1 - 1]! ≤ 1 :=
      hstart.resolve_left hzero
    have hp0 : 0 < p.1 := by omega
    have hpN : p.1 < n := by
      have hb := cells_bound (nn := n) (by rw [hok.ptnSize]; omega)
        hok.ptnEnd p hp
      have hle := cells_le p hp
      rw [hok.ptnSize] at hb
      omega
    have hmem : p.1 - 1 ∈ (initialPartition G).2 := by
      rw [getElem!_initPtn] at hstart'
      split at hstart'
      · next h => exact h.1
      · split at hstart'
        · omega
        · omega
    have hpair : List.Pairwise (· < ·) (initialPartition G).2 := by
      rw [initialPartition_snd_eq]
      exact endsOf_pairwise _ 0
    have hlt : p.1 - 1 < n - 1 := by omega
    have ha := foldActive_of_later _ (0, 0) (p.1 - 1) (n - 1) hpair
      hmem hlast hlt
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ p.1)] using ha

/-- The root refinement state has the certificate invariant required by
`refine_equitable`. -/
theorem certInv_initial (G : Colored n k) (hn0 : 0 < n) :
    CertInv { n := n, g := rowsOf G } 1
      { lab := (initialPartition G).1,
        ptn := initPtn n (n + 2) (initialPartition G).2,
        active := initActive (initialPartition G).2,
        numcells := (initialPartition G).2.length,
        hint := 0, maxpos := 0,
        longcode := (initialPartition G).2.length } :=
  certInv_of_activeCells (initial_cells_active G hn0)

end Hex.GraphIso.Nauty
