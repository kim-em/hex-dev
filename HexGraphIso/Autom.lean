/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Iso
public import HexGraphIso.Nauty.Invariant.Trace
public import HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Perm
import all HexGraphIso.Nauty.Cert.Cert
import all HexGraphIso.Nauty.Invariant.Trace
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso

variable {n k : Nat}

/-- The entries of a checked raw permutation array. -/
theorem Perm.val_get_of_ofNatArray? {a : Array Nat} {p : Perm n}
    (h : Perm.ofNatArray? n a = some p) (i : Fin n) :
    (p.get i).val = a[i.val]! := by
  rw [Perm.ofNatArray?] at h
  split at h
  · rename_i hc
    have hsz : i.val < a.size := hc.1.symm ▸ i.isLt
    rw [Perm.get, Perm.vec_of_ofVector? h]
    rw [getElem!_pos a i.val hsz]
    simp
  · simp at h

/-- Accept one raw generator array from the traversal: rebuild it as a
permutation of `Fin n` and check that it is an automorphism. This is
the only step that admits a generator, and the admission test is
`checkIso`. -/
@[expose] def autom? (G : Colored n k) (γ : Array Nat) : Option (Perm n) :=
  match Perm.ofNatArray? n γ with
  | some p => if checkIso G G p then some p else none
  | none => none

theorem autom?_isIso {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (h : autom? G γ = some p) : IsIso G G p := by
  rw [autom?] at h
  split at h
  · split at h
    · rename_i hchk
      rw [← Option.some.inj h]
      exact (checkIso_iff G G _).mp hchk
    · simp at h
  · simp at h

theorem autom?_val_get {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (h : autom? G γ = some p) (i : Fin n) : (p.get i).val = γ[i.val]! := by
  rw [autom?] at h
  split at h
  · rename_i q hq
    split at h
    · rw [← Option.some.inj h]
      exact Perm.val_get_of_ofNatArray? hq i
    · simp at h
  · simp at h


/-- The checked constructor accepts any correctly sized array representing
a permutation, including the empty permutation. -/
theorem Perm.ofNatArray?_eq {γ : Array Nat} {p : Perm n}
    (hsize : γ.size = n) (hval : ∀ i : Fin n, (p.get i).val = γ[i.val]!) :
    Perm.ofNatArray? n γ = some p := by
  have hvalid : γ.size = n ∧ ∀ i, (hi : i < γ.size) → γ[i] < n := by
    refine ⟨hsize, fun i hi => ?_⟩
    have hv := hval ⟨i, by omega⟩
    rw [getElem!_pos γ i hi] at hv
    exact hv ▸ (p.get ⟨i, by omega⟩).isLt
  rw [Perm.ofNatArray?, dite_eq_left hvalid]
  have heq : (Hex.Vector.ofFn' fun i : Fin n =>
      (⟨γ[i.val]'(hvalid.1.symm ▸ i.isLt),
        hvalid.2 i.val (hvalid.1.symm ▸ i.isLt)⟩ : Fin n)) = p.vec := by
    apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [Hex.Vector.getElem_ofFn']
    have hv := hval ⟨i, hi⟩
    rw [getElem!_pos γ i (by omega)] at hv
    exact hv.symm
  rw [heq, Perm.ofVector?, dite_eq_left ⟨p.nodup, p.complete⟩]

/-- A valid automorphism array passes the public admission filter. -/
theorem autom?_eq {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (hsize : γ.size = n) (hval : ∀ i : Fin n, (p.get i).val = γ[i.val]!)
    (hp : IsIso G G p) : autom? G γ = some p := by
  simp only [autom?, Perm.ofNatArray?_eq hsize hval, (checkIso_iff G G p).mpr hp,
    ↓reduceIte]

namespace Aut

open Nauty

/-- The row checker supplies a typed permutation with exactly the array's
entries. Colour preservation is a separate obligation. -/
theorem checked_perm {G : Colored n k} {γ : Array Nat}
    (h : checkAutom (rowsOf G) γ = true) :
    ∃ p : Perm n, (∀ i : Fin n, (p.get i).val = γ[i.val]!) ∧
      (∀ i j, G.graph.adj (p.get i) (p.get j) = G.graph.adj i j) := by
  have hb := checkAutom_bound h
  have hi := checkAutom_inj h
  have hperm : ((List.range n).map fun i => γ[i]!).Perm (List.range n) := by
    have hh := h
    rw [checkAutom] at hh
    simp only [Bool.and_eq_true] at hh
    exact List.isPerm_iff.mp hh.1.2
  let f (i : Fin n) : Fin n := ⟨γ[i.val]!, hb i.val i.isLt⟩
  have hinj : ∀ i j, f i = f j → i = j := by
    intro i j heq
    exact Fin.ext (hi i.val j.val i.isLt j.isLt (congrArg Fin.val heq))
  have hsurj : ∀ i, ∃ j, f j = i := by
    intro i
    have hm := hperm.mem_iff.mpr (List.mem_range.mpr i.isLt)
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hm
    exact ⟨⟨j, List.mem_range.mp hj⟩, Fin.ext heq⟩
  let p := Perm.ofFn f hinj hsurj
  have hval : ∀ i : Fin n, (p.get i).val = γ[i.val]! := by
    intro i
    simp [p, f]
  refine ⟨p, hval, fun i j => ?_⟩
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound (size_rowsOf G) h
  have hσp : ∀ i : Fin n, σ i.val = (p.get i).val :=
    fun i => (hσ i.val i.isLt).trans (hval i).symm
  have heq := congrArg (fun row : VSet n => row.mem (σ j.val)) (hrows.2.2 i.val i.isLt)
  rw [VSet.mem_image_apply σ _ j.isLt, hσp i, hσp j,
    getElem!_rowsOf G (p.get i).isLt, getElem!_rowsOf G i.isLt,
    mem_rowOf_lt G (p.get i).isLt (p.get j).isLt,
    mem_rowOf_lt G i.isLt j.isLt] at heq
  exact heq

/-- A row-checked array preserving the initial colours passes the public
admission filter. -/
theorem admit {G : Colored n k} {γ : Array Nat}
    (hcheck : checkAutom (rowsOf G) γ = true) (hcolor : ColorMap G γ) :
    ∃ p, autom? G γ = some p := by
  obtain ⟨p, hval, hadj⟩ := checked_perm hcheck
  have hsize : γ.size = n := by
    have hh := hcheck
    rw [checkAutom] at hh
    simp only [Bool.and_eq_true] at hh
    exact beq_iff_eq.mp hh.1.1.1
  refine ⟨p, autom?_eq hsize hval (IsIso.mk ?_ hadj)⟩
  intro v
  obtain ⟨hv, hc⟩ := hcolor v
  have he : p.get v = (⟨γ[v.val]!, hv⟩ : Fin n) := Fin.ext (hval v)
  change G.coloring.cells.get (p.get v) = G.coloring.cells.get v
  rw [he]
  exact hc

/-- A scatter between two reached labellings preserves the initial
colouring, so its row-check certificate passes the public filter. -/
theorem admit_scatter {G : Colored n k} {γ ref cur : Array Nat}
    (hn : 0 < n) (hrefSize : ref.size = n)
    (href : CellsReach G ref) (hcur : CellsReach G cur)
    (hcheck : checkAutom (rowsOf G) γ = true)
    (hmap : ∀ i, i < n → γ[ref[i]!]! = cur[i]!) :
    ∃ p, autom? G γ = some p :=
  admit hcheck (ColorMap.scatter hn hrefSize href hcur hmap)

/-- A root-ledger carrier preserves colours because it stabilizes every
initial colour cell. This includes carriers of implicit pruning pairs. -/
theorem admit_root {G : Colored n k} {γ : Array Nat}
    (hcheck : checkAutom (rowsOf G) γ = true)
    (hstab : CellStab (initPtn n (n + 2) (initialPartition G).2) 1
      (initialPartition G).1 γ) : ∃ p, autom? G γ = some p := by
  apply admit hcheck
  intro v
  have hn : 0 < n := by have := v.isLt; omega
  exact ColorMap.scatter hn (initial_nodeOk G hn).labSize
    (cellsReach_initial G) hstab
    (fun i hi => (getElem!_map_of_lt (fun w => γ[w]!) _
      (by rw [(initial_nodeOk G hn).labSize]; exact hi)).symm) v

end Aut

end Hex.GraphIso
