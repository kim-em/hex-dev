/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Fixed
public import HexGraphIso.Generated
public import HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- Every graph automorphism stabilizes the initial ordered colour cells.
The raw representation is the same one used by the pruning checker. -/
theorem initial_stab {G : Colored n k} {p : Perm n}
    (hp : IsIso G G p) (hn : 0 < n) :
    CellStab (initPtn n (n + 2) (initialPartition G).2) 1
      (initialPartition G).1 (renamingArray (renamingOf p)) := by
  have hlab := (initial_nodeOk G hn).labOk
  have he : (initialPartition G).1.map
      (fun v => (renamingArray (renamingOf p))[v]!) =
      (initialPartition G).1.map (renamingOf p).toFun :=
    map_congr_of_labOk hlab fun v hv => renamingArray_get _ hv
  change cellsPerm _ _ _ _
  rw [he]
  exact initial_cellsPerm hp hn

/-- A true automorphism fixing the individualized path stabilizes the
current cells in the raw representation used by search pruning. -/
theorem path_stab {G : Colored n k} {st : SearchSt n} {level : Nat}
    (hn : 0 < n)
    (hpath : PathStab { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st)
    {p : Perm n} (hp : IsIso G G p)
    (hfix : ∀ v : Fin n, st.fixedpts.mem v.val = true → p.get v = v) :
    CellStab st.ptn level st.lab (renamingArray (renamingOf p)) := by
  have hcheck := checkAutom_renaming (ctx := { g := rowsOf G })
    (renamingOf p) (rowsMap_of_isIso hp)
  exact hpath _ hcheck (initial_stab hp hn) (fun u hu hm => by
    rw [renamingArray_get _ hu, renamingOf_lt p hu, hfix ⟨u, hu⟩ hm])

/-- Every target cell is invariant under the true point stabilizer of the
current individualized path. -/
theorem window_stable {G : Colored n k} {st : SearchSt n} {level tc len : Nat}
    (hpath : PathStab { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st)
    (hlab : LabOk st.lab n) (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.lab.size)
    {p : Perm n} (hp : IsIso G G p)
    (hfix : ∀ v : Fin n, st.fixedpts.mem v.val = true → p.get v = v)
    (v : Fin n) (hv : (windowSet n st.lab tc len).mem v.val = true) :
    (windowSet n st.lab tc len).mem (p.get v).val = true := by
  have hn : 0 < n := by have := v.isLt; omega
  have h := windowSet_carry (path_stab hn hpath hp hfix) hcell hrange hlab hv
  rwa [renamingArray_get _ v.isLt, renamingOf_lt p v.isLt] at h

/-- At a discrete partition, a cell stabilizer fixes every vertex. -/
theorem discrete_fixes {ptn lab γ : Array Nat} {level : Nat}
    (hstab : CellStab ptn level lab γ)
    (hsize : lab.size = n) (hperm : lab.toList.Perm (List.range n))
    (hptn : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hdisc : discreteAt ptn level n = true) :
    ∀ v, v < n → γ[v]! = v := by
  intro v hv
  have hm := hperm.mem_iff.mpr (List.mem_range.mpr hv)
  obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hm
  have hin : i < n := by simpa [hsize] using hi
  have hv' : lab[i]! = v := by
    rw [getElem!_pos lab i (by omega)]
    exact hiv
  have he := discrete_pointwise hstab (by omega : n ≤ ptn.size) hend hdisc i hin
  rw [getElem!_map_of_lt (fun w => γ[w]!) lab (by omega), hv'] at he
  exact he.symm

/-- The pointwise stabilizer of an individualized path is trivial once
refinement is discrete. This is the terminal case of the stabilizer chain. -/
theorem terminal {G : Colored n k} {st : SearchSt n} {level : Nat}
    (hpath : PathStab { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st)
    (hsize : st.lab.size = n) (hperm : st.lab.toList.Perm (List.range n))
    (hptn : st.ptn.size = n) (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hdisc : discreteAt st.ptn level n = true)
    {p : Perm n} (hp : IsIso G G p)
    (hfix : ∀ v : Fin n, st.fixedpts.mem v.val = true → p.get v = v) :
    p = Perm.id n := by
  apply Perm.ext
  intro v
  have hn : 0 < n := by have := v.isLt; omega
  have hstab := path_stab hn hpath hp hfix
  have he := discrete_fixes hstab hsize hperm hptn hend hdisc v.val v.isLt
  rw [renamingArray_get _ v.isLt, renamingOf_lt p v.isLt] at he
  simpa only [Perm.get_id] using (Fin.ext he : p.get v = v)

end Hex.GraphIso.Nauty.Generation
