/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Reference
public import HexGraphIso.Nauty.Correct.Generation.Trace
public import HexGraphIso.AutTrace
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- A matching next refinement code advances the first-reference
comparison, regardless of the canonical-incumbent comparison. -/
theorem match_prep {st : SearchSt n} {level code : Nat}
    (hlevel : st.eqlevFirst = level - 1) (hcode : code = st.firstcode[level]!) :
    (otherNodePrep level code st).eqlevFirst = level := by
  rw [otherNodePrep_eqlevFirst]
  simp only [hlevel, hcode, beq_self_eq_true, and_self, ↓reduceIte]

/-- Recovering a matching ancestor keeps the first-reference comparison
live at precisely that ancestor. -/
theorem match_recover {st : SearchSt n} {level inf : Nat}
    (hlevel : level ≤ st.eqlevFirst) :
    (recover n inf level st).eqlevFirst = level := by
  rw [recover_eqlevFirst]
  split <;> omega

/-- A first-reference target hint equal to the specification's choice
cannot demote the first-reference comparison. -/
theorem match_target {ctx : Ctx n} {lab ptn : Array Nat} {level tcLevel : Nat}
    (heq : Equitable ctx level lab ptn) (hlab : LabOk lab n)
    (hlsz : lab.size = n) (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) {hint : Int}
    (hhint : hint = Int.ofNat (specTargetcell ctx lab ptn level tcLevel)) :
    Int.ofNat (maketargetcell ctx lab ptn level tcLevel hint).1 = hint := by
  change Int.ofNat (targetcell ctx lab ptn level tcLevel hint) = hint
  by_cases hadmit : hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧
      ((hint == 0) = true ∨ ptn[hint.toNat - 1]! ≤ level)
  · rw [targetcell, ite_eq_left hadmit, hhint]
    simp
  · rw [targetcell_eq_spec_of_inadmissible heq hlab hlsz hpsz hend hint hadmit, hhint]

/-- The row checker implies the executable automorphism scan. -/
theorem isautom_of_checked {ctx : Ctx n} {γ : Array Nat}
    (hsize : ctx.g.size = n) (h : checkAutom ctx.g γ = true) :
    isautom ctx γ = true := by
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound hsize h
  apply (isautom_iff ctx γ).mpr
  intro i hi j hj _
  have hm := VSet.mem_toList.mp hj
  have hjn := VSet.mem_lt hm
  rw [← hσ i hi, ← hσ j hjn, hrows.2.2 i hi, VSet.mem_image_apply σ _ hjn]
  exact hm

/-- Scattering a permutation labelling onto its renamed copy reconstructs
the renaming's complete array. -/
theorem scatter_renaming {ref : Array Nat} (σ : Renaming n)
    (hsize : ref.size = n) (hperm : ref.toList.Perm (List.range n)) :
    firstScatter n ref (ref.map σ.toFun) = renamingArray σ := by
  have hok : LabOk ref n := fun i hi => by
    have hm := hperm.mem_iff.mp (List.getElem_mem (by simpa using hi))
    simpa only [getElem!_pos ref i hi, Array.getElem_toList] using List.mem_range.mp hm
  have hinj : ∀ a b, a < n → b < n → ref[a]! = ref[b]! → a = b := by
    intro a b ha hb heq
    have hnd := hperm.symm.nodup List.nodup_range
    exact (List.Nodup.getElem_inj hnd (hi := by simpa [hsize] using ha)
      (hj := by simpa [hsize] using hb)).mp (by simpa [getElem!_pos, hsize, ha, hb] using heq)
  apply Array.ext (by rw [firstScatter_size, renamingArray_size])
  intro v hv hv'
  have hvn : v < n := by simpa only [renamingArray_size] using hv'
  obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp
    (hperm.mem_iff.mpr (List.mem_range.mpr hvn))
  have hin : i < n := by simpa [hsize] using hi
  have hat : ref[i]! = v := by
    rw [getElem!_pos ref i (by omega)]
    exact hiv
  have hsc := foldl_scatter_getElem (lab₂ := ref.map σ.toFun) hinj
    (base := Array.replicate n 0) (fun j hj => by simpa using hok j (by omega))
    (Nat.le_refl n) hin
  rw [firstScatter_fold, getElem!_map_of_lt σ.toFun ref (by omega), hat] at hsc
  have he := hsc.trans (renamingArray_get σ hvn).symm
  rw [getElem!_pos (firstScatter n ref (ref.map σ.toFun)) v hv,
    getElem!_pos (renamingArray σ) v hv'] at he
  exact he

/-- Reaching the renamed first-reference leaf emits that exact
permutation, even if the canonical incumbent is strictly greater. -/
theorem match_emits {G : Colored n k} {st : SearchSt n} {level : Nat}
    {p : Perm n} (hp : IsIso G G p)
    (hsize : st.firstlab.size = n)
    (hperm : st.firstlab.toList.Perm (List.range n))
    (hlab : st.lab = st.firstlab.map (renamingOf p).toFun)
    (hlevel : st.eqlevFirst = level)
    (hsent : st.firstcode[level + 1]! = codeSentinel) :
    (processnode { g := rowsOf G } level n st).2.genTrace =
      st.genTrace.push (renamingArray (renamingOf p)) := by
  have hsc : firstScatter n st.firstlab st.lab = renamingArray (renamingOf p) := by
    rw [hlab]
    exact scatter_renaming _ hsize hperm
  have hcheck := checkAutom_renaming (ctx := { g := rowsOf G })
    (renamingOf p) (rowsMap_of_isIso hp)
  have hscan := isautom_of_checked (size_rowsOf G) hcheck
  have he := processnode_genTrace_first (ctx := { g := rowsOf G })
    (st := st) (level := level) (numcells := n) (by simp [hlevel]) hsent (by simp)
    (by rw [firstScatter_fold, hsc]; exact hscan)
  rwa [firstScatter_fold, hsc] at he

end Hex.GraphIso.Nauty.Generation
