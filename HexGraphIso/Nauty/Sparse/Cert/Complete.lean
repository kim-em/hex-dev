/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Produce

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std
attribute [local instance] lexOrd

/-- Expanding a sufficiently fueled valid native subtree always produces
an accepted proof of any genuine upper bound. All child premises follow
from the executed refinement, target selection and individualization. -/
theorem produceNode_replays {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} {B : Key n}
    (hp : lab.toList.Perm (List.range n)) (ho : NodeOk n level lab ptn active)
    (hc : numcells = bcount ptn level n) (hl : level ≤ numcells)
    (hf : n < fuel + numcells)
    (hb : ∀ l ∈ specLeaves G tcLevel fuel level lab ptn active numcells, Key.Le (l.key G) B) :
    ∃ a, checkNode G tcLevel fuel level lab ptn active numcells
      (produceNode G tcLevel fuel level lab ptn active numcells B) B = some a := by
  induction fuel generalizing level lab ptn active numcells B with
  | zero => have := bcount_le ptn level n; omega
  | succ fuel ih =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    obtain ⟨hp', ho', hc', hm⟩ := refine_node G level lab ptn active numcells hp ho hc
    change r.lab.toList.Perm (List.range n) at hp'
    change NodeOk n level r.lab r.ptn r.active at ho'
    change r.numcells = bcount r.ptn level n at hc'
    change numcells ≤ r.numcells at hm
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _
      (specLeaves_nonempty G tcLevel (fuel + 1) level lab ptn active numcells hp ho hc hl hf)
    obtain ⟨qs, hqs⟩ := Replay.head_codes hq
    have hbound := hb q hq
    cases B with
    | mk codes H =>
      cases codes with
      | nil =>
        simp only [Key.Le, Key.cmp, SpecLeaf.key, hqs, List.compare_cons_nil,
          Ordering.then, Ordering.isLE] at hbound
        contradiction
      | cons b bs =>
        have hcode : r.longcode ≤ b := Replay.code_le hqs hbound
        rw [produceNode]
        by_cases hlt : compare r.longcode b = .lt
        · refine ⟨false, ?_⟩
          dsimp only [r] at hlt
          simp only [hlt, ite_true, checkNode]
        · dsimp only [r] at hlt
          simp only [hlt, ite_false]
          by_cases hd : discreteAt r.ptn level n = true
          · obtain ⟨l, hparse⟩ := Label.ofArray?_exists hp'
            dsimp only [r] at hd hparse
            have hmem : (⟨[r.longcode, codeSentinel], l⟩ : SpecLeaf n) ∈
                specLeaves G tcLevel (fuel + 1) level lab ptn active numcells := by
              simp only [specLeaves, r, hd, ite_true, hparse, List.mem_singleton]
            obtain ⟨a, ha⟩ := Replay.leaf_exists (hb _ hmem)
            refine ⟨a, ?_⟩
            simpa only [hd, ite_true, checkNode, hparse] using ha
          · have hd' : discreteAt r.ptn level n = false := Bool.eq_false_iff.mpr hd
            have he : r.longcode = b := by
              have hn : ¬r.longcode < b := fun h => hlt (Nat.compare_eq_lt.mpr h)
              omega
            dsimp only [r] at hd' he
            have hcount : bcount r.ptn level n < n := by
              have hbn := bcount_le r.ptn level n
              have hne : bcount r.ptn level n ≠ n := fun h =>
                hd ((discreteAt_iff_bcount ho'.ptnSize.symm ho'.ptnEnd).mpr h)
              omega
            have hend : r.ptn[n - 1]! ≤ level := by simpa only [ho'.ptnSize] using ho'.ptnEnd
            let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
            obtain ⟨ht, hn, hbt⟩ := maketargetcell_valid G r.lab r.ptn level tcLevel (-1)
              hp' ho'.ptnSize hend hcount
            let child := fun o => breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
            let make := fun o => produceNode G tcLevel fuel (level + 1)
              (child o).1 (child o).2.1 (child o).2.2 (r.numcells + 1) ⟨bs, H⟩
            have hchecks : ∃ a, Replay.all (fun co : CertNode × Nat =>
                checkNode G tcLevel fuel (level + 1) (child co.2).1 (child co.2).2.1
                  (child co.2).2.2 (r.numcells + 1) co.1 ⟨bs, H⟩)
                ((List.range t.2.2).map make).zipIdx = some a := by
              apply Replay.all_exists
              intro co hco
              have hpos : co.2 < t.2.2 := by
                simpa only [List.length_map, List.length_range, Nat.zero_add] using
                  List.snd_lt_add_of_mem_zipIdx hco
              have hco' : co.1 = make co.2 := by
                simpa only [Nat.sub_zero, List.getElem_map, List.getElem_range] using
                  List.fst_eq_of_mem_zipIdx hco
              rw [hco']
              obtain ⟨hpc, hoc, hcc, hlc⟩ := breakout_node hp' ho' hc' (by omega) ht hbt hn hpos
              apply ih hpc hoc hcc hlc (by change n < fuel + (r.numcells + 1); omega)
              intro l hlmem
              have hmem : l.prepend r.longcode ∈
                  specLeaves G tcLevel (fuel + 1) level lab ptn active numcells := by
                rw [specLeaves]
                simp only [hd', Bool.false_eq_true, ite_false]
                exact List.mem_flatMap.mpr ⟨co.2, List.mem_range.mpr hpos,
                  List.mem_map.mpr ⟨l, hlmem, rfl⟩⟩
              have hb' := hb _ hmem
              rw [SpecLeaf.prepend_key] at hb'
              have hB : (⟨b :: bs, H⟩ : Key n) = prefixKey [r.longcode] ⟨bs, H⟩ := by
                simp only [prefixKey, List.singleton_append, r, he]
              rw [hB] at hb'
              simpa only [Key.Le, prefixKey_cmp] using hb'
            simpa only [make, child, t, r, hd', Bool.false_eq_true, ite_false,
              checkNode, he, and_self, ite_true, List.length_map, List.length_range] using hchecks

end Hex.GraphIso.Nauty.Sparse
