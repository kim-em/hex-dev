/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CanonSpec
public import HexGraphIso.Nauty.Equitable

public section

/-!
The executable and specification target-cell policies agree on equitable
partitions when the executable is not given a history-dependent hint.
-/

namespace Hex.GraphIso.Nauty

/-- On an equitable pair of cells, nauty's representative test agrees with
the specification's count-multiset test. -/
theorem joinTest_iff_first {ctx : Ctx n} {lab ptn : Array Nat} {level : Nat}
    (heq : Equitable ctx level lab ptn) {c d : Nat × Nat}
    (hc : c ∈ cells ptn level n) (hd : d ∈ cells ptn level n) :
    joinTest ctx lab (worksetOf n lab d.1 d.2) c.1 c.2 = true ↔
      ¬ (worksetOf n lab d.1 d.2).interIsEmpty ctx.g[lab[c.1]!]! = true ∧
        ¬ (worksetOf n lab d.1 d.2).subset ctx.g[lab[c.1]!]! = true := by
  have hc_le := cells_le c hc
  have hsplit := heq c hc d hd
  have hlen : 0 < c.2 + 1 - c.1 := by omega
  have hpos :
      (countsOf ctx lab (worksetOf n lab d.1 d.2) c.1 c.2).any
          (fun q => decide (0 < q)) = true ↔
        0 < (worksetOf n lab d.1 d.2).cardInter ctx.g[lab[c.1]!]! := by
    constructor
    · intro h
      obtain ⟨q, hq, hqpos⟩ := List.any_eq_true.mp h
      rcases List.mem_map.mp hq with ⟨o, ho, rfl⟩
      have he := hsplit o 0 (List.mem_range.mp ho) hlen
      simpa [decide_eq_true_eq, he] using hqpos
    · intro h
      refine List.any_eq_true.mpr
        ⟨(worksetOf n lab d.1 d.2).cardInter ctx.g[lab[c.1]!]!, ?_, ?_⟩
      · rw [countsOf]
        exact List.mem_map.mpr ⟨0, List.mem_range.mpr hlen, by simp⟩
      · simpa [decide_eq_true_eq] using h
  have hmiss :
      (countsOf ctx lab (worksetOf n lab d.1 d.2) c.1 c.2).any
          (fun q => decide (q < (worksetOf n lab d.1 d.2).card)) = true ↔
        (worksetOf n lab d.1 d.2).cardInter ctx.g[lab[c.1]!]! <
          (worksetOf n lab d.1 d.2).card := by
    constructor
    · intro h
      obtain ⟨q, hq, hqlt⟩ := List.any_eq_true.mp h
      rcases List.mem_map.mp hq with ⟨o, ho, rfl⟩
      have he := hsplit o 0 (List.mem_range.mp ho) hlen
      simpa [decide_eq_true_eq, he] using hqlt
    · intro h
      refine List.any_eq_true.mpr
        ⟨(worksetOf n lab d.1 d.2).cardInter ctx.g[lab[c.1]!]!, ?_, ?_⟩
      · rw [countsOf]
        exact List.mem_map.mpr ⟨0, List.mem_range.mpr hlen, by simp⟩
      · simpa [decide_eq_true_eq] using h
  have hnonzero :
      0 < (worksetOf n lab d.1 d.2).cardInter ctx.g[lab[c.1]!]! ↔
        ¬ (worksetOf n lab d.1 d.2).interIsEmpty ctx.g[lab[c.1]!]! = true := by
    rw [VSet.cardInter_eq, VSet.interIsEmpty_eq, VSet.isEmpty_iff]
    constructor
    · intro hp hzero
      rw [hzero, VSet.card_empty] at hp
      omega
    · intro hne
      rcases Nat.eq_zero_or_pos ((worksetOf n lab d.1 d.2).inter
          ctx.g[lab[c.1]!]!).card with h0 | h0
      · exact absurd (VSet.eq_empty_of_card_eq_zero h0) hne
      · exact h0
  have hproper :
      (worksetOf n lab d.1 d.2).cardInter ctx.g[lab[c.1]!]! <
          (worksetOf n lab d.1 d.2).card ↔
        ¬ (worksetOf n lab d.1 d.2).subset ctx.g[lab[c.1]!]! = true := by
    rw [VSet.cardInter_eq, VSet.subset_iff_inter]
    have hsub : ((worksetOf n lab d.1 d.2).inter ctx.g[lab[c.1]!]!).subset
        (worksetOf n lab d.1 d.2) = true :=
      VSet.subset_iff.mpr fun v hv => by
        rw [VSet.mem_inter] at hv
        exact ((Bool.and_eq_true _ _).mp hv).1
    have hle := VSet.card_le_of_subset hsub
    constructor
    · intro hlt he
      exact (Nat.ne_of_lt hlt) (congrArg VSet.card he)
    · intro hne
      rcases Nat.lt_or_ge ((worksetOf n lab d.1 d.2).inter ctx.g[lab[c.1]!]!).card
          (worksetOf n lab d.1 d.2).card with hlt | hge
      · exact hlt
      · exact absurd (VSet.eq_of_subset_of_card_eq hsub (by omega)) hne
  rw [joinTest, Bool.and_eq_true, hpos, hmiss, hnonzero, hproper]

/-- Replacing a listed cell's recorded end by `cellEnd` preserves its
membership in the cell list. -/
private theorem start_cell {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {p : Nat × Nat} (hp : p ∈ cells ptn level nn) :
    (p.1, cellEnd ptn level p.1) ∈ cells ptn level nn := by
  have hic := cells_isCell hnn hend p hp
  have hbound := cells_bound hnn hend p hp
  have hle := cells_le p hp
  have hce := cellEnd_of_isCell_start hic (by omega)
  have : cellEnd ptn level p.1 = p.2 := by
    rw [hce]
    omega
  rwa [this]

/-- The executable and specification row counters take the same branches
on an equitable partition. -/
theorem bestcellRow_eq_spec {ctx : Ctx n} {lab ptn : Array Nat}
    {level : Nat} (heq : Equitable ctx level lab ptn)
    (hlab : LabOk lab n) (hlsz : lab.size = n)
    (hpsz : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    {startArr : Array Nat}
    (hstart : ∀ v, v < startArr.size →
      ∃ p ∈ cells ptn level n, startArr[v]! = p.1)
    {v2 : Nat} (hv2 : v2 < startArr.size) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      (∀ v ∈ vs, v < startArr.size) →
      bestcellRow ctx lab startArr
          (worksetOf n lab startArr[v2]!
            (cellEnd ptn level startArr[v2]!)) v2 vs bucket =
        specBestcellRow ctx lab ptn level startArr
          (worksetOf n lab startArr[v2]!
            (cellEnd ptn level startArr[v2]!)) v2 vs bucket
  | [], _, _ => rfl
  | v1 :: rest, bucket, hvs => by
    rw [bestcellRow, specBestcellRow]
    obtain ⟨c, hc, hcstart⟩ := hstart v1 (hvs v1 (by simp))
    obtain ⟨d, hd, hdstart⟩ := hstart v2 hv2
    have hc' := start_cell (by omega : n ≤ ptn.size) hend hc
    have hd' := start_cell (by omega : n ≤ ptn.size) hend hd
    rw [← hcstart] at hc'
    rw [← hdstart] at hd'
    have hj := joinTest_iff_first heq hc' hd'
    rcases hjv : joinTest ctx lab
        (worksetOf n lab startArr[v2]!
          (cellEnd ptn level startArr[v2]!))
        startArr[v1]! (cellEnd ptn level startArr[v1]!) with _ | _
    · have hn : ¬ (¬ (worksetOf n lab startArr[v2]!
          (cellEnd ptn level startArr[v2]!)).interIsEmpty
            ctx.g[lab[startArr[v1]!]!]! = true ∧
          ¬ (worksetOf n lab startArr[v2]!
            (cellEnd ptn level startArr[v2]!)).subset
              ctx.g[lab[startArr[v1]!]!]! = true) := by
        intro h
        have := hj.mpr h
        rw [hjv] at this
        cases this
      simp only [Bool.false_eq_true, ite_false, ite_eq_right hn]
      exact bestcellRow_eq_spec heq hlab hlsz hpsz hend hstart hv2
        rest bucket (fun v hv => hvs v (by simp [hv]))
    · have hy := hj.mp hjv
      simp only [ite_true, ite_eq_left hy]
      exact bestcellRow_eq_spec heq hlab hlsz hpsz hend hstart hv2
        rest _ (fun v hv => hvs v (by simp [hv]))

/-- Folding the row counters over all nonsingleton cells produces the same
bucket on an equitable partition. -/
theorem bestcellRows_eq_spec {ctx : Ctx n} {lab ptn : Array Nat}
    {level : Nat} (heq : Equitable ctx level lab ptn)
    (hlab : LabOk lab n) (hlsz : lab.size = n)
    (hpsz : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    {startArr : Array Nat}
    (hstart : ∀ v, v < startArr.size →
      ∃ p ∈ cells ptn level n, startArr[v]! = p.1) :
    ∀ (vs : List Nat) (bucket : Array Nat),
      (∀ v ∈ vs, v < startArr.size) →
      bestcellRows ctx lab ptn level startArr vs bucket =
        specBestcellRows ctx lab ptn level startArr vs bucket
  | [], _, _ => rfl
  | v2 :: rest, bucket, hvs => by
    rw [bestcellRows, specBestcellRows,
      bestcellRow_eq_spec heq hlab hlsz hpsz hend hstart
        (hvs v2 (by simp)) (List.range v2) bucket
        (fun v hv => by
          have := List.mem_range.mp hv
          have := hvs v2 (by simp)
          omega)]
    exact bestcellRows_eq_spec heq hlab hlsz hpsz hend hstart rest _
      (fun v hv => hvs v (by simp [hv]))

/-- On an equitable partition, nauty's `bestcell` agrees with the
specification's representative-independent form. -/
theorem bestcell_eq_spec {ctx : Ctx n} {lab ptn : Array Nat} {level : Nat}
    (heq : Equitable ctx level lab ptn) (hlab : LabOk lab n)
    (hlsz : lab.size = n) (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    bestcell ctx lab ptn level = specBestcell ctx lab ptn level := by
  rw [bestcell, specBestcell]
  dsimp only
  rcases hnnt : ((((cells ptn level n).filter
      fun (c1, c2) => c1 ≠ c2).map (·.1)).length == 0) with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    have hstart : ∀ v, v < (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).toArray.size →
        ∃ p ∈ cells ptn level n,
          (((cells ptn level n).filter
            fun (c1, c2) => c1 ≠ c2).map (·.1)).toArray[v]! = p.1 := by
      intro v hv
      have hv' : v < (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).length := by
        simpa using hv
      rw [List.getElem!_toArray]
      rw [getElem!_pos
        (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)) v hv']
      have hm := List.getElem_mem hv'
      rcases List.mem_map.mp hm with ⟨p, hp, he⟩
      exact ⟨p, (List.mem_filter.mp hp).1, he.symm⟩
    have hvs : ∀ v ∈ List.range' 1
          ((((cells ptn level n).filter
            fun (c1, c2) => c1 ≠ c2).map (·.1)).length - 1),
        v < (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).toArray.size := by
      intro v hv
      have hr := List.mem_range'_1.mp hv
      have hn0 : (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).length ≠ 0 := by
        simpa using hnnt
      have : v < (((cells ptn level n).filter
          fun (c1, c2) => c1 ≠ c2).map (·.1)).length := by omega
      simpa using this
    rw [bestcellRows_eq_spec heq hlab hlsz hpsz hend hstart _ _ hvs]
  · simp only [ite_true]

/-- If a history-dependent hint is inadmissible, the executable falls
through to the specification's target-cell policy. -/
theorem targetcell_eq_spec_of_inadmissible {ctx : Ctx n}
    {lab ptn : Array Nat}
    {level tcLevel : Nat} (heq : Equitable ctx level lab ptn)
    (hlab : LabOk lab n) (hlsz : lab.size = n)
    (hpsz : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hint : Int)
    (hbad : ¬ (hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧
      (hint == 0 ∨ ptn[hint.toNat - 1]! ≤ level))) :
    targetcell ctx lab ptn level tcLevel hint =
      specTargetcell ctx lab ptn level tcLevel := by
  rw [targetcell, ite_eq_right hbad, specTargetcell]
  rcases Decidable.em (level ≤ tcLevel) with h | h
  · rw [ite_eq_left h, ite_eq_left h]
    exact bestcell_eq_spec heq hlab hlsz hpsz hend
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- With no history-dependent hint, the executable and specification
target-cell choices agree on an equitable partition. -/
theorem targetcell_eq_spec {ctx : Ctx n} {lab ptn : Array Nat}
    {level tcLevel : Nat} (heq : Equitable ctx level lab ptn)
    (hlab : LabOk lab n) (hlsz : lab.size = n)
    (hpsz : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level) :
    targetcell ctx lab ptn level tcLevel (-1) =
      specTargetcell ctx lab ptn level tcLevel := by
  apply targetcell_eq_spec_of_inadmissible heq hlab hlsz hpsz hend
  rintro ⟨h, -⟩
  omega

/-- The complete unhinted target-cell record agrees with the specification
on an equitable partition. -/
theorem maketargetcell_eq_spec {ctx : Ctx n}
    {lab ptn : Array Nat} {level tcLevel : Nat}
    (heq : Equitable ctx level lab ptn) (hlab : LabOk lab n)
    (hlsz : lab.size = n) (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    maketargetcell ctx lab ptn level tcLevel (-1) =
      specMaketargetcell ctx lab ptn level tcLevel := by
  rw [maketargetcell, specMaketargetcell,
    targetcell_eq_spec heq hlab hlsz hpsz hend]

end Hex.GraphIso.Nauty
