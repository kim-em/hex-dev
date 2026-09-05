/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable

public section

/-!
The equitability fixpoint theorem (SPEC § Verified search refinement,
the cheapautom clause of the store-validity obligation).

`HexGraphIso.Nauty.Equitable` defines the predicates and proves the
per-pass postconditions; this file proves the active-set and potential
bookkeeping of one refinement step, consumed by
`HexGraphIso.Nauty.EquitableFix` for the fixpoint theorem.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}


/-! # Splitter-set stability across a pass

The pass permutes members within each processed cell, so every cell's
splitter set survives as a bitset. -/

theorem worksetOf_congr_perm {lab lab' : Array Nat} {lo hi : Nat}
    (hp : (segN lab lo (hi + 1 - lo)).Perm (segN lab' lo (hi + 1 - lo))) :
    worksetOf n lab lo hi = worksetOf n lab' lo hi := by
  refine VSet.ext fun v => ?_
  rcases hm : (worksetOf n lab' lo hi).mem v with _ | _
  · rcases hm2 : (worksetOf n lab lo hi).mem v with _ | _
    · rfl
    · obtain ⟨hv, hseg⟩ := mem_worksetOf_iff.mp hm2
      exact absurd (mem_worksetOf_iff.mpr ⟨hv, hp.mem_iff.mp hseg⟩) (by simp [hm])
  · obtain ⟨hv, hseg⟩ := mem_worksetOf_iff.mp hm
    exact mem_worksetOf_iff.mpr ⟨hv, hp.mem_iff.mpr hseg⟩

/-- Pointwise-permuted images have permuted concatenations. -/
private theorem flatMap_perm {α : Type} {f g : α → List Nat} :
    ∀ l : List α, (∀ x ∈ l, (f x).Perm (g x)) →
      (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.Perm.append (h x (List.mem_cons_self ..))
      (flatMap_perm l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- The whole labelling segment is the concatenation of the cell
segments. -/
private theorem segN_flatMap_cells_go {lab ptn : Array Nat}
    {level nn : Nat} (hnn : nn ≤ ptn.size)
    (hendn : ptn[nn - 1]! ≤ level) :
    ∀ fuel c1, nn ≤ c1 + fuel →
      (cells.go ptn level nn fuel c1).flatMap
          (fun p => segN lab p.1 (p.2 + 1 - p.1)) =
        segN lab c1 (nn - c1)
  | 0, c1, hf => by
    rw [cells.go, show nn - c1 = 0 from by omega, segN_zero,
      List.flatMap_nil]
  | fuel + 1, c1, hf => by
    rw [cells.go]
    rcases Decidable.em (c1 < nn) with hc | hc
    · rw [ite_eq_left hc, List.flatMap_cons]
      have hge : c1 ≤ cellEnd ptn level c1 := cellEnd_ge
      have hle : cellEnd ptn level c1 ≤ nn - 1 :=
        cellEnd_le (by omega) hendn (by omega)
      rw [segN_flatMap_cells_go hnn hendn fuel (cellEnd ptn level c1 + 1)
        (by omega),
        show nn - c1 = (cellEnd ptn level c1 + 1 - c1) +
          (nn - (cellEnd ptn level c1 + 1)) from by omega, segN_append,
        show c1 + (cellEnd ptn level c1 + 1 - c1) =
          cellEnd ptn level c1 + 1 from by omega]
    · rw [ite_eq_right hc, show nn - c1 = 0 from by omega, segN_zero,
        List.flatMap_nil]

/-- Cell-contents equivalence permutes the whole labelling segment. -/
theorem cellsPerm_segN_perm {lab lab' ptn : Array Nat} {level nn : Nat}
    (h : cellsPerm ptn level lab lab') (hnn : nn ≤ ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) (hendn : ptn[nn - 1]! ≤ level) :
    (segN lab 0 nn).Perm (segN lab' 0 nn) := by
  have h1 := segN_flatMap_cells_go (lab := lab) hnn hendn nn 0 (by omega)
  have h2 := segN_flatMap_cells_go (lab := lab') hnn hendn nn 0 (by omega)
  rw [Nat.sub_zero] at h1 h2
  rw [← h1, ← h2]
  refine flatMap_perm _ fun p hp => ?_
  exact h p.1 (p.2 + 1 - p.1)
    (cells_isCell hnn hend p (by rw [cells]; exact hp))

/-! # Injective labellings and disjoint cell members

The certificate algebra rests on distinct cells having disjoint
splitter sets, which needs the labelling injective on the vertex
range; injectivity survives a pass because the pass permutes the
whole segment. -/

/-- The labelling is injective on the vertex range. -/
def LabInj (lab : Array Nat) (nn : Nat) : Prop :=
  ∀ i j, i < nn → j < nn → lab[i]! = lab[j]! → i = j

private theorem countP_range_le_one {p : Nat → Bool} {n : Nat}
    (h : ∀ i j, i < n → j < n → p i = true → p j = true → i = j) :
    (List.range n).countP p ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons,
      List.countP_nil]
    rcases hp : p m with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have := ih fun i j hi hj hpi hpj =>
        h i j (by omega) (by omega) hpi hpj
      omega
    · have hz : (List.range m).countP p = 0 := by
        rw [List.countP_eq_zero]
        intro a ha hpa
        have ham := List.mem_range.mp ha
        exact absurd (h a m (by omega) (by omega) hpa hp) (by omega)
      simp [hz]

private theorem two_le_countP_range {p : Nat → Bool} {n i j : Nat}
    (hij : i < j) (hj : j < n) (hpi : p i = true) (hpj : p j = true) :
    2 ≤ (List.range n).countP p := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons,
      List.countP_nil]
    rcases Decidable.em (j = m) with heq | hne
    · have h1 : 0 < (List.range m).countP p :=
        List.countP_pos_iff.mpr ⟨i, List.mem_range.mpr (by omega), hpi⟩
      rw [show p m = true from heq ▸ hpj]
      simp only [ite_true]
      omega
    · have := ih (by omega)
      omega

/-- Injectivity transports across a whole-segment permutation. -/
theorem labInj_of_perm {lab lab' : Array Nat} {nn : Nat}
    (hp : (segN lab' 0 nn).Perm (segN lab 0 nn))
    (h : LabInj lab nn) : LabInj lab' nn := by
  intro i j hi hj he
  rcases Nat.lt_or_ge i j with hlt | hge
  · exfalso
    have h2 : 2 ≤ (segN lab' 0 nn).count lab'[j]! := by
      rw [segN, List.count_eq_countP, List.countP_map]
      refine two_le_countP_range hlt hj ?_ ?_ <;>
        simp only [Function.comp_apply, Nat.zero_add] <;>
        simp [he]
    have h1 : (segN lab 0 nn).count lab'[j]! ≤ 1 := by
      rw [segN, List.count_eq_countP, List.countP_map]
      refine countP_range_le_one fun a b ha hb hpa hpb => ?_
      simp only [Function.comp_apply, Nat.zero_add, beq_iff_eq] at hpa hpb
      exact h a b ha hb (hpa.trans hpb.symm)
    rw [hp.count_eq] at h2
    omega
  · rcases Nat.lt_or_ge j i with hlt | hge2
    · exfalso
      have h2 : 2 ≤ (segN lab' 0 nn).count lab'[i]! := by
        rw [segN, List.count_eq_countP, List.countP_map]
        refine two_le_countP_range hlt hi ?_ ?_ <;>
          simp only [Function.comp_apply, Nat.zero_add] <;>
          simp [he]
      have h1 : (segN lab 0 nn).count lab'[i]! ≤ 1 := by
        rw [segN, List.count_eq_countP, List.countP_map]
        refine countP_range_le_one fun a b ha hb hpa hpb => ?_
        simp only [Function.comp_apply, Nat.zero_add, beq_iff_eq]
          at hpa hpb
        exact h a b ha hb (hpa.trans hpb.symm)
      rw [hp.count_eq] at h2
      omega
    · omega

/-- Under an injective labelling, separated windows have disjoint
members. -/
theorem segments_disjoint_of_labInj {lab : Array Nat}
    {nn a la b lb : Nat} (h : LabInj lab nn) (hab : a + la ≤ b)
    (hbn : b + lb ≤ nn) :
    ∀ v, v ∈ segN lab a la → v ∈ segN lab b lb → False := by
  intro v hva hvb
  obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hva
  obtain ⟨o', ho', he⟩ := mem_segN_iff.mp hvb
  have := h (b + o') (a + o) (by omega) (by omega) he
  omega

/-! # The active union as a membership test -/

private theorem mem_activeUnion_fold {level : Nat} {st : RefineSt n} :
    ∀ (l : List (Nat × Nat)) (A : VSet n) (v : Nat),
      (l.foldl (fun A p => if st.active.mem p.1 then
          A.union (worksetOf n st.lab p.1 p.2) else A) A).mem v =
        (A.mem v || l.any fun p =>
          st.active.mem p.1 && (worksetOf n st.lab p.1 p.2).mem v)
  | [], A, v => by simp
  | x :: l, A, v => by
    rw [List.foldl_cons, List.any_cons]
    rcases hP : st.active.mem x.1 with _ | _
    · rw [ite_eq_right (by simp),
        mem_activeUnion_fold (level := level) l A v]
      simp
    · rw [ite_eq_left (by simp),
        mem_activeUnion_fold (level := level) l _ v, VSet.mem_union]
      simp [Bool.or_assoc]

/-- Membership in the active union: some active cell's splitter set
holds the vertex. -/
theorem mem_activeUnion {level : Nat} {st : RefineSt n} {v : Nat} :
    (activeUnion level st).mem v = true ↔
      ∃ p ∈ cells st.ptn level n, st.active.mem p.1 = true ∧
        (worksetOf n st.lab p.1 p.2).mem v = true := by
  rw [activeUnion,
    mem_activeUnion_fold (level := level) (cells st.ptn level n)
      VSet.empty v,
    VSet.mem_empty, Bool.false_or, List.any_eq_true]
  constructor
  · rintro ⟨p, hp, hpp⟩
    rw [Bool.and_eq_true] at hpp
    exact ⟨p, hp, hpp.1, hpp.2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, by rw [h1, Bool.true_and]; exact h2⟩

/-- An active cell's splitter set lies inside the active union. -/
theorem workset_submask_activeUnion {level : Nat} {st : RefineSt n}
    {p : Nat × Nat} (hp : p ∈ cells st.ptn level n)
    (ha : st.active.mem p.1 = true) :
    (worksetOf n st.lab p.1 p.2).inter (activeUnion level st) =
      worksetOf n st.lab p.1 p.2 :=
  VSet.subset_iff_inter.mp (VSet.subset_iff.mpr fun _ hi =>
    mem_activeUnion.mpr ⟨p, hp, ha, hi⟩)

theorem pairwise_rel_of_mem {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R →
      ∀ a ∈ l, ∀ b ∈ l, a = b ∨ R a b ∨ R b a
  | [], _, a, ha, _, _ => absurd ha (by simp)
  | x :: l, h, a, ha, b, hb => by
    obtain ⟨hx, hl⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha' <;>
      rcases List.mem_cons.mp hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hx b hb'))
    · exact Or.inr (Or.inr (hx a ha'))
    · exact pairwise_rel_of_mem hl a ha' b hb'

/-- Distinct cells of an injective labelling have disjoint splitter
sets. -/
theorem worksetOf_cells_disjoint {level : Nat} {st : RefineSt n}
    (hinj : LabInj st.lab n) (hps : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    {p q : Nat × Nat} (hp : p ∈ cells st.ptn level n)
    (hq : q ∈ cells st.ptn level n) (hne : p ≠ q) :
    (worksetOf n st.lab p.1 p.2).inter (worksetOf n st.lab q.1 q.2) = VSet.empty := by
  have hendn : st.ptn[n - 1]! ≤ level := by
    have h := hend
    rw [hps] at h
    exact h
  have hpb := cells_end_lt_of_end (Nat.le_of_eq hps.symm) hend hendn p hp
  have hqb := cells_end_lt_of_end (Nat.le_of_eq hps.symm) hend hendn q hq
  have hple := cells_le p hp
  have hqle := cells_le q hq
  rcases pairwise_rel_of_mem cells_pairwise p hp q hq with rfl | ho | ho
  · exact absurd rfl hne
  · exact worksetOf_disjoint fun v hv hv' =>
      segments_disjoint_of_labInj hinj (by omega : p.1 + (p.2 + 1 - p.1) ≤ q.1)
        (by omega) v hv hv'
  · have h := worksetOf_disjoint (n := n) (lab := st.lab) (lab' := st.lab)
      (lo := q.1) (hi := q.2) (lo' := p.1) (hi' := p.2)
      fun v hv hv' => segments_disjoint_of_labInj hinj
        (by omega : q.1 + (q.2 + 1 - q.1) ≤ p.1) (by omega) v hv hv'
    rw [VSet.inter_comm]
    exact h

/-- An inactive cell's splitter set misses the active union. -/
theorem inactive_and_activeUnion {level : Nat} {st : RefineSt n}
    (hinj : LabInj st.lab n) (hps : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    {p : Nat × Nat} (hp : p ∈ cells st.ptn level n)
    (ha : st.active.mem p.1 = false) :
    (worksetOf n st.lab p.1 p.2).inter (activeUnion level st) = VSet.empty := by
  refine VSet.ext fun i => ?_
  rw [VSet.mem_inter, VSet.mem_empty]
  rcases h1 : (worksetOf n st.lab p.1 p.2).mem i with _ | _
  · rfl
  · rcases h2 : (activeUnion level st).mem i with _ | _
    · rfl
    · obtain ⟨q, hq, hqa, hqi⟩ := mem_activeUnion.mp h2
      have hne : p ≠ q := fun he => by
        rw [he, hqa] at ha
        cases ha
      have := worksetOf_cells_disjoint hinj hps hend hp hq hne
      have h3 := congrArg (fun x => x.mem i) this
      simp only [VSet.mem_inter, VSet.mem_empty] at h3
      rw [h1, show (worksetOf n st.lab q.1 q.2).mem i = true from hqi]
        at h3
      cases h3

/-! # The trivial pass: active-set effect per processed cell -/

private theorem trivialSplit_active_eq (level cell1 cell2 : Nat)
    (c1 c2 : Int) (st : RefineSt n) :
    (trivialSplit level cell1 cell2 c1 c2 st).active =
      if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
        if st.active.mem cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat then
          st.active.insert c1.toNat
        else
          st.active.insert cell1
      else
        st.active := by
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · rw [ite_eq_left hA, ite_eq_left hA]
    rcases Decidable.em
        (st.active.mem cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · rw [ite_eq_left hB, ite_eq_left hB]
      rcases (c1.toNat == cell2) with _ | _ <;> rfl
    · rw [ite_eq_right hB, ite_eq_right hB]
      rcases (c2.toNat == cell1) with _ | _ <;> rfl
  · rw [ite_eq_right hA, ite_eq_right hA]

private theorem trivialSplit_numcells_eq (level cell1 cell2 : Nat)
    (c1 c2 : Int) (st : RefineSt n) :
    (trivialSplit level cell1 cell2 c1 c2 st).numcells =
      if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
        st.numcells + 1
      else
        st.numcells := by
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · rw [ite_eq_left hA, ite_eq_left hA]
    rcases Decidable.em
        (st.active.mem cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · rw [ite_eq_left hB]
      rcases (c1.toNat == cell2) with _ | _ <;> rfl
    · rw [ite_eq_right hB]
      rcases (c2.toNat == cell1) with _ | _ <;> rfl
  · rw [ite_eq_right hA, ite_eq_right hA]

private theorem trivialSplit_maxpos_eq (level cell1 cell2 : Nat)
    (c1 c2 : Int) (st : RefineSt n) :
    (trivialSplit level cell1 cell2 c1 c2 st).maxpos = st.maxpos := by
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · rw [ite_eq_left hA]
    rcases Decidable.em
        (st.active.mem cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · rw [ite_eq_left hB]
      rcases (c1.toNat == cell2) with _ | _ <;> rfl
    · rw [ite_eq_right hB]
      rcases (c2.toNat == cell1) with _ | _ <;> rfl
  · rw [ite_eq_right hA]

/-- One processed cell of the trivial pass, the bookkeeping half:
`maxpos` untouched, and either nothing changes or exactly one junction
boundary is written together with one activation, the activated
position being the junction successor whenever the cell was active. -/
theorem trivialCell_state {level cell1 cell2 : Nat} {gRow : VSet n} {st : RefineSt n}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size) :
    (trivialCell level gRow cell1 cell2 st).maxpos = st.maxpos ∧
    (((trivialCell level gRow cell1 cell2 st).ptn = st.ptn ∧
      (trivialCell level gRow cell1 cell2 st).active = st.active ∧
      (trivialCell level gRow cell1 cell2 st).numcells = st.numcells) ∨
     (∃ j x, cell1 ≤ j ∧ j < cell2 ∧
       (trivialCell level gRow cell1 cell2 st).ptn = st.ptn.set! j level ∧
       (trivialCell level gRow cell1 cell2 st).active =
         st.active.insert x ∧
       (trivialCell level gRow cell1 cell2 st).numcells =
         st.numcells + 1 ∧
       (x = cell1 ∨ x = j + 1) ∧
       (st.active.mem cell1 = true → x = j + 1))) := by
  rcases Decidable.em (cell1 = cell2) with rfl | hne
  · have heq : trivialCell level gRow cell1 cell1 st = st := by
      rw [trivialCell]
      simp
    rw [heq]
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · have heq : trivialCell level gRow cell1 cell2 st =
        trivialSplit level cell1 cell2
          (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
            (Int.ofNat cell1) (Int.ofNat cell2)).2.1
          (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
            (Int.ofNat cell1) (Int.ofNat cell2)).2.2
          { st with lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
              (Int.ofNat cell1) (Int.ofNat cell2)).1 } := by
      rw [trivialCell]
      simp [hne]
    obtain ⟨hp1, hp2, _, _, _, _⟩ := splitCellLoop_spec
      (gRow := gRow) (cell2 + 1 - cell1) (cell2 - cell1 + 2) st.lab
      (Int.ofNat cell1) (Int.ofNat cell2)
      (by simp only [Int.ofNat_eq_natCast]; omega)
      (by
        have : (cell2 : Int) < (st.lab.size : Int) := by
          exact_mod_cast hsz
        simpa using this)
      (by
        rw [show (Int.ofNat cell2 + 1 - Int.ofNat cell1) =
          ((cell2 + 1 - cell1 : Nat) : Int) from by
            simp only [Int.ofNat_eq_natCast]
            omega])
      (by omega)
    obtain ⟨cnt, hcnt⟩ : ∃ c,
        (segN st.lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·) =
          c := ⟨_, rfl⟩
    have hcntle : cnt ≤ cell2 + 1 - cell1 := by
      have := List.countP_le_length
        (l := segN st.lab cell1 (cell2 + 1 - cell1))
        (p := (gRow.mem ·))
      rw [segN_length, hcnt] at this
      exact this
    have htn : (Int.ofNat cell1).toNat = cell1 := rfl
    rw [htn] at hp1 hp2
    rw [hcnt] at hp1 hp2
    rw [heq, trivialSplit_maxpos_eq]
    refine ⟨rfl, ?_⟩
    rw [trivialSplit_active_eq, trivialSplit_numcells_eq,
      trivialSplit_ptn_eq]
    dsimp only
    rw [hp1, hp2]
    rcases Decidable.em (1 ≤ cnt ∧ cnt ≤ cell2 - cell1) with hc | hc
    · have hg : (Int.ofNat cell1 + (cnt : Int) - 1 ≥ Int.ofNat cell1 ∧
          Int.ofNat cell1 + (cnt : Int) ≤ Int.ofNat cell2) := by
        constructor
        · simp only [Int.ofNat_eq_natCast]
          omega
        · simp only [Int.ofNat_eq_natCast]
          omega
      rw [ite_eq_left hg, ite_eq_left hg, ite_eq_left hg]
      have htn2 : (Int.ofNat cell1 + (cnt : Int) - 1).toNat =
          cell1 + cnt - 1 := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have htn3 : (Int.ofNat cell1 + (cnt : Int)).toNat = cell1 + cnt := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [htn2, htn3]
      refine Or.inr ?_
      rcases Decidable.em (st.active.mem cell1 = true ∨
          cell1 + cnt - 1 - cell1 ≥ cell2 - (cell1 + cnt)) with hB | hB
      · exact ⟨cell1 + cnt - 1, cell1 + cnt, by omega, by omega, rfl,
          by rw [ite_eq_left hB], rfl, Or.inr (by omega),
          fun _ => by omega⟩
      · exact ⟨cell1 + cnt - 1, cell1, by omega, by omega, rfl,
          by rw [ite_eq_right hB], rfl, Or.inl rfl,
          fun hact => absurd (Or.inl hact) hB⟩
    · have hg : ¬(Int.ofNat cell1 + (cnt : Int) - 1 ≥ Int.ofNat cell1 ∧
          Int.ofNat cell1 + (cnt : Int) ≤ Int.ofNat cell2) := by
        intro ⟨hg1, hg2⟩
        simp only [Int.ofNat_eq_natCast] at hg1 hg2
        exact hc ⟨by omega, by omega⟩
      rw [ite_eq_right hg, ite_eq_right hg, ite_eq_right hg]
      exact Or.inl ⟨rfl, rfl, rfl⟩

/-- The trivial pass over a window list, the bookkeeping half:
`maxpos` kept, partition and active bits outside the windows kept,
the potential ledger balanced, and per window either nothing or one
junction with one activation. -/
theorem refineTrivial_go_state {level : Nat} {gRow : VSet n} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n),
      (∀ p ∈ cs, p.1 ≤ p.2 ∧ p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      st.ptn.size = st.lab.size →
      st.lab.size = n →
      (refineTrivial.go level gRow cs st).maxpos = st.maxpos ∧
      (∀ u, (∀ p ∈ cs, u < p.1 ∨ p.2 < u) →
        (refineTrivial.go level gRow cs st).active.mem u =
          st.active.mem u) ∧
      (∀ q, (∀ p ∈ cs, q < p.1 ∨ p.2 < q) →
        (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]!) ∧
      (refineTrivial.go level gRow cs st).active.card +
          2 * st.numcells ≤
        st.active.card +
          2 * (refineTrivial.go level gRow cs st).numcells ∧
      st.numcells ≤ (refineTrivial.go level gRow cs st).numcells ∧
      (∀ p ∈ cs,
        ((∀ q, p.1 ≤ q → q ≤ p.2 →
            (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]!) ∧
         (∀ u, p.1 ≤ u → u ≤ p.2 →
            (refineTrivial.go level gRow cs st).active.mem u =
              st.active.mem u)) ∨
        (∃ j x, p.1 ≤ j ∧ j < p.2 ∧
          (refineTrivial.go level gRow cs st).ptn[j]! = level ∧
          (∀ q, p.1 ≤ q → q ≤ p.2 → q ≠ j →
            (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]!) ∧
          (x = p.1 ∨ x = j + 1) ∧
          (st.active.mem p.1 = true → x = j + 1) ∧
          (refineTrivial.go level gRow cs st).active.mem x = true ∧
          (∀ u, p.1 ≤ u → u ≤ p.2 → u ≠ x →
            (refineTrivial.go level gRow cs st).active.mem u =
              st.active.mem u)))
  | [], st, _, _, _, _ => by
    rw [refineTrivial.go]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, by omega, Nat.le_refl _,
      fun p hp => absurd hp (by simp)⟩
  | (c1, c2) :: rest, st, hw, hpw, hlp, hls => by
    rw [refineTrivial.go]
    obtain ⟨h12, hsz⟩ := hw (c1, c2) (List.mem_cons_self ..)
    dsimp only at h12 hsz
    obtain ⟨hsize, _, _⟩ :=
      trivialCell_effect (level := level) (gRow := gRow) (st := st)
        h12 hsz
    obtain ⟨hmax, hdisj⟩ :=
      trivialCell_state (level := level) (gRow := gRow) (st := st)
        h12 hsz
    have hps1 : (trivialCell level gRow c1 c2 st).ptn.size =
        st.ptn.size := by
      rcases hdisj with ⟨he, _, _⟩ | ⟨j, x, _, _, he, _⟩
      · rw [he]
      · rw [he, Array.size_set!]
    have hhead := (List.pairwise_cons.mp hpw).1
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ :=
      refineTrivial_go_state rest
        (trivialCell level gRow c1 c2 st)
        (fun p hp => by
          obtain ⟨hp1, hp2⟩ := hw p (List.mem_cons_of_mem _ hp)
          exact ⟨hp1, by rw [hsize]; exact hp2⟩)
        (List.pairwise_cons.mp hpw).2
        (by rw [hps1, hsize]; exact hlp)
        (by rw [hsize]; exact hls)
    have houtA : ∀ u, u < c1 ∨ c2 < u →
        (trivialCell level gRow c1 c2 st).active.mem u =
          st.active.mem u := by
      intro u hu
      rcases hdisj with ⟨_, he, _⟩ | ⟨j, x, hj1, hj2, _, he, _, hx, _⟩
      · rw [he]
      · rw [he, VSet.mem_insert,
          show (x == u) = false from by
            simp only [beq_eq_false_iff_ne]
            rcases hx with rfl | rfl <;> omega,
          Bool.false_and, Bool.or_false]
    have houtP : ∀ q, q < c1 ∨ c2 < q →
        (trivialCell level gRow c1 c2 st).ptn[q]! = st.ptn[q]! := by
      intro q hq
      rcases hdisj with ⟨he, _, _⟩ | ⟨j, x, hj1, hj2, he, _⟩
      · rw [he]
      · rw [he, Array.getElem!_set!_ne _ _ _ _ (by omega)]
    have hkeepP : ∀ q, q ≤ c2 →
        (refineTrivial.go level gRow rest
          (trivialCell level gRow c1 c2 st)).ptn[q]! =
          (trivialCell level gRow c1 c2 st).ptn[q]! := by
      intro q hq
      exact ih3 q fun pr hpr => Or.inl (by
        have := hhead pr hpr
        simp only at this
        omega)
    have hkeepA : ∀ u, u ≤ c2 →
        (refineTrivial.go level gRow rest
          (trivialCell level gRow c1 c2 st)).active.mem u =
          (trivialCell level gRow c1 c2 st).active.mem u := by
      intro u hu
      exact ih2 u fun pr hpr => Or.inl (by
        have := hhead pr hpr
        simp only at this
        omega)
    refine ⟨ih1.trans hmax, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [ih2 u fun p hp => hu p (List.mem_cons_of_mem _ hp),
        houtA u (by
          have := hu (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · intro q hq
      rw [ih3 q fun pr hpr => hq pr (List.mem_cons_of_mem _ hpr),
        houtP q (by
          have := hq (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · have hcell : (trivialCell level gRow c1 c2 st).active.card +
          2 * st.numcells ≤
            st.active.card +
              2 * (trivialCell level gRow c1 c2 st).numcells := by
        rcases hdisj with ⟨_, he, hn⟩ | ⟨j, x, _, _, _, he, hn, _⟩
        · rw [he, hn]
          exact Nat.le_refl _
        · rw [he]
          have := VSet.card_insert_le st.active x
          omega
      omega
    · have : st.numcells ≤
          (trivialCell level gRow c1 c2 st).numcells := by
        rcases hdisj with ⟨_, _, hn⟩ | ⟨j, x, _, _, _, _, hn, _⟩
        · rw [hn]
          exact Nat.le_refl _
        · rw [hn]
          omega
      omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · rcases hdisj with ⟨heP, heA, _⟩ |
          ⟨j, x, hj1, hj2, heP, heA, _, hx, himp⟩
        · refine Or.inl ⟨?_, ?_⟩
          · intro q hq1 hq2
            rw [hkeepP q hq2, heP]
          · intro u hu1 hu2
            rw [hkeepA u hu2, heA]
        · refine Or.inr ⟨j, x, hj1, hj2, ?_, ?_, hx, himp, ?_, ?_⟩
          · rw [hkeepP j (by omega), heP,
              Array.getElem!_set!_self _ _ _ (by
                rw [hlp]
                omega)]
          · intro q hq1 hq2 hqj
            rw [hkeepP q hq2, heP,
              Array.getElem!_set!_ne _ _ _ _ (by omega)]
          · rw [hkeepA x (by rcases hx with rfl | rfl <;> omega), heA]
            exact VSet.mem_insert_self _ (by rcases hx with rfl | rfl <;> omega)
          · intro u hu1 hu2 hux
            rw [hkeepA u hu2, heA, VSet.mem_insert,
              show (x == u) = false from by
                simp only [beq_eq_false_iff_ne]
                omega,
              Bool.false_and, Bool.or_false]
      · have hout1 : c2 < p.1 := by
          have := hhead p hmem
          simpa using this
        rcases ih6 p hmem with ⟨hP, hA⟩ |
          ⟨j, x, hj1, hj2, hjl, hP, hx, himp, hax, hA⟩
        · refine Or.inl ⟨?_, ?_⟩
          · intro q hq1 hq2
            rw [hP q hq1 hq2, houtP q (Or.inr (by omega))]
          · intro u hu1 hu2
            rw [hA u hu1 hu2, houtA u (Or.inr (by omega))]
        · refine Or.inr ⟨j, x, hj1, hj2, hjl, ?_, hx, ?_, hax, ?_⟩
          · intro q hq1 hq2 hqj
            rw [hP q hq1 hq2 hqj, houtP q (Or.inr (by omega))]
          · intro hact
            exact himp (by
              rw [houtA p.1 (Or.inr (by omega))]
              exact hact)
          · intro u hu1 hu2 hux
            rw [hA u hu1 hu2 hux, houtA u (Or.inr (by omega))]

/-! # The nontrivial pass: active-set effect of the window scan -/

private theorem windowStep_maxpos (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt n) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).maxpos =
      if Int.ofNat (c2 - c1) > maxcell then c1 else st.maxpos := by
  rw [windowStep]
  dsimp only
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, ite_false, ite_true]

/-- The window scan's active-set ledger: bits at or below the cell
start and beyond the cell end are untouched, the active set only
grows, every new bit sits just after a boundary, every boundary the
scan writes gets its successor activated (the successor of the last
write being pending exactly while mass remains), the potential ledger
balances, and the running largest-fragment position stays justified. -/
theorem windowScan_active_state {level cell1 cell2 : Nat}
    {counts : List Nat} (hc2 : cell2 < n) :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n),
      cell1 ≤ c1 →
      c1 + (vs.map (multOf counts)).sum = cell2 + 1 →
      (c1 = cell1 ∨ st.ptn[c1 - 1]! ≤ level ∨ c1 = cell2 + 1) →
      cell2 < st.ptn.size →
      (∀ u, u ≤ cell1 ∨ cell2 < u →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active.mem u = st.active.mem u) ∧
      (∀ u, st.active.mem u = true →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active.mem u = true) ∧
      (∀ q : Nat, st.ptn[q]! ≤ level →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[q]! ≤ level) ∧
      (∀ q : Nat, q < c1 →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[q]! = st.ptn[q]!) ∧
      (∀ u, (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active.mem u = true → st.active.mem u = true ∨
        (cell1 < u ∧ u ≤ cell2 ∧
          (windowScan level cell1 cell2 counts vs c1 maxcell
            st).ptn[u - 1]! ≤ level)) ∧
      (∀ u, c1 < u → u ≤ cell2 →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[u - 1]! ≤ level →
        st.ptn[u - 1]! ≤ level ∨
          (windowScan level cell1 cell2 counts vs c1 maxcell
            st).active.mem u = true) ∧
      (0 < (vs.map (multOf counts)).sum → c1 = cell1 ∨
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active.mem c1 = true) ∧
      ((windowScan level cell1 cell2 counts vs c1 maxcell
          st).active.card + 2 * st.numcells ≤
        st.active.card + 2 * (windowScan level cell1 cell2
          counts vs c1 maxcell st).numcells) ∧
      st.numcells ≤ (windowScan level cell1 cell2 counts vs c1 maxcell
        st).numcells ∧
      ((maxcell < 0 ∨ (cell1 ≤ st.maxpos ∧ st.maxpos ≤ cell2 ∧
          (st.maxpos = cell1 ∨ st.active.mem st.maxpos = true))) →
        (0 < (vs.map (multOf counts)).sum ∨ 0 ≤ maxcell) →
        (cell1 ≤ (windowScan level cell1 cell2 counts vs c1 maxcell
            st).maxpos ∧
         (windowScan level cell1 cell2 counts vs c1 maxcell
            st).maxpos ≤ cell2 ∧
         ((windowScan level cell1 cell2 counts vs c1 maxcell
            st).maxpos = cell1 ∨
          (windowScan level cell1 cell2 counts vs c1 maxcell
            st).active.mem (windowScan level cell1 cell2 counts vs c1
              maxcell st).maxpos = true)))
  | [], c1, maxcell, st, hcw, htot, hbnd, hsz => by
    rw [windowScan]
    refine ⟨fun _ _ => rfl, fun _ h => h, fun _ h => h, fun _ _ => rfl,
      fun u h => Or.inl h, fun u hu1 hu2 h => Or.inl h,
      by simp, by omega, Nat.le_refl _, ?_⟩
    intro hmc hf
    rcases hmc with hmc | hmc
    · rcases hf with hf | hf
      · simp at hf
      · omega
    · exact hmc
  | v :: vs, c1, maxcell, st, hcw, htot, hbnd, hsz => by
    rw [windowScan]
    have hsum : (List.map (multOf counts) (v :: vs)).sum =
        multOf counts v + (List.map (multOf counts) vs).sum := by
      rw [List.map_cons, List.sum_cons]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · rw [ite_eq_left hm]
      obtain ⟨m, hmv⟩ : ∃ m, multOf counts v = m := ⟨_, rfl⟩
      rw [hmv] at hm ⊢
      have hin : c1 + m ≤ cell2 + 1 := by
        rw [hsum, hmv] at htot
        omega
      have hpe := ptn_windowStep_eq level cell1 cell2 v c1 (c1 + m)
        maxcell st
      have hae := active_windowStep_eq level cell1 cell2 v c1 (c1 + m)
        maxcell st
      have hne := nc_windowStep_eq level cell1 cell2 v c1 (c1 + m)
        maxcell st
      have hme := windowStep_maxpos level cell1 cell2 v c1 (c1 + m)
        maxcell st
      obtain ⟨w, hw⟩ : ∃ w, windowStep level cell1 cell2 v c1 (c1 + m)
        maxcell st = w := ⟨_, rfl⟩
      rw [hw] at hpe hae hne hme
      rw [hw]
      have hwps : w.ptn.size = st.ptn.size := by
        rw [hpe]
        rcases Decidable.em (c1 + m ≤ cell2) with h | h
        · rw [ite_eq_left h, Array.size_set!]
        · rw [ite_eq_right h]
      obtain ⟨ih1, ih2, ih3, ihH, ih4, ih5, ih6, ih7, ih8, ih9⟩ :=
        windowScan_active_state (level := level) (cell1 := cell1)
          (cell2 := cell2) (counts := counts) hc2 vs (c1 + m)
          (if Int.ofNat m > maxcell then Int.ofNat m else maxcell) w
          (by omega)
          (by rw [hsum, hmv] at htot; omega)
          (by
            rcases Decidable.em (c1 + m ≤ cell2) with h | h
            · refine Or.inr (Or.inl ?_)
              rw [hpe, ite_eq_left h,
                Array.getElem!_set!_self _ _ _ (by omega)]
              exact Nat.le_refl _
            · refine Or.inr (Or.inr (by omega)))
          (by rw [hwps]; exact hsz)
      have houtA : ∀ u, u ≤ cell1 ∨ cell2 < u →
          w.active.mem u = st.active.mem u := by
        intro u hu
        rw [hae]
        rcases Decidable.em (c1 = cell1) with h | h
        · rw [ite_eq_right (by simp [h])]
        · rw [ite_eq_left (by simp [h]), VSet.mem_insert,
            show (c1 == u) = false from by
              simp only [beq_eq_false_iff_ne]
              omega,
            Bool.false_and, Bool.or_false]
      have hmonoA : ∀ u, st.active.mem u = true →
          w.active.mem u = true := by
        intro u hu
        rw [hae]
        rcases Decidable.em (c1 = cell1) with h | h
        · rw [ite_eq_right (by simp [h])]
          exact hu
        · rw [ite_eq_left (by simp [h]), VSet.mem_insert, hu, Bool.true_or]
      have hpersist : ∀ q : Nat, st.ptn[q]! ≤ level →
          w.ptn[q]! ≤ level := by
        intro q hq
        rw [hpe]
        rcases Decidable.em (c1 + m ≤ cell2) with h | h
        · rw [ite_eq_left h]
          rcases getElem!_set!_cases st.ptn (c1 + m - 1) level q with
            he | he
          · rw [he]
            exact hq
          · rw [he]
            exact Nat.le_refl _
        · rw [ite_eq_right h]
          exact hq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rw [ih1 u hu, houtA u hu]
      · intro u hu
        exact ih2 u (hmonoA u hu)
      · intro q hq
        exact ih3 q (hpersist q hq)
      · intro q hq
        rw [ihH q (by omega), hpe]
        rcases Decidable.em (c1 + m ≤ cell2) with h | h
        · rw [ite_eq_left h,
            Array.getElem!_set!_ne _ _ _ _ (by omega)]
        · rw [ite_eq_right h]
      · intro u hu
        rcases ih4 u hu with h | h
        · rw [hae] at h
          rcases Decidable.em (c1 = cell1) with hc | hc
          · rw [ite_eq_right (by simp [hc])] at h
            exact Or.inl h
          · rw [ite_eq_left (by simp [hc]), VSet.mem_insert] at h
            rcases hb2 : st.active.mem u with _ | _
            · rw [hb2, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨h, _⟩ := h
              subst h
              refine Or.inr ⟨by omega, by omega, ?_⟩
              rcases hbnd with hb | hb | hb
              · exact absurd hb hc
              · exact ih3 _ (hpersist _ hb)
              · omega
            · exact Or.inl rfl
        · exact Or.inr h
      · intro u hu1 hu2 hb
        rcases Decidable.em (c1 + m < u) with hgt | hgt
        · rcases ih5 u hgt hu2 hb with h | h
          · rw [hpe] at h
            rcases Decidable.em (c1 + m ≤ cell2) with hc | hc
            · rw [ite_eq_left hc] at h
              rcases Decidable.em (u - 1 = c1 + m - 1) with he | he
              · omega
              · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)] at h
                exact Or.inl h
            · rw [ite_eq_right hc] at h
              exact Or.inl h
          · exact Or.inr h
        · rcases Decidable.em (u = c1 + m) with hu' | hu'
          · subst hu'
            rcases Decidable.em (0 < (vs.map (multOf counts)).sum) with
              hf | hf
            · rcases ih6 hf with h | h
              · exact absurd h (by omega)
              · exact Or.inr h
            · rw [hsum, hmv] at htot
              omega
          · refine Or.inl ?_
            rw [ihH (u - 1) (by omega), hpe] at hb
            rcases Decidable.em (c1 + m ≤ cell2) with h | h
            · rw [ite_eq_left h,
                Array.getElem!_set!_ne _ _ _ _ (by omega)] at hb
              exact hb
            · rw [ite_eq_right h] at hb
              exact hb
      · intro _
        rcases Decidable.em (c1 = cell1) with hc | hc
        · exact Or.inl hc
        · refine Or.inr (ih2 c1 ?_)
          rw [hae, ite_eq_left (by simp [hc])]
          exact VSet.mem_insert_self _ (by omega)
      · have hstep : w.active.card + 2 * st.numcells ≤
            st.active.card + 2 * w.numcells := by
          rw [hae, hne]
          rcases Decidable.em (c1 = cell1) with hc | hc
          · rw [ite_eq_right (by simp [hc]), ite_eq_left hc]
            exact Nat.le_refl _
          · rw [ite_eq_left (by simp [hc]), ite_eq_right hc]
            have := VSet.card_insert_le st.active c1
            omega
        omega
      · have hstep : st.numcells ≤ w.numcells := by
          rw [hne]
          rcases Decidable.em (c1 = cell1) with hc | hc
          · rw [ite_eq_left hc]
            exact Nat.le_refl _
          · rw [ite_eq_right hc]
            omega
        omega
      · intro hmc _
        refine ih9 ?_ (Or.inr (by
          rcases Decidable.em (Int.ofNat m > maxcell) with h | h
          · rw [ite_eq_left h]
            simp only [Int.ofNat_eq_natCast]
            omega
          · rw [ite_eq_right h]
            simp only [Int.ofNat_eq_natCast] at h
            omega))
        refine Or.inr ?_
        rw [hme]
        rcases Decidable.em (Int.ofNat (c1 + m - c1) > maxcell) with
          h | h
        · rw [ite_eq_left h]
          refine ⟨by omega, by omega, ?_⟩
          rcases Decidable.em (c1 = cell1) with hc | hc
          · exact Or.inl hc
          · refine Or.inr ?_
            rw [hae, ite_eq_left (by simp [hc])]
            exact VSet.mem_insert_self _ (by omega)
        · rw [ite_eq_right h]
          have hmge : ¬((m : Int) > maxcell) := by
            rw [show Int.ofNat (c1 + m - c1) = (m : Int) from by
              simp only [Int.ofNat_eq_natCast]
              omega] at h
            exact h
          have hmc0 : 0 ≤ maxcell := by
            rcases Decidable.em (0 ≤ maxcell) with h0 | h0
            · exact h0
            · exfalso
              have : (m : Int) ≥ 1 := by exact_mod_cast hm
              omega
          rcases hmc with hmc | hmc
          · omega
          · obtain ⟨hg1, hg2, hg3⟩ := hmc
            refine ⟨hg1, hg2, ?_⟩
            rcases hg3 with hg | hg
            · exact Or.inl hg
            · exact Or.inr (hmonoA _ hg)
    · rw [ite_eq_right hm]
      have hsum0 : (List.map (multOf counts) (v :: vs)).sum =
          (List.map (multOf counts) vs).sum := by
        rw [hsum]
        omega
      obtain ⟨ih1, ih2, ih3, ihH, ih4, ih5, ih6, ih7, ih8, ih9⟩ :=
        windowScan_active_state (level := level) (cell1 := cell1)
          (cell2 := cell2) (counts := counts) hc2 vs c1 maxcell
          st hcw (by rw [← hsum0]; exact htot) hbnd hsz
      refine ⟨ih1, ih2, ih3, ihH, ih4, ih5, ?_, ih7, ih8, ?_⟩
      · intro hf
        rw [hsum0] at hf
        exact ih6 hf
      · intro hmc hf
        refine ih9 hmc ?_
        rcases hf with hf | hf
        · rw [hsum0] at hf
          exact Or.inl hf
        · exact Or.inr hf

private theorem nontrivialFix_active (cell1 : Nat) (st : RefineSt n) :
    (nontrivialFix cell1 st).active =
      if st.active.mem cell1 = true then st.active
      else (st.active.insert cell1).erase st.maxpos := by
  rw [nontrivialFix]
  rcases h : st.active.mem cell1 with _ | _
  · rw [ite_eq_left (by simp), ite_eq_right (by simp)]
  · rw [ite_eq_right (by simp), ite_eq_left (by simp)]

private theorem nontrivialFix_numcells (cell1 : Nat) (st : RefineSt n) :
    (nontrivialFix cell1 st).numcells = st.numcells := by
  rw [nontrivialFix]
  rcases h : st.active.mem cell1 with _ | _
  · rw [ite_eq_left (by simp)]
  · rw [ite_eq_right (by simp)]

/-- One processed cell of the nontrivial pass, the bookkeeping half:
active bits and boundaries outside the window untouched, the
potential ledger balanced, and the two activation clauses — an active
cell activates every fragment start, an inactive one every fragment
start but one. -/
theorem nontrivialCell_outcome {ctx : Ctx n}
    {level cell1 cell2 : Nat} {workset : VSet n} {st : RefineSt n}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.ptn.size) (hnb : cell2 < n)
    (hopen : ∀ q, cell1 ≤ q → q < cell2 → st.ptn[q]! > level) :
    (∀ u, u < cell1 ∨ cell2 < u →
      (nontrivialCell ctx level workset cell1 cell2 st).active.mem u =
        st.active.mem u) ∧
    (∀ q : Nat, q < cell1 ∨ cell2 ≤ q →
      (nontrivialCell ctx level workset cell1 cell2 st).ptn[q]! =
        st.ptn[q]!) ∧
    (nontrivialCell ctx level workset cell1 cell2 st).ptn.size =
      st.ptn.size ∧
    ((nontrivialCell ctx level workset cell1 cell2
        st).active.card + 2 * st.numcells ≤
      st.active.card +
        2 * (nontrivialCell ctx level workset cell1 cell2 st).numcells) ∧
    st.numcells ≤
      (nontrivialCell ctx level workset cell1 cell2 st).numcells ∧
    (st.active.mem cell1 = true →
      ∀ u, cell1 ≤ u → u ≤ cell2 →
        (u = cell1 ∨ (nontrivialCell ctx level workset cell1 cell2
          st).ptn[u - 1]! ≤ level) →
        (nontrivialCell ctx level workset cell1 cell2
          st).active.mem u = true) ∧
    (st.active.mem cell1 = false →
      ∃ w, ∀ u, cell1 ≤ u → u ≤ cell2 →
        (u = cell1 ∨ (nontrivialCell ctx level workset cell1 cell2
          st).ptn[u - 1]! ≤ level) → u ≠ w →
        (nontrivialCell ctx level workset cell1 cell2
          st).active.mem u = true) := by
  rcases Decidable.em (cell1 = cell2) with heq | hne
  · have he : nontrivialCell ctx level workset cell1 cell2 st = st := by
      rw [nontrivialCell, ite_eq_left (by simp [heq])]
    rw [he]
    subst heq
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, by omega, Nat.le_refl _,
      ?_, ?_⟩
    · intro hact u hu1 hu2 _
      rw [show u = cell1 from by omega]
      exact hact
    · intro hact
      exact ⟨cell1, fun u hu1 hu2 _ hne =>
        absurd (show u = cell1 from by omega) hne⟩
  · rw [nontrivialCell, ite_eq_right (by simp [hne])]
    rcases Decidable.em
        ((countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
          ((countsOf ctx st.lab workset cell1 cell2).headD 0) =
        (countsOf ctx st.lab workset cell1 cell2).foldl Nat.max
          ((countsOf ctx st.lab workset cell1 cell2).headD 0)) with
      hmm | hmm
    · rw [ite_eq_left (by simpa using hmm)]
      refine ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, by dsimp only; omega,
        Nat.le_refl _, ?_, ?_⟩
      · intro hact u hu1 hu2 hu3
        rcases Decidable.em (u = cell1) with rfl | hne2
        · exact hact
        · have hb' : st.ptn[u - 1]! ≤ level := by
            rcases hu3 with rfl | hb
            · exact absurd rfl hne2
            · exact hb
          exact absurd hb' (by
            have := hopen (u - 1) (by omega) (by omega)
            omega)
      · intro hact
        refine ⟨cell1, fun u hu1 hu2 hu3 hne2 => ?_⟩
        have hb' : st.ptn[u - 1]! ≤ level := by
          rcases hu3 with rfl | hb
          · exact absurd rfl hne2
          · exact hb
        exact absurd hb' (by
          have := hopen (u - 1) (by omega) (by omega)
          omega)
    · rw [ite_eq_right (by simpa using hmm)]
      obtain ⟨S, hS⟩ : ∃ S, windowScan level cell1 cell2
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st = S := ⟨_, rfl⟩
      have hlen := countsOf_length ctx st.lab workset cell1 cell2
      have htotS : cell1 + ((countValues (countsOf ctx st.lab workset
          cell1 cell2)).map (multOf (countsOf ctx st.lab workset cell1
            cell2))).sum = cell2 + 1 := by
        rw [sum_multOf_countValues, hlen]
        omega
      have hfired : 0 < ((countValues (countsOf ctx st.lab workset
          cell1 cell2)).map (multOf (countsOf ctx st.lab workset cell1
            cell2))).sum := by
        rw [sum_multOf_countValues, hlen]
        omega
      obtain ⟨sc1, sc2, sc3, scH, sc4, sc5, sc6, sc7, sc8, sc9⟩ :=
        windowScan_active_state (level := level) (cell1 := cell1)
          (cell2 := cell2)
          (counts := countsOf ctx st.lab workset cell1 cell2) hnb
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st (Nat.le_refl _) htotS (Or.inl rfl) hsz
      obtain ⟨_, _, scF, scS, _⟩ :=
        windowScan_payload (level := level) (nn := n) hnb
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st (Nat.le_refl _) htotS hsz
          (fun p hp1 hp2 => hopen p hp1 hp2)
      rw [hS] at sc1 sc2 sc3 scH sc4 sc5 sc6 sc7 sc8 sc9 scF scS
      have hmp := sc9 (Or.inl (by omega)) (Or.inl hfired)
      have hcell1A : S.active.mem cell1 = st.active.mem cell1 :=
        sc1 cell1 (Or.inl (Nat.le_refl _))
      have hax : (nontrivialFix cell1 { S with
          lab := writeSegment S.lab cell1 (segmentOf S.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2))) }).active =
          if S.active.mem cell1 = true then S.active
          else (S.active.insert cell1).erase S.maxpos := by
        rw [nontrivialFix_active]
      have hpx : (nontrivialFix cell1 { S with
          lab := writeSegment S.lab cell1 (segmentOf S.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2))) }).ptn = S.ptn := by
        rw [nontrivialFix_ptn]
      have hnx : (nontrivialFix cell1 { S with
          lab := writeSegment S.lab cell1 (segmentOf S.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2))) }).numcells = S.numcells := by
        rw [nontrivialFix_numcells]
      rw [hS, hax, hpx, hnx]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rcases hb : st.active.mem cell1 with _ | _
        · rw [ite_eq_right (by simp [hcell1A, hb]), VSet.mem_erase,
            VSet.mem_insert,
            show (cell1 == u) = false from by
              simp only [beq_eq_false_iff_ne]
              omega,
            Bool.false_and, Bool.or_false,
            show (S.maxpos == u) = false from by
              simp only [beq_eq_false_iff_ne]
              omega,
            Bool.not_false, Bool.and_true]
          exact sc1 u (by omega)
        · rw [ite_eq_left (by rw [hcell1A, hb])]
          exact sc1 u (by omega)
      · intro q hq
        exact scF q (by omega)
      · exact scS
      · rcases hb : st.active.mem cell1 with _ | _
        · rw [ite_eq_right (by simp [hcell1A, hb])]
          have h1 := VSet.card_insert_le S.active cell1
          have h2 : (S.active.insert cell1).mem S.maxpos = true := by
            rcases hmp.2.2 with hm | hm
            · rw [hm]
              exact VSet.mem_insert_self _ (by omega)
            · exact VSet.mem_insert_mono _ _ hm
          have h3 := VSet.card_erase_of_mem h2
          omega
        · rw [ite_eq_left (by rw [hcell1A, hb])]
          exact sc7
      · exact sc8
      · intro hact u hu1 hu2 hu3
        rw [ite_eq_left (by rw [hcell1A, hact])]
        rcases Decidable.em (u = cell1) with rfl | hne2
        · rw [hcell1A]
          exact hact
        · have hb : S.ptn[u - 1]! ≤ level := by
            rcases hu3 with rfl | hb
            · exact absurd rfl hne2
            · exact hb
          rcases sc5 u (by omega) hu2 hb with h | h
          · exact absurd h (by
              have := hopen (u - 1) (by omega) (by omega)
              omega)
          · exact h
      · intro hact
        refine ⟨S.maxpos, fun u hu1 hu2 hu3 hne2 => ?_⟩
        rw [ite_eq_right (by simp [hcell1A, hact]), VSet.mem_erase,
          show (S.maxpos == u) = false from by
            simp only [beq_eq_false_iff_ne]
            omega,
          Bool.not_false, Bool.and_true, VSet.mem_insert]
        have hlt : cell1 < n := by omega
        rcases hu3 with rfl | hb
        · simp [hlt]
        · rcases Decidable.em (u = cell1) with rfl | hne3
          · simp [hlt]
          · rcases sc5 u (by omega) hu2 hb with h | h
            · exact absurd h (by
                have := hopen (u - 1) (by omega) (by omega)
                omega)
            · rw [h, Bool.true_or]

/-- The nontrivial pass over a window list, the bookkeeping half. -/
theorem refineNontrivial_go_state {ctx : Ctx n} {level : Nat} {workset : VSet n} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n),
      (∀ p ∈ cs, p.1 ≤ p.2 ∧ p.2 < st.ptn.size ∧ p.2 < n) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      (∀ p ∈ cs, ∀ q, p.1 ≤ q → q < p.2 → st.ptn[q]! > level) →
      (∀ u, (∀ p ∈ cs, u < p.1 ∨ p.2 < u) →
        (refineNontrivial.go ctx level workset cs st).active.mem u =
          st.active.mem u) ∧
      (∀ q : Nat, (∀ p ∈ cs, q < p.1 ∨ p.2 ≤ q) →
        (refineNontrivial.go ctx level workset cs st).ptn[q]! =
          st.ptn[q]!) ∧
      (refineNontrivial.go ctx level workset cs st).ptn.size =
        st.ptn.size ∧
      ((refineNontrivial.go ctx level workset cs
          st).active.card + 2 * st.numcells ≤
        st.active.card +
          2 * (refineNontrivial.go ctx level workset cs st).numcells) ∧
      st.numcells ≤
        (refineNontrivial.go ctx level workset cs st).numcells ∧
      (∀ p ∈ cs,
        (st.active.mem p.1 = true →
          ∀ u, p.1 ≤ u → u ≤ p.2 →
            (u = p.1 ∨ (refineNontrivial.go ctx level workset cs
              st).ptn[u - 1]! ≤ level) →
            (refineNontrivial.go ctx level workset cs
              st).active.mem u = true) ∧
        (st.active.mem p.1 = false →
          ∃ w, ∀ u, p.1 ≤ u → u ≤ p.2 →
            (u = p.1 ∨ (refineNontrivial.go ctx level workset cs
              st).ptn[u - 1]! ≤ level) → u ≠ w →
            (refineNontrivial.go ctx level workset cs
              st).active.mem u = true))
  | [], st, _, _, _ => by
    rw [refineNontrivial.go]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, by omega, Nat.le_refl _,
      fun p hp => absurd hp (by simp)⟩
  | (c1, c2) :: rest, st, hw, hpw, hop => by
    rw [refineNontrivial.go]
    obtain ⟨h12, hsz, hnb⟩ := hw (c1, c2) (List.mem_cons_self ..)
    dsimp only at h12 hsz hnb
    obtain ⟨o1, o2, oS, o3, o4, o5, o6⟩ :=
      nontrivialCell_outcome (ctx := ctx) (level := level)
        (workset := workset) (st := st) h12 hsz hnb
        (fun q hq1 hq2 => hop (c1, c2) (List.mem_cons_self ..) q hq1 hq2)
    have hhead := (List.pairwise_cons.mp hpw).1
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ :=
      refineNontrivial_go_state rest
        (nontrivialCell ctx level workset c1 c2 st)
        (fun p hp => by
          obtain ⟨hp1, hp2, hp3⟩ := hw p (List.mem_cons_of_mem _ hp)
          exact ⟨hp1, by rw [oS]; exact hp2, hp3⟩)
        (List.pairwise_cons.mp hpw).2
        (fun p hp q hq1 hq2 => by
          rw [o2 q (Or.inr (by
            have := hhead p hp
            simp only at this
            omega))]
          exact hop p (List.mem_cons_of_mem _ hp) q hq1 hq2)
    have hkeepP : ∀ q, q ≤ c2 →
        (refineNontrivial.go ctx level workset rest
          (nontrivialCell ctx level workset c1 c2 st)).ptn[q]! =
          (nontrivialCell ctx level workset c1 c2 st).ptn[q]! := by
      intro q hq
      exact ih2 q fun pr hpr => Or.inl (by
        have := hhead pr hpr
        simp only at this
        omega)
    have hkeepA : ∀ u, u ≤ c2 →
        (refineNontrivial.go ctx level workset rest
          (nontrivialCell ctx level workset c1 c2 st)).active.mem u =
          (nontrivialCell ctx level workset c1 c2
            st).active.mem u := by
      intro u hu
      exact ih1 u fun pr hpr => Or.inl (by
        have := hhead pr hpr
        simp only at this
        omega)
    refine ⟨?_, ?_, by rw [ih3, oS], ?_, ?_, ?_⟩
    · intro u hu
      rw [ih1 u fun pr hpr => hu pr (List.mem_cons_of_mem _ hpr),
        o1 u (by
          have := hu (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · intro q hq
      rw [ih2 q fun pr hpr => hq pr (List.mem_cons_of_mem _ hpr),
        o2 q (by
          have := hq (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · omega
    · omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · constructor
        · intro hact u hu1 hu2 hu3
          rw [hkeepA u hu2]
          refine o5 hact u hu1 hu2 ?_
          rcases hu3 with rfl | hb
          · exact Or.inl rfl
          · refine Or.inr ?_
            rw [← hkeepP (u - 1) (by omega)]
            exact hb
        · intro hact
          obtain ⟨w, hwc⟩ := o6 hact
          refine ⟨w, fun u hu1 hu2 hu3 hne2 => ?_⟩
          rw [hkeepA u hu2]
          refine hwc u hu1 hu2 ?_ hne2
          rcases hu3 with rfl | hb
          · exact Or.inl rfl
          · refine Or.inr ?_
            rw [← hkeepP (u - 1) (by omega)]
            exact hb
      · have hout1 : c2 < p.1 := by
          have := hhead p hmem
          simpa using this
        obtain ⟨hA, hI⟩ := ih6 p hmem
        have hacteq : (nontrivialCell ctx level workset c1 c2
            st).active.mem p.1 = st.active.mem p.1 :=
          o1 p.1 (Or.inr (by omega))
        constructor
        · intro hact u hu1 hu2 hu3
          exact hA (by rw [hacteq]; exact hact) u hu1 hu2 hu3
        · intro hact
          exact hI (by rw [hacteq]; exact hact)

private theorem trivial_state_of_fields {ctx : Ctx n}
    {level split1 : Nat} {st R : RefineSt n}
    (hRa : R.active = st.active.erase split1) (hRp : R.ptn = st.ptn)
    (hRl : R.lab = st.lab) (hRn : R.numcells = st.numcells)
    (hok : StOk n level st)
    (hmem : st.active.mem split1 = true) :
    ((refineTrivial ctx level split1 R).active.card +
        2 * st.numcells + 1 ≤
      st.active.card +
        2 * (refineTrivial ctx level split1 R).numcells) ∧
    st.numcells ≤ (refineTrivial ctx level split1 R).numcells ∧
    (∀ p ∈ cells st.ptn level n,
      (st.active.mem p.1 = true → p.1 ≠ split1 →
        ∀ u, p.1 ≤ u → u ≤ p.2 →
          (u = p.1 ∨ (refineTrivial ctx level split1
            R).ptn[u - 1]! ≤ level) →
          (refineTrivial ctx level split1 R).active.mem u = true) ∧
      ((st.active.mem p.1 = false ∨ p.1 = split1) →
        ∃ w, ∀ u, p.1 ≤ u → u ≤ p.2 →
          (u = p.1 ∨ (refineTrivial ctx level split1
            R).ptn[u - 1]! ≤ level) → u ≠ w →
          (refineTrivial ctx level split1 R).active.mem u = true)) := by
  have hps := hok.ptnSize
  have hls := hok.labSize
  have hend := hok.ptnEnd
  have hendn : st.ptn[n - 1]! ≤ level := by
    have h := hend
    rw [hps] at h
    exact h
  have hcbd := cells_end_lt_of_end (ptn := st.ptn) (level := level)
    (Nat.le_of_eq hps.symm) hend hendn
  have hopenc : ∀ p ∈ cells st.ptn level n,
      ∀ q, p.1 ≤ q → q < p.2 → st.ptn[q]! > level := by
    intro p hp q hq1 hq2
    exact (cells_isCell (Nat.le_of_eq hps.symm) hend p hp).2.2.1 q hq1
      (by
        have := cells_le p hp
        omega)
  have herase : (st.active.erase split1).card + 1 =
      st.active.card :=
    VSet.card_erase_of_mem hmem
  have hactconv : ∀ a : Nat, a ≠ split1 →
      (st.active.erase split1).mem a = st.active.mem a := by
    intro a ha
    rw [VSet.mem_erase,
      show (split1 == a) = false from by
        simp only [beq_eq_false_iff_ne]
        omega,
      Bool.not_false, Bool.and_true]
  rw [refineTrivial, hRp]
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ :=
    refineTrivial_go_state (level := level)
      (gRow := ctx.g[R.lab[split1]!]!)
      (cells st.ptn level n) R
      (fun p hp => ⟨cells_le p hp, by
        rw [hRl, hls]
        exact hcbd p hp⟩)
      cells_pairwise
      (by rw [hRp, hRl]; omega)
      (by rw [hRl]; exact hls)
  rw [hRa] at g2 g4 g6
  rw [hRn] at g4 g5
  refine ⟨by omega, g5, ?_⟩
  intro p hp
  have hopen := hopenc p hp
  have hle12 := cells_le p hp
  rcases g6 p hp with ⟨hPu, hAu⟩ | ⟨j, x, hj1, hj2, hjl, hPo, hx,
      himp, hax, hAo⟩
  · constructor
    · intro hact hne u hu1 hu2 hu3
      rcases Decidable.em (u = p.1) with heq | hne2
      · rw [heq, hAu p.1 (Nat.le_refl _) (by omega), hactconv p.1 hne]
        exact hact
      · have hb := hu3.resolve_left hne2
        rw [hPu (u - 1) (by omega) (by omega), hRp] at hb
        exact absurd hb (by
          have := hopen (u - 1) (by omega) (by omega)
          omega)
    · intro hact
      refine ⟨p.1, fun u hu1 hu2 hu3 hne2 => ?_⟩
      have hb := hu3.resolve_left hne2
      rw [hPu (u - 1) (by omega) (by omega), hRp] at hb
      exact absurd hb (by
        have := hopen (u - 1) (by omega) (by omega)
        omega)
  · have himp' : st.active.mem p.1 = true → p.1 ≠ split1 →
        x = j + 1 := by
      intro hact hne
      exact himp (by rw [hactconv p.1 hne]; exact hact)
    constructor
    · intro hact hne u hu1 hu2 hu3
      have hxj := himp' hact hne
      rcases Decidable.em (u = p.1) with heq | hne2
      · rw [heq, hAo p.1 (Nat.le_refl _) (by omega) (by omega),
          hactconv p.1 hne]
        exact hact
      · have hb := hu3.resolve_left hne2
        rcases Decidable.em (u - 1 = j) with hej | hej
        · rw [show u = x from by omega]
          exact hax
        · rw [hPo (u - 1) (by omega) (by omega) hej, hRp] at hb
          exact absurd hb (by
            have := hopen (u - 1) (by omega) (by omega)
            omega)
    · intro hact
      rcases hx with hxa | hxb
      · refine ⟨j + 1, fun u hu1 hu2 hu3 hne2 => ?_⟩
        rcases Decidable.em (u = x) with heq | hne3
        · rw [heq]
          exact hax
        · have hb := hu3.resolve_left (by omega)
          rcases Decidable.em (u - 1 = j) with hej | hej
          · exact absurd (show u = j + 1 from by omega) hne2
          · rw [hPo (u - 1) (by omega) (by omega) hej, hRp] at hb
            exact absurd hb (by
              have := hopen (u - 1) (by omega) (by omega)
              omega)
      · refine ⟨p.1, fun u hu1 hu2 hu3 hne2 => ?_⟩
        have hb := hu3.resolve_left hne2
        rcases Decidable.em (u - 1 = j) with hej | hej
        · rw [show u = x from by omega]
          exact hax
        · rw [hPo (u - 1) (by omega) (by omega) hej, hRp] at hb
          exact absurd hb (by
            have := hopen (u - 1) (by omega) (by omega)
            omega)

private theorem nontrivial_state_of_fields {ctx : Ctx n}
    {level split1 split2 : Nat} {st R : RefineSt n}
    (hRa : R.active = st.active.erase split1) (hRp : R.ptn = st.ptn)
    (_hRl : R.lab = st.lab) (hRn : R.numcells = st.numcells)
    (hok : StOk n level st)
    (hmem : st.active.mem split1 = true) :
    ((refineNontrivial ctx level split1 split2 R).active.card +
        2 * st.numcells + 1 ≤
      st.active.card +
        2 * (refineNontrivial ctx level split1 split2 R).numcells) ∧
    st.numcells ≤
      (refineNontrivial ctx level split1 split2 R).numcells ∧
    (∀ p ∈ cells st.ptn level n,
      (st.active.mem p.1 = true → p.1 ≠ split1 →
        ∀ u, p.1 ≤ u → u ≤ p.2 →
          (u = p.1 ∨ (refineNontrivial ctx level split1 split2
            R).ptn[u - 1]! ≤ level) →
          (refineNontrivial ctx level split1 split2
            R).active.mem u = true) ∧
      ((st.active.mem p.1 = false ∨ p.1 = split1) →
        ∃ w, ∀ u, p.1 ≤ u → u ≤ p.2 →
          (u = p.1 ∨ (refineNontrivial ctx level split1 split2
            R).ptn[u - 1]! ≤ level) → u ≠ w →
          (refineNontrivial ctx level split1 split2
            R).active.mem u = true)) := by
  have hps := hok.ptnSize
  have hend := hok.ptnEnd
  have hendn : st.ptn[n - 1]! ≤ level := by
    have h := hend
    rw [hps] at h
    exact h
  have hcbd := cells_end_lt_of_end (ptn := st.ptn) (level := level)
    (Nat.le_of_eq hps.symm) hend hendn
  have hopenc : ∀ p ∈ cells st.ptn level n,
      ∀ q, p.1 ≤ q → q < p.2 → st.ptn[q]! > level := by
    intro p hp q hq1 hq2
    exact (cells_isCell (Nat.le_of_eq hps.symm) hend p hp).2.2.1 q hq1
      (by
        have := cells_le p hp
        omega)
  have herase : (st.active.erase split1).card + 1 =
      st.active.card :=
    VSet.card_erase_of_mem hmem
  have hactconv : ∀ a : Nat, a ≠ split1 →
      (st.active.erase split1).mem a = st.active.mem a := by
    intro a ha
    rw [VSet.mem_erase,
      show (split1 == a) = false from by
        simp only [beq_eq_false_iff_ne]
        omega,
      Bool.not_false, Bool.and_true]
  have hactsp : (st.active.erase split1).mem split1 = false := by
    rw [VSet.mem_erase]
    simp
  rw [refineNontrivial]
  dsimp only
  obtain ⟨R2, hR2⟩ : ∃ R2 : RefineSt n, ({ R with
      longcode := mash R.longcode (split2 - split1 + 1) } :
        RefineSt n) = R2 := ⟨_, rfl⟩
  have hR2a : R2.active = st.active.erase split1 := by
    rw [← hR2]
    exact hRa
  have hR2p : R2.ptn = st.ptn := by
    rw [← hR2]
    exact hRp
  have hR2n : R2.numcells = st.numcells := by
    rw [← hR2]
    exact hRn
  rw [hR2, hRp]
  obtain ⟨_, _, _, g4, g5, g6⟩ :=
    refineNontrivial_go_state (ctx := ctx) (level := level)
      (workset := worksetOf n R.lab split1 split2)
      (cells R.ptn level n) R2
      (fun p hp => by
        rw [hRp] at hp
        refine ⟨cells_le p hp, ?_, ?_⟩
        · rw [hR2p, hps]
          exact hcbd p hp
        · have := hcbd p hp
          omega)
      (by rw [hRp]; exact cells_pairwise)
      (fun p hp q hq1 hq2 => by
        rw [hR2p]
        rw [hRp] at hp
        exact hopenc p hp q hq1 hq2)
  rw [hR2a] at g4 g6
  rw [hR2n] at g4 g5
  rw [hRp] at g4 g5 g6
  refine ⟨by omega, g5, ?_⟩
  intro p hp
  obtain ⟨hA, hI⟩ := g6 p hp
  constructor
  · intro hact hne u hu1 hu2 hu3
    exact hA (by rw [hactconv p.1 hne]; exact hact) u hu1 hu2 hu3
  · intro hact
    refine hI ?_
    rcases hact with hact | heq
    · rcases Decidable.em (p.1 = split1) with heq2 | hne
      · rw [heq2]
        exact hactsp
      · rw [hactconv p.1 hne]
        exact hact
    · rw [heq]
      exact hactsp

/-- One `refineStep`, the bookkeeping half: the potential drops
strictly, and per old cell an active non-splitter cell activates every
fragment start while any other cell leaves at most one start
inactive. -/
theorem refineStep_state {ctx : Ctx n} {level split1 : Nat}
    {st : RefineSt n} (hok : StOk n level st)
    (hmem : st.active.mem split1 = true) :
    ((refineStep ctx level split1 st).active.card +
        2 * st.numcells + 1 ≤
      st.active.card +
        2 * (refineStep ctx level split1 st).numcells) ∧
    st.numcells ≤ (refineStep ctx level split1 st).numcells ∧
    (∀ p ∈ cells st.ptn level n,
      (st.active.mem p.1 = true → p.1 ≠ split1 →
        ∀ u, p.1 ≤ u → u ≤ p.2 →
          (u = p.1 ∨ (refineStep ctx level split1
            st).ptn[u - 1]! ≤ level) →
          (refineStep ctx level split1 st).active.mem u = true) ∧
      ((st.active.mem p.1 = false ∨ p.1 = split1) →
        ∃ w, ∀ u, p.1 ≤ u → u ≤ p.2 →
          (u = p.1 ∨ (refineStep ctx level split1
            st).ptn[u - 1]! ≤ level) → u ≠ w →
          (refineStep ctx level split1 st).active.mem u = true)) := by
  rw [refineStep]
  dsimp only
  split
  · exact trivial_state_of_fields (st := st) rfl rfl rfl rfl hok
      hmem
  · exact nontrivial_state_of_fields (st := st) rfl rfl rfl rfl hok
      hmem

end Hex.GraphIso.Nauty

