/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Refine
import all HexGraphIso.Nauty.Search.State

public section

/-! Reach preservation for primitive state transitions. -/

namespace Hex.GraphIso.Nauty

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

/-! # Search-state operation facts -/

private theorem pushAuto_lab (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).lab = st.lab := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_ptn (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).ptn = st.ptn := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_canonlab (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).canonlab = st.canonlab := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_firstlab (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).firstlab = st.firstlab := by
  rw [pushAuto]
  split <;> rfl

private theorem firstterminal_lab (level : Nat) (st : SearchSt n) :
    (firstterminal level st).lab = st.lab := rfl

private theorem firstterminal_ptn (level : Nat) (st : SearchSt n) :
    (firstterminal level st).ptn = st.ptn := rfl

private theorem firstterminal_canonlab (level : Nat) (st : SearchSt n) :
    (firstterminal level st).canonlab = st.lab := rfl

/-- `[:n]` unfolds to a `forIn` over `List.range n`. -/
private theorem forIn_range_eq' {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

private theorem forIn_reopen_eq {inf level : Nat} :
    ∀ (l : List Nat) (ptn : Array Nat),
      (forIn l ptn (fun i r =>
        if r[i]! > level then
          pure (ForInStep.yield (r.set! i inf))
        else
          pure (ForInStep.yield r)) : Id (Array Nat)) =
      l.foldl
        (fun r i => if r[i]! > level then r.set! i inf else r) ptn
  | [], _ => rfl
  | i :: l, ptn => by
    rw [List.forIn_cons, List.foldl_cons]
    rcases Decidable.em (ptn[i]! > level) with h | h
    · rw [ite_eq_left h, ite_eq_left h]
      exact forIn_reopen_eq l _
    · rw [ite_eq_right h, ite_eq_right h]
      exact forIn_reopen_eq l _

private theorem foldl_reopen_size {inf level : Nat} :
    ∀ (l : List Nat) (ptn : Array Nat),
      (l.foldl
        (fun r i => if r[i]! > level then r.set! i inf else r)
        ptn).size = ptn.size
  | [], _ => rfl
  | i :: l, ptn => by
    rw [List.foldl_cons]
    rcases Decidable.em (ptn[i]! > level) with h | h
    · rw [ite_eq_left h, foldl_reopen_size l _, Array.size_set!]
    · rw [ite_eq_right h, foldl_reopen_size l _]

private theorem foldl_reopen_getElem {inf level : Nat} :
    ∀ {nn : Nat} (ptn : Array Nat) (q : Nat),
      ((List.range nn).foldl
        (fun r i => if r[i]! > level then r.set! i inf else r)
        ptn)[q]! =
      if q < nn ∧ ptn[q]! > level then inf else ptn[q]! := by
  intro nn
  induction nn with
  | zero =>
    intro ptn q
    rw [List.range_zero, List.foldl_nil,
      ite_eq_right (by rintro ⟨h, -⟩; omega)]
  | succ m ih =>
    intro ptn q
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    have hm := ih ptn m
    rw [ite_eq_right (by rintro ⟨h, -⟩; omega)] at hm
    rcases Decidable.em (ptn[m]! > level) with hop | hop
    · rw [ite_eq_left (by rw [hm]; exact hop)]
      rcases Decidable.em (q = m) with rfl | hne
      · rcases Nat.lt_or_ge q ptn.size with hqs | hqs
        · rw [Array.getElem!_set!_self _ _ _
            (by rw [foldl_reopen_size]; exact hqs),
            ite_eq_left ⟨by omega, hop⟩]
        · rw [getElem!_neg ptn q (by omega)] at hop
          exact absurd hop (Nat.not_lt.mpr (Nat.zero_le level))
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hne h.symm),
          ih ptn q]
        rcases Decidable.em (q < m ∧ ptn[q]! > level) with hc | hc
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (by
            rintro ⟨h1, h2⟩
            exact hc ⟨by omega, h2⟩)]
    · rw [ite_eq_right (by rw [hm]; exact hop), ih ptn q]
      rcases Decidable.em (q < m ∧ ptn[q]! > level) with hc | hc
      · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc.2⟩]
      · rw [ite_eq_right hc, ite_eq_right (by
          rintro ⟨h1, h2⟩
          rcases Decidable.em (q = m) with rfl | hne
          · exact hop h2
          · exact hc ⟨by omega, h2⟩)]

private theorem ite_or {α : Type} {P : α → Prop} {c : Prop}
    [Decidable c] {a b : α} (ha : P a) (hb : P b) :
    P (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- `recover` never changes the current labelling. -/
theorem recover_lab (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).lab = st.lab := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.lab, ite_self]

private theorem recover_canonlab (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).canonlab = st.canonlab := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlab, ite_self]

private theorem recover_ptn_foldl (n inf level : Nat)
    (st : SearchSt n) :
    (recover n inf level st).ptn =
      (List.range n).foldl
        (fun r i => if r[i]! > level then r.set! i inf else r)
        st.ptn := by
  have h1 : (recover n inf level st).ptn =
      (forIn [0:n] st.ptn (fun i r =>
        if r[i]! > level then
          pure (ForInStep.yield (r.set! i inf))
        else
          pure (ForInStep.yield r)) : Id (Array Nat)) := by
    rw [recover]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite SearchSt.ptn, ite_self]
    rfl
  rw [h1, forIn_range_eq', forIn_reopen_eq]

/-- `recover` reopens exactly the entries above its receiving level. -/
theorem recover_ptn (n inf level : Nat) (st : SearchSt n)
    (q : Nat) :
    (recover n inf level st).ptn[q]! =
      if q < n ∧ st.ptn[q]! > level then inf else st.ptn[q]! := by
  rw [recover_ptn_foldl, foldl_reopen_getElem]

/-- Reopening a partition preserves its array size. -/
theorem recover_ptn_size (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).ptn.size = st.ptn.size := by
  rw [recover_ptn_foldl, foldl_reopen_size]

private theorem processnode_lab (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.lab = st.lab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.lab), pushAuto_lab,
    ite_self]

private theorem processnode_ptn (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.ptn = st.ptn := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.ptn), pushAuto_ptn,
    ite_self]

/-- `processnode` either keeps `canonlab` or installs the current
labelling. -/
private theorem processnode_canonlab (ctx : Ctx n)
    (level numcells : Nat) (st : SearchSt n) :
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∨
      (processnode ctx level numcells st).2.canonlab = st.lab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.canonlab),
    pushAuto_canonlab]
  refine ite_or (P := fun y => y = st.canonlab ∨ y = st.lab) ?_ ?_ <;>
  repeat' first
  | exact Or.inl rfl
  | exact Or.inr rfl
  | apply ite_or (P := fun y => y = st.canonlab ∨ y = st.lab)

/-! # Pruning shrinks the target cell -/

private theorem mem_inter_left {a b : VSet n} {v : Nat}
    (h : (a.inter b).mem v = true) : a.mem v = true := by
  rw [VSet.mem_inter, Bool.and_eq_true] at h
  exact h.1

private theorem shortprune_subset {tcell : VSet n} {st : SearchSt n}
    {v : Nat} (h : (shortprune tcell st).mem v = true) :
    tcell.mem v = true := by
  rw [shortprune] at h
  rcases hb : st.autos.back? with _ | pair
  · rw [hb] at h
    exact h
  · rw [hb] at h
    exact mem_inter_left h

private theorem longprune_subset {fixedpts : VSet n} {v : Nat} :
    ∀ {autos : List (VSet n × VSet n)} {tcell : VSet n},
      (autos.foldl
        (fun tcell (pair : VSet n × VSet n) =>
          if fixedpts.subset pair.1 then tcell.inter pair.2
          else tcell) tcell).mem v = true →
      tcell.mem v = true
  | [], _, h => h
  | pair :: autos, tcell, h => by
    rw [List.foldl_cons] at h
    have h1 := longprune_subset (autos := autos) h
    split at h1
    · exact mem_inter_left h1
    · exact h1

private theorem longprune_mem {tcell fixedpts : VSet n}
    {autos : Array (VSet n × VSet n)} {v : Nat}
    (h : (longprune tcell fixedpts autos).mem v = true) :
    tcell.mem v = true := by
  rw [longprune, ← Array.foldl_toList] at h
  exact longprune_subset h

/-- `nextElem` yields only from a nonempty set. -/
private theorem nextElem_some_ne_empty {s : VSet n} {pos : Option Nat}
    {v : Nat} (h : s.nextElem pos = some v) : s ≠ VSet.empty := by
  rintro rfl
  have := VSet.nextElem_mem h
  rw [VSet.mem_empty] at this
  cases this

/-! # The quartet induction -/

variable {n k : Nat}

/-- One `recover` step satisfies the exit contract at its own
level. -/
theorem recover_out {G : Colored n k} {level : Nat}
    {st : SearchSt n} (hlev : level + 1 < n + 2)
    (hreach : CellsReach G st.lab) :
    SearchOut G level level st (recover n (n + 2) level st) := by
  refine ⟨by rw [recover_lab], recover_ptn_size _ _ _ _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [recover_lab]
    exact hreach
  · intro q hq
    rw [recover_ptn]
    rcases Decidable.em (q < n ∧ st.ptn[q]! > level) with hc | hc
    · exfalso
      rcases hq with h | h
      · omega
      · rw [recover_ptn, ite_eq_left hc] at h
        omega
    · rw [ite_eq_right hc]
  · rw [recover_lab]
    exact cellsPerm_refl _ _ _
  · left
    rw [recover]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite SearchSt.firstlab, ite_self]
  · left
    rw [recover_canonlab]
  · rw [recover_canonlab]
    exact Or.inl rfl

private theorem otherNodePrep_lab (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).lab = st.lab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.lab, ite_self]

private theorem otherNodePrep_ptn (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).ptn = st.ptn := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.ptn, ite_self]

private theorem otherNodePrep_canonlab (level code : Nat)
    (st : SearchSt n) :
    (otherNodePrep level code st).canonlab = st.canonlab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlab, ite_self]

private theorem otherNodePrep_firstlab (level code : Nat)
    (st : SearchSt n) :
    (otherNodePrep level code st).firstlab = st.firstlab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.firstlab, ite_self]

private theorem processnode_firstlab (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.firstlab = st.firstlab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.firstlab),
    pushAuto_firstlab, ite_self]

/-- `processnode` preserves the node invariant, installing at most a
reached labelling. -/
theorem processnode_searchOk {G : Colored n k} {ctx : Ctx n}
    {level nc pnl pnn : Nat} {st4 st5 : SearchSt n}
    (hok4 : SearchOk G level nc st4)
    (hl : st5.lab = (processnode ctx pnl pnn st4).2.lab)
    (hp : st5.ptn = (processnode ctx pnl pnn st4).2.ptn)
    (hc : st5.canonlab = (processnode ctx pnl pnn st4).2.canonlab) :
    SearchOk G level nc st5 := by
  rw [processnode_lab] at hl
  rw [processnode_ptn] at hp
  refine ⟨by rw [hl]; exact hok4.labSize,
    by rw [hp]; exact hok4.ptnSize,
    by rw [hl]; exact hok4.reach,
    fun q hq => by rw [hp]; exact hok4.init1 q hq,
    fun q hqn => by rw [hp]; exact hok4.vals q hqn,
    by rw [hp]; exact hok4.count,
    by rw [hp]; exact hok4.bc, ?_⟩
  rcases processnode_canonlab ctx pnl pnn st4 with h | h
  · rw [hc, h]
    exact hok4.canon
  · rw [hc, h]
    exact Or.inr ⟨hok4.labSize, by rw [hl] at *; exact hok4.reach⟩

set_option maxHeartbeats 3200000 in
/-- Transport the `processnode` canonlab dichotomy along projection
equations, keyed on the output state. -/
theorem canonlab_or_of {G : Colored n k} {ctx : Ctx n}
    {pnl pnn : Nat} {st4 stO : SearchSt n} {cl rl : Array Nat}
    (hO : stO.canonlab = (processnode ctx pnl pnn st4).2.canonlab)
    (hc : st4.canonlab = cl) (hl : st4.lab = rl)
    (hsz : rl.size = n) (hre : CellsReach G rl) :
    stO.canonlab = cl ∨
      (stO.canonlab.size = n ∧ CellsReach G stO.canonlab) := by
  rcases processnode_canonlab ctx pnl pnn st4 with h | h
  · exact Or.inl (hO.trans (h.trans hc))
  · right
    have he : stO.canonlab = rl := hO.trans (h.trans hl)
    rw [he]
    exact ⟨hsz, hre⟩

/-- Transport `processnode`'s preservation of the first leaf through a
state update that does not touch the stored labelling. -/
private theorem firstlab_eq_of {ctx : Ctx n} {pnl pnn : Nat}
    {st4 stO : SearchSt n} {fl : Array Nat}
    (hO : stO.firstlab = (processnode ctx pnl pnn st4).2.firstlab)
    (hf : st4.firstlab = fl) : stO.firstlab = fl := by
  exact hO.trans ((processnode_firstlab ctx pnl pnn st4).trans hf)

/-- Transport the cell-permutation form of the `processnode` canonical
store dichotomy through a state update. -/
private theorem canonStore_or_of {ctx : Ctx n} {pnl pnn lev : Nat}
    {st4 stO : SearchSt n} {cl rl lab ptn : Array Nat}
    (hO : stO.canonlab = (processnode ctx pnl pnn st4).2.canonlab)
    (hc : st4.canonlab = cl) (hl : st4.lab = rl)
    (hsz : rl.size = lab.size) (hperm : cellsPerm ptn lev lab rl) :
    stO.canonlab = cl ∨
      (stO.canonlab.size = lab.size ∧
        cellsPerm ptn lev lab stO.canonlab) := by
  rcases processnode_canonlab ctx pnl pnn st4 with h | h
  · exact Or.inl (hO.trans (h.trans hc))
  · right
    have he : stO.canonlab = rl := hO.trans (h.trans hl)
    rw [he]
    exact ⟨hsz, hperm⟩

/-- The root state satisfies the search invariant. -/
theorem root_searchOk {k : Nat} (G : Colored n k)
    (hn0 : 0 < n) :
    SearchOk G 1 (initialPartition G).2.length
      { lab := (initialPartition G).1
        ptn := initPtn n (n + 2) (initialPartition G).2
        active := initActive n (initialPartition G).2
        orbits := .ofFn (n := n) fun i => i.val
        firstcode := .replicate (n + 2) 0
        canoncode := .replicate (n + 2) 0
        firsttc := .replicate (n + 2) (-1)
        firstlab := .replicate n 0
        canonlab := .replicate n 0
        canong := .replicate n .empty
        numorbits := n } := by
  have hinitEnd := (initial_nodeOk G hn0).ptnEnd
  rw [size_initPtn] at hinitEnd
  refine ⟨size_initialPartition G, size_initPtn _ _ _,
    cellsReach_initial G, fun q hq => hq, ?_, ?_, ?_, Or.inl rfl⟩
  · intro q hqn
    rw [getElem!_initPtn]
    rcases Decidable.em (q ∈ (initialPartition G).2 ∧ q < n) with
      hm | hm
    · rw [ite_eq_left hm]
      exact Or.inl (by omega)
    · rw [ite_eq_right hm, ite_eq_left hqn]
      exact Or.inr rfl
  · exact (bcount_initPtn G).symm
  · exact bcount_pos_of_boundary (q := n - 1) (by omega) hinitEnd


end Hex.GraphIso.Nauty
