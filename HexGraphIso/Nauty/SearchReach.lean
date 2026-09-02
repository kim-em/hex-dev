/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchInv
import all HexGraphIso.Nauty.Search

public section

/-!
The quartet induction: every state the transcribed search
(`firstPathNode`/`firstChildLoop`/`otherNode`/`otherChildLoop`)
reaches keeps its labelling cell-content-reachable from the initial
labelling (`CellsReach`), its initial boundaries intact, and its
`numcells` accurate — so the search's `canonlab` output is reached
(`canonlab_cellsReach`), which discharges the transcription-side
residuals of `certifyCanon?_isSome`
(`colorSortedCheck_canonlab`, `canonlab_perm_range`).

The state-operation lemmas unfold the non-exposed search definitions,
so they live here behind `import all` and stay private; only the
`runColored`-level results are exported.
-/

namespace Hex.GraphIso.Nauty

/-! # Search-state operation facts -/

private theorem pushAuto_lab (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).lab = st.lab := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_ptn (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).ptn = st.ptn := by
  rw [pushAuto]
  split <;> rfl

private theorem pushAuto_canonlab (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).canonlab = st.canonlab := by
  rw [pushAuto]
  split <;> rfl

private theorem firstterminal_lab (level : Nat) (st : SearchSt) :
    (firstterminal level st).lab = st.lab := rfl

private theorem firstterminal_ptn (level : Nat) (st : SearchSt) :
    (firstterminal level st).ptn = st.ptn := rfl

private theorem firstterminal_canonlab (level : Nat) (st : SearchSt) :
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

private theorem recover_lab (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).lab = st.lab := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.lab, ite_self]

private theorem recover_canonlab (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).canonlab = st.canonlab := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlab, ite_self]

private theorem recover_ptn_foldl (n inf level : Nat)
    (st : SearchSt) :
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

private theorem recover_ptn (n inf level : Nat) (st : SearchSt)
    (q : Nat) :
    (recover n inf level st).ptn[q]! =
      if q < n ∧ st.ptn[q]! > level then inf else st.ptn[q]! := by
  rw [recover_ptn_foldl, foldl_reopen_getElem]

private theorem recover_ptn_size (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).ptn.size = st.ptn.size := by
  rw [recover_ptn_foldl, foldl_reopen_size]

private theorem processnode_lab (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.lab = st.lab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.lab), pushAuto_lab,
    ite_self]

private theorem processnode_ptn (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.ptn = st.ptn := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.ptn), pushAuto_ptn,
    ite_self]

/-- `processnode` either keeps `canonlab` or installs the current
labelling. -/
private theorem processnode_canonlab (ctx : Ctx)
    (level numcells : Nat) (st : SearchSt) :
    (processnode ctx level numcells st).2.canonlab = st.canonlab ∨
      (processnode ctx level numcells st).2.canonlab = st.lab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.canonlab),
    pushAuto_canonlab]
  refine ite_or (P := fun y => y = st.canonlab ∨ y = st.lab) ?_ ?_ <;>
  repeat' first
  | exact Or.inl rfl
  | exact Or.inr rfl
  | apply ite_or (P := fun y => y = st.canonlab ∨ y = st.lab)

/-! # Pruning shrinks the target cell -/

private theorem elem_and_left {a b v : Nat}
    (h : elem (a &&& b) v = true) : elem a v = true := by
  have h1 : (a &&& b).testBit v = true := h
  simp only [Nat.testBit_and, Bool.and_eq_true] at h1
  exact h1.1

private theorem shortprune_subset {tcell : Nat} {st : SearchSt}
    {v : Nat} (h : elem (shortprune tcell st) v = true) :
    elem tcell v = true := by
  rw [shortprune] at h
  rcases hb : st.autos.back? with _ | pair
  · rw [hb] at h
    exact h
  · rw [hb] at h
    exact elem_and_left h

private theorem longprune_subset {fixedpts : Nat} {v : Nat} :
    ∀ {autos : List (Nat × Nat)} {tcell : Nat},
      elem (autos.foldl
        (fun tcell (pair : Nat × Nat) =>
          if fixedpts &&& pair.1 == fixedpts then tcell &&& pair.2
          else tcell) tcell) v = true →
      elem tcell v = true
  | [], _, h => h
  | pair :: autos, tcell, h => by
    rw [List.foldl_cons] at h
    have h1 := longprune_subset (autos := autos) h
    split at h1
    · exact elem_and_left h1
    · exact h1

private theorem longprune_mem {tcell fixedpts : Nat}
    {autos : Array (Nat × Nat)} {v : Nat}
    (h : elem (longprune tcell fixedpts autos) v = true) :
    elem tcell v = true := by
  rw [longprune, ← Array.foldl_toList] at h
  exact longprune_subset h

/-- `nextElem` yields only from a nonempty set. -/
private theorem nextElem_some_ne_zero {s : Nat} {pos : Option Nat}
    {v : Nat} (h : nextElem s pos = some v) : s ≠ 0 := by
  rintro rfl
  rw [nextElem.eq_def] at h
  rcases pos with _ | p
  · simp at h
  · simp [Nat.zero_shiftRight, Nat.zero_shiftLeft] at h

end Hex.GraphIso.Nauty
