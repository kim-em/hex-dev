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

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

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

private theorem pushAuto_firstlab (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).firstlab = st.firstlab := by
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

/-! # The quartet induction -/

variable {n k : Nat}

/-- One `recover` step satisfies the exit contract at its own
level. -/
theorem recover_out {G : Colored n k} {level : Nat}
    {st : SearchSt} (hlev : level + 1 < n + 2)
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

private theorem otherNodePrep_lab (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).lab = st.lab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.lab, ite_self]

private theorem otherNodePrep_ptn (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).ptn = st.ptn := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.ptn, ite_self]

private theorem otherNodePrep_canonlab (level code : Nat)
    (st : SearchSt) :
    (otherNodePrep level code st).canonlab = st.canonlab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlab, ite_self]

private theorem otherNodePrep_firstlab (level code : Nat)
    (st : SearchSt) :
    (otherNodePrep level code st).firstlab = st.firstlab := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.firstlab, ite_self]

private theorem processnode_firstlab (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.firstlab = st.firstlab := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.firstlab),
    pushAuto_firstlab, ite_self]

/-- `processnode` preserves the node invariant, installing at most a
reached labelling. -/
theorem processnode_searchOk {G : Colored n k} {ctx : Ctx}
    {level nc pnl pnn : Nat} {st4 st5 : SearchSt}
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
theorem canonlab_or_of {G : Colored n k} {ctx : Ctx}
    {pnl pnn : Nat} {st4 stO : SearchSt} {cl rl : Array Nat}
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
private theorem firstlab_eq_of {ctx : Ctx} {pnl pnn : Nat}
    {st4 stO : SearchSt} {fl : Array Nat}
    (hO : stO.firstlab = (processnode ctx pnl pnn st4).2.firstlab)
    (hf : st4.firstlab = fl) : stO.firstlab = fl := by
  exact hO.trans ((processnode_firstlab ctx pnl pnn st4).trans hf)

/-- Transport the cell-permutation form of the `processnode` canonical
store dichotomy through a state update. -/
private theorem canonStore_or_of {ctx : Ctx} {pnl pnn lev : Nat}
    {st4 stO : SearchSt} {cl rl lab ptn : Array Nat}
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

mutual

theorem firstPathNode_ok (G : Colored n k) (ctx : Ctx)
    (hn : ctx.n = n) (inf : Nat) (hinf : inf = n + 2)
    (tcLevel : Nat) (hn0 : 0 < n)
    (fuel level numcells : Nat) (st : SearchSt)
    (hok : SearchOk G level numcells st) (h1 : 1 ≤ level)
    (hfuel : n + 1 ≤ level + fuel) :
    SearchOut G (level - 1) level st
        (firstPathNode ctx inf tcLevel fuel level numcells st).2 ∧
      ((∀ v, v < n → st.orbits[v]! = v) →
        (firstPathNode ctx inf tcLevel fuel level numcells
            st).2.canonlab.size = n ∧
          CellsReach G (firstPathNode ctx inf tcLevel fuel level
            numcells st).2.canonlab) := by
  match fuel with
  | 0 =>
    exfalso
    have hb := bcount_le st.ptn level n
    have hc := hok.bc
    omega
  | fuel + 1 =>
    rw [firstPathNode]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
    have hend := searchOk_end hn0 hok h1
    have hnn' : ctx.n = st.ptn.size := by
      rw [hok.ptnSize, hn]
    have hls : st.lab.size = st.ptn.size := by
      rw [hok.labSize, hok.ptnSize]
    have hRinv := refine_refInv (ctx := ctx) (level := level)
      (lab := st.lab) (ptn := st.ptn) (active := st.active)
      (numcells := numcells) (by omega) hls hend
    have hRreach : CellsReach G
        (refine ctx level st.lab st.ptn st.active numcells).lab :=
      refine_cellsReach hn hn0 hok.reach hok.labSize hok.ptnSize
        hend (fun q hq => Nat.le_trans (hok.init1 q hq) h1)
    have hRsize : (refine ctx level st.lab st.ptn st.active
        numcells).lab.size = n := by
      rw [hRinv.labSize, hok.labSize]
    have hRend : (refine ctx level st.lab st.ptn st.active
        numcells).ptn[(refine ctx level st.lab st.ptn st.active
          numcells).ptn.size - 1]! ≤ level := by
      rw [hRinv.ptnSize]
      rw [refine_frozen hnn' hls hend hend]
      exact hend
    rcases Decidable.em ((refine ctx level st.lab st.ptn st.active
        numcells).numcells ≠ ctx.n) with hnl | hnl
    · -- an internal node: individualize down the target cell
      simp only [ite_eq_left hnl,
        beq_eq_false_iff_ne.mpr hnl, Bool.false_eq_true, ite_false]
      have hokR := refine_searchOk (st2 := { st with
          lab := (refine ctx level st.lab st.ptn st.active
            numcells).lab,
          ptn := (refine ctx level st.lab st.ptn st.active
            numcells).ptn,
          active := (refine ctx level st.lab st.ptn st.active
            numcells).active,
          firstcode := st.firstcode.set! level (refine ctx level
            st.lab st.ptn st.active numcells).longcode,
          numnodes := st.numnodes + 1 })
        hn hn0 hok h1 rfl rfl (Or.inl rfl)
      have hlive : bcount (refine ctx level st.lab st.ptn st.active
          numcells).ptn level ctx.n < ctx.n := by
        have h0 := hokR.count
        dsimp only at h0
        have h2 := bcount_le (refine ctx level st.lab st.ptn
          st.active numcells).ptn level n
        have h3 : (refine ctx level st.lab st.ptn st.active
            numcells).numcells ≠ n := by
          rw [← hn]
          exact hnl
        rw [hn]
        omega
      obtain ⟨tcw, lenw, hmk, hicw, hlen2w, hrangew⟩ :=
        maketargetcell_open (lab := (refine ctx level st.lab st.ptn
          st.active numcells).lab) (tcLevel := tcLevel)
          (hint := (-1 : Int)) h1
          (by rw [hRinv.ptnSize, ← hnn']) hRend hlive
      rw [hmk]
      dsimp only
      have hrangen : tcw + lenw ≤ n := by
        rw [← hn]
        exact hrangew
      have hWmem : ∀ v : Nat,
          elem (worksetOf (refine ctx level st.lab st.ptn st.active
            numcells).lab tcw (tcw + lenw - 1)) v = true →
          v ∈ segN (refine ctx level st.lab st.ptn st.active
            numcells).lab tcw lenw := by
        intro v hv
        have h0 : ((segN (refine ctx level st.lab st.ptn st.active
            numcells).lab tcw (tcw + lenw - 1 + 1 - tcw)).any
              (· == v)) = true := by
          rw [← testBit_worksetOf]
          exact hv
        rw [show tcw + lenw - 1 + 1 - tcw = lenw from by omega] at h0
        rcases List.any_eq_true.mp h0 with ⟨x, hx, hbeq⟩
        have : x = v := by simpa using hbeq
        rw [← this]
        exact hx
      have hW0 : worksetOf (refine ctx level st.lab st.ptn st.active
          numcells).lab tcw (tcw + lenw - 1) ≠ 0 := by
        refine elem_ne_zero (v := (refine ctx level st.lab st.ptn
          st.active numcells).lab[tcw]!) ?_
        have h0 : ((segN (refine ctx level st.lab st.ptn st.active
            numcells).lab tcw (tcw + lenw - 1 + 1 - tcw)).any
              (· == (refine ctx level st.lab st.ptn st.active
                numcells).lab[tcw]!)) = true := by
          rw [show tcw + lenw - 1 + 1 - tcw = lenw from by omega]
          refine List.any_eq_true.mpr ⟨(refine ctx level st.lab
            st.ptn st.active numcells).lab[tcw]!, ?_, by simp⟩
          exact mem_segN_iff.mpr ⟨0, by omega, by rw [Nat.add_zero]⟩
        rw [← testBit_worksetOf] at h0
        exact h0
      have hsome : nextElem (worksetOf (refine ctx level st.lab
          st.ptn st.active numcells).lab tcw (tcw + lenw - 1)) none =
          some ((nextElem (worksetOf (refine ctx level st.lab st.ptn
            st.active numcells).lab tcw (tcw + lenw - 1))
              none).getD 0) := by
        rw [nextElem]
        rw [ite_eq_right hW0]
        rfl
      have hcont : ∀ st5 : SearchSt,
          st5.lab = (refine ctx level st.lab st.ptn st.active
            numcells).lab →
          st5.ptn = (refine ctx level st.lab st.ptn st.active
            numcells).ptn →
          st5.firstlab = st.firstlab →
          st5.canonlab = st.canonlab →
          st5.orbits = st.orbits →
          (SearchOut G (level - 1) level st
            (firstChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
              (refine ctx level st.lab st.ptn st.active
                numcells).numcells tcw
              ((nextElem (worksetOf (refine ctx level st.lab st.ptn
                st.active numcells).lab tcw (tcw + lenw - 1))
                  none).getD 0)
              (nextElem (worksetOf (refine ctx level st.lab st.ptn
                st.active numcells).lab tcw (tcw + lenw - 1)) none)
              (worksetOf (refine ctx level st.lab st.ptn st.active
                numcells).lab tcw (tcw + lenw - 1)) 0 st5).2.2) ∧
          ((∀ v, v < n → st.orbits[v]! = v) →
            ((firstChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
              (refine ctx level st.lab st.ptn st.active
                numcells).numcells tcw
              ((nextElem (worksetOf (refine ctx level st.lab st.ptn
                st.active numcells).lab tcw (tcw + lenw - 1))
                  none).getD 0)
              (nextElem (worksetOf (refine ctx level st.lab st.ptn
                st.active numcells).lab tcw (tcw + lenw - 1)) none)
              (worksetOf (refine ctx level st.lab st.ptn st.active
                numcells).lab tcw (tcw + lenw - 1)) 0
                st5).2.2.canonlab.size = n ∧
              CellsReach G (firstChildLoop ctx inf tcLevel fuel
                (ctx.n + 1) level (refine ctx level st.lab st.ptn
                  st.active numcells).numcells tcw
                ((nextElem (worksetOf (refine ctx level st.lab
                  st.ptn st.active numcells).lab tcw
                    (tcw + lenw - 1)) none).getD 0)
                (nextElem (worksetOf (refine ctx level st.lab st.ptn
                  st.active numcells).lab tcw (tcw + lenw - 1)) none)
                (worksetOf (refine ctx level st.lab st.ptn st.active
                  numcells).lab tcw (tcw + lenw - 1)) 0
                  st5).2.2.canonlab)) := by
        intro st5 h5l h5p h5f h5c h5o
        have hok5 := refine_searchOk (st2 := st5) hn hn0 hok h1 h5l
          h5p (Or.inl h5c)
        have hloop := firstChildLoop_ok G ctx hn inf hinf tcLevel
          hn0 fuel (ctx.n + 1) level
          (refine ctx level st.lab st.ptn st.active numcells).numcells
          tcw
          ((nextElem (worksetOf (refine ctx level st.lab st.ptn
            st.active numcells).lab tcw (tcw + lenw - 1)) none).getD
              0)
          (nextElem (worksetOf (refine ctx level st.lab st.ptn
            st.active numcells).lab tcw (tcw + lenw - 1)) none)
          (worksetOf (refine ctx level st.lab st.ptn st.active
            numcells).lab tcw (tcw + lenw - 1)) 0 st5 lenw hok5 h1
          (by omega)
          (fun _ => ⟨by rw [h5p]; exact hicw, hlen2w, hrangen⟩)
          (fun v hv => by rw [h5l]; exact hWmem v hv)
          (fun v hv => nextElem_mem hv)
        refine ⟨refine_loop_out hn hn0 hok h1 h5l h5p
          (Or.inl h5f) (Or.inl h5c) (Or.inl h5c) hloop.1,
          fun hid => ?_⟩
        exact hloop.2 (fun v hv => by rw [h5o]; exact hid v hv)
          hsome (by omega)
      rcases Decidable.em (st.noncheaplevel ≥ level ∧
          ¬cheapautom (refine ctx level st.lab st.ptn st.active
            numcells).ptn level ctx.n = true) with hca | hca
      · simp only [ite_eq_left hca]
        split
        · exact hcont _ rfl rfl rfl rfl rfl
        · refine ⟨ite_or (P := fun y : Int × SearchSt =>
              SearchOut G (level - 1) level st y.2) ?_ ?_,
            fun hid => ite_or (P := fun y : Int × SearchSt =>
              y.2.canonlab.size = n ∧
                CellsReach G y.2.canonlab) ?_ ?_⟩
          · exact SearchOut.congr (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              noncheaplevel := level + 1,
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).1
              rfl rfl rfl rfl
          · exact (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              noncheaplevel := level + 1,
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).1
          · exact (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              noncheaplevel := level + 1,
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).2 hid
          · exact (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              noncheaplevel := level + 1,
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).2 hid
      · simp only [ite_eq_right hca]
        split
        · exact hcont _ rfl rfl rfl rfl rfl
        · refine ⟨ite_or (P := fun y : Int × SearchSt =>
              SearchOut G (level - 1) level st y.2) ?_ ?_,
            fun hid => ite_or (P := fun y : Int × SearchSt =>
              y.2.canonlab.size = n ∧
                CellsReach G y.2.canonlab) ?_ ?_⟩
          · exact SearchOut.congr (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).1
              rfl rfl rfl rfl
          · exact (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).1
          · exact (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).2 hid
          · exact (hcont { st with
              lab := (refine ctx level st.lab st.ptn st.active
                numcells).lab,
              ptn := (refine ctx level st.lab st.ptn st.active
                numcells).ptn,
              active := (refine ctx level st.lab st.ptn st.active
                numcells).active,
              firstcode := st.firstcode.set! level (refine ctx level
                st.lab st.ptn st.active numcells).longcode,
              firsttc := st.firsttc.set! level (Int.ofNat tcw),
              numnodes := st.numnodes + 1,
              tctotal := st.tctotal + lenw } rfl rfl rfl rfl rfl).2 hid
    · -- the refined partition is discrete: this node is the leaf
      have hleaf : ((refine ctx level st.lab st.ptn st.active
          numcells).numcells == ctx.n) = true := by
        rcases Decidable.em ((refine ctx level st.lab st.ptn
          st.active numcells).numcells = ctx.n) with he | he
        · simpa using he
        · exact absurd he (by simpa using hnl)
      simp only [ite_eq_right hnl, hleaf, ite_true]
      refine ⟨refine_loop_out hn hn0 hok h1 rfl rfl
        (Or.inr ⟨hRinv.labSize, hRinv.perm⟩)
        (Or.inr ⟨hRinv.labSize, hRinv.perm⟩)
        (Or.inr ⟨hRsize, hRreach⟩)
        (SearchOut.refl G level level hRreach), fun _ =>
        ⟨hRsize, hRreach⟩⟩
termination_by (fuel, 0, 0)

theorem firstChildLoop_ok (G : Colored n k) (ctx : Ctx)
    (hn : ctx.n = n) (inf : Nat) (hinf : inf = n + 2)
    (tcLevel : Nat) (hn0 : 0 < n)
    (fuel cfuel level numcells tc tv1 : Nat) (tv? : Option Nat)
    (tcell0 index0 : Nat) (st0 : SearchSt) (len : Nat)
    (hok : SearchOk G level numcells st0) (h1 : 1 ≤ level)
    (hfuel : n + 1 ≤ level + 1 + fuel)
    (hcell : tcell0 ≠ 0 →
      IsCell st0.ptn level tc len ∧ 2 ≤ len ∧ tc + len ≤ n)
    (hmem : ∀ v, elem tcell0 v = true → v ∈ segN st0.lab tc len)
    (htv : ∀ v, tv? = some v → elem tcell0 v = true) :
    SearchOut G level level st0
        (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc
          tv1 tv? tcell0 index0 st0).2.2 ∧
      ((∀ v, v < n → st0.orbits[v]! = v) → tv? = some tv1 →
        1 ≤ cfuel →
        (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc
            tv1 tv? tcell0 index0 st0).2.2.canonlab.size = n ∧
          CellsReach G
            (firstChildLoop ctx inf tcLevel fuel cfuel level numcells
              tc tv1 tv? tcell0 index0 st0).2.2.canonlab) := by
  match cfuel, tv? with
  | 0, _ =>
    rw [firstChildLoop]
    exact ⟨SearchOut.refl G level level hok.reach,
      fun _ _ hcontra => by omega⟩
  | cfuel + 1, none =>
    rw [firstChildLoop]
    case x_1 => omega
    exact ⟨SearchOut.refl G level level hok.reach,
      fun _ hcontra => by cases hcontra⟩
  | cfuel + 1, some tv =>
    rw [firstChildLoop]
    have htvmem0 : elem tcell0 tv = true := htv tv rfl
    obtain ⟨hic, hlen2, hrange⟩ := hcell (elem_ne_zero htvmem0)
    obtain ⟨o, ho, hoeq⟩ := mem_segN_iff.mp (hmem tv htvmem0)
    have htvn : tv < n := by
      rw [← hoeq]
      exact cellsReach_lt hok.reach (tc + o) (by omega)
    rcases horb : (st0.orbits[tv]! == tv) with _ | _
    · -- pruned iteration: nothing changes but the head pointer
      have htail := fun idx =>
        firstChildLoop_ok G ctx hn inf hinf tcLevel hn0 fuel cfuel
          level numcells tc tv1 (nextElem tcell0 (some tv)) tcell0 idx
          st0 len hok h1 hfuel hcell hmem
          (fun v hv => nextElem_mem hv)
      simp only [horb, Bool.false_eq_true, ite_false, Id.run_pure,
        apply_ite Id.run]
      rcases hidx : (st0.orbits[tv]! == tv1) with _ | _ <;>
        simp only [hidx, Bool.false_eq_true, ite_false, ite_true] <;>
        exact ⟨(htail _).1, fun hid _ _ => by
          have hb : (st0.orbits[tv]! == tv) = true := by
            rw [hid tv htvn]
            simp
          rw [horb] at hb
          cases hb⟩
    · -- live iteration
      subst hoeq
      simp only [horb, ite_true, Id.run_bind, Id.run_pure,
        apply_ite Id.run]
      have hlevn : level ≤ n := Nat.le_trans hok.bc (bcount_le _ _ _)
      have hCok := breakout_searchOk (st' := { st0 with
          lab := (breakout st0.lab st0.ptn (level + 1) tc
            st0.lab[tc + o]!).1,
          ptn := (breakout st0.lab st0.ptn (level + 1) tc
            st0.lab[tc + o]!).2.1,
          active := (breakout st0.lab st0.ptn (level + 1) tc
            st0.lab[tc + o]!).2.2,
          fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
          cosetindex := st0.lab[tc + o]! })
        hn0 hok h1 hic hlen2 hrange ho rfl
        (breakout_ptn st0.lab st0.ptn (level + 1) tc
          st0.lab[tc + o]!) rfl
      rcases htv1 : (st0.lab[tc + o]! == tv1) with _ | _
      · -- off the first path: an `otherNode` child
        simp only [htv1, Bool.false_eq_true, ite_false]
        have hDout := (otherNode_ok G ctx hn inf hinf tcLevel hn0
          fuel (level + 1) (numcells + 1) _ hCok (by omega)
          (by omega)).mono (B' := level) (by omega)
        have hbase := breakout_child_out hn0 hok h1 hic hlen2 hrange
          ho hDout rfl (breakout_ptn st0.lab st0.ptn (level + 1) tc
            st0.lab[tc + o]!) rfl rfl
        have hnotv1 : ¬ st0.lab[tc + o]! = tv1 := by
          intro he
          rw [he] at htv1
          simp at htv1
        rcases Decidable.em ((otherNode ctx inf tcLevel fuel
            (level + 1) (numcells + 1) { st0 with
              lab := (breakout st0.lab st0.ptn (level + 1) tc
                st0.lab[tc + o]!).1,
              ptn := (breakout st0.lab st0.ptn (level + 1) tc
                st0.lab[tc + o]!).2.1,
              active := (breakout st0.lab st0.ptn (level + 1) tc
                st0.lab[tc + o]!).2.2,
              fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
              cosetindex := st0.lab[tc + o]! }).1 <
            Int.ofNat level) with hrt | hrt
        · simp only [ite_eq_left hrt]
          exact ⟨hbase.congr rfl rfl rfl rfl,
            fun hid heq _ => absurd (by injection heq) hnotv1⟩
        · simp only [ite_eq_right hrt]
          have hcont : ∀ (tcell' idx : Nat) (stG : SearchSt),
              stG.lab = (otherNode ctx inf tcLevel fuel (level + 1)
                (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.lab →
              stG.ptn = (otherNode ctx inf tcLevel fuel (level + 1)
                (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.ptn →
              stG.firstlab = (otherNode ctx inf tcLevel fuel
                (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.firstlab →
              stG.canonlab = (otherNode ctx inf tcLevel fuel
                (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.canonlab →
              (∀ v, elem tcell' v = true → elem tcell0 v = true) →
              SearchOut G level level st0
                (firstChildLoop ctx inf tcLevel fuel cfuel level
                  numcells tc tv1
                  (nextElem tcell' (some st0.lab[tc + o]!)) tcell'
                  idx (recover ctx.n inf level stG)).2.2 := by
            intro tcell' idx stG hgl hgp hgf hgc hsub
            have houtG : SearchOut G level level st0 stG :=
              hbase.congr hgl hgp hgf hgc
            have hrecout : SearchOut G level level stG
                (recover ctx.n inf level stG) := by
              rw [hn, hinf]
              exact recover_out (by omega) houtG.reach
            have hout0R := houtG.trans hrecout
            have hokR : SearchOk G level numcells
                (recover ctx.n inf level stG) := by
              refine searchOk_of_out hok h1 hout0R ?_
              intro q hqn
              rw [hn, hinf, recover_ptn]
              rcases Decidable.em (q < n ∧ stG.ptn[q]! > level)
                with hc | hc
              · rw [ite_eq_left hc]
                exact Or.inr rfl
              · rw [ite_eq_right hc]
                left
                rcases Nat.lt_or_ge level stG.ptn[q]! with hgt | hle
                · exact absurd ⟨hqn, hgt⟩ hc
                · exact hle
            have htail := firstChildLoop_ok G ctx hn inf hinf tcLevel
              hn0 fuel cfuel level numcells tc tv1
              (nextElem tcell' (some st0.lab[tc + o]!)) tcell' idx
              (recover ctx.n inf level stG) len hokR h1 hfuel
              (fun _ => ⟨isCell_of_low hout0R.low hic, hlen2,
                hrange⟩)
              (fun v hv => (hout0R.perm tc len hic).mem_iff.mp
                (hmem v (hsub v hv)))
              (fun v hv => nextElem_mem hv)
            exact hout0R.trans htail.1
          rcases hnsp : ((otherNode ctx inf tcLevel fuel (level + 1)
              (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.needshortprune)
            with _ | _
          · simp only [hnsp, Bool.false_eq_true, ite_false]
            refine ⟨ite_or
                (P := fun x : Option Int × Nat × SearchSt =>
                  SearchOut G level level st0 x.2.2) ?_ ?_,
              fun hid heq _ => absurd (by injection heq) hnotv1⟩
            · refine hcont _ _ _ ?_ ?_ ?_ ?_ ?_ <;>
                first | rfl | exact fun v hv => hv
            · refine hcont _ _ _ ?_ ?_ ?_ ?_ ?_ <;>
                first | rfl | exact fun v hv => hv
          · simp only [hnsp, ite_true]
            refine ⟨ite_or
                (P := fun x : Option Int × Nat × SearchSt =>
                  SearchOut G level level st0 x.2.2) ?_ ?_,
              fun hid heq _ => absurd (by injection heq) hnotv1⟩
            · refine hcont _ _ _ ?_ ?_ ?_ ?_ ?_ <;>
                first | rfl | exact fun v hv => shortprune_subset hv
            · refine hcont _ _ _ ?_ ?_ ?_ ?_ ?_ <;>
                first | rfl | exact fun v hv => shortprune_subset hv
      · -- on the first path: the `firstPathNode` child installs
        simp only [htv1, ite_true]
        have htveq : st0.lab[tc + o]! = tv1 := by simpa using htv1
        have hDfull := firstPathNode_ok G ctx hn inf hinf tcLevel hn0
          fuel (level + 1) (numcells + 1) _ hCok (by omega)
          (by omega)
        have hDout := hDfull.1.mono (B' := level) (by omega)
        have hbase := breakout_child_out hn0 hok h1 hic hlen2 hrange
          ho hDout rfl (breakout_ptn st0.lab st0.ptn (level + 1) tc
            st0.lab[tc + o]!) rfl rfl
        rcases Decidable.em ((firstPathNode ctx inf tcLevel fuel
            (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).1 <
            Int.ofNat level) with hrt | hrt
        · simp only [ite_eq_left hrt]
          exact ⟨hbase.congr rfl rfl rfl rfl,
            fun hid heq _ => hDfull.2 (fun v hv => hid v hv)⟩
        · simp only [ite_eq_right hrt]
          have hcont : ∀ (tcell' idx : Nat) (stG : SearchSt),
              stG.lab = (firstPathNode ctx inf tcLevel fuel
                (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.lab →
              stG.ptn = (firstPathNode ctx inf tcLevel fuel
                (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.ptn →
              stG.firstlab = (firstPathNode ctx inf tcLevel fuel
                (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.firstlab →
              stG.canonlab = (firstPathNode ctx inf tcLevel fuel
                (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.canonlab →
              (∀ v, elem tcell' v = true → elem tcell0 v = true) →
              SearchOut G level level st0
                (firstChildLoop ctx inf tcLevel fuel cfuel level
                  numcells tc tv1
                  (nextElem tcell' (some st0.lab[tc + o]!)) tcell'
                  idx (recover ctx.n inf level stG)).2.2 ∧
              (((firstPathNode ctx inf tcLevel fuel (level + 1)
                    (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.canonlab.size = n ∧
                  CellsReach G (firstPathNode ctx inf tcLevel fuel
                    (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.canonlab) →
                (firstChildLoop ctx inf tcLevel fuel cfuel level
                    numcells tc tv1
                    (nextElem tcell' (some st0.lab[tc + o]!)) tcell'
                    idx (recover ctx.n inf level
                      stG)).2.2.canonlab.size = n ∧
                  CellsReach G (firstChildLoop ctx inf tcLevel fuel
                    cfuel level numcells tc tv1
                    (nextElem tcell' (some st0.lab[tc + o]!)) tcell'
                    idx (recover ctx.n inf level
                      stG)).2.2.canonlab) := by
            intro tcell' idx stG hgl hgp hgf hgc hsub
            have houtG : SearchOut G level level st0 stG :=
              hbase.congr hgl hgp hgf hgc
            have hrecout : SearchOut G level level stG
                (recover ctx.n inf level stG) := by
              rw [hn, hinf]
              exact recover_out (by omega) houtG.reach
            have hout0R := houtG.trans hrecout
            have hokR : SearchOk G level numcells
                (recover ctx.n inf level stG) := by
              refine searchOk_of_out hok h1 hout0R ?_
              intro q hqn
              rw [hn, hinf, recover_ptn]
              rcases Decidable.em (q < n ∧ stG.ptn[q]! > level)
                with hc | hc
              · rw [ite_eq_left hc]
                exact Or.inr rfl
              · rw [ite_eq_right hc]
                left
                rcases Nat.lt_or_ge level stG.ptn[q]! with hgt | hle
                · exact absurd ⟨hqn, hgt⟩ hc
                · exact hle
            have htail := firstChildLoop_ok G ctx hn inf hinf tcLevel
              hn0 fuel cfuel level numcells tc tv1
              (nextElem tcell' (some st0.lab[tc + o]!)) tcell' idx
              (recover ctx.n inf level stG) len hokR h1 hfuel
              (fun _ => ⟨isCell_of_low hout0R.low hic, hlen2,
                hrange⟩)
              (fun v hv => (hout0R.perm tc len hic).mem_iff.mp
                (hmem v (hsub v hv)))
              (fun v hv => nextElem_mem hv)
            refine ⟨hout0R.trans htail.1, fun hinst => ?_⟩
            rcases htail.1.canon with hcc | hcc
            · rw [hcc, recover_canonlab, hgc]
              exact hinst
            · exact hcc
          have hDinstalled := hDfull.2
          rcases hnsp : ((firstPathNode ctx inf tcLevel fuel
              (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]!,
                  cosetindex := st0.lab[tc + o]! }).2.needshortprune)
            with _ | _
          · simp only [hnsp, Bool.false_eq_true, ite_false]
            refine ⟨ite_or
                (P := fun x : Option Int × Nat × SearchSt =>
                  SearchOut G level level st0 x.2.2) ?_ ?_,
              fun hid heq _ => ite_or
                (P := fun x : Option Int × Nat × SearchSt =>
                  x.2.2.canonlab.size = n ∧
                    CellsReach G x.2.2.canonlab) ?_ ?_⟩
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).1 <;>
                first | rfl | exact fun v hv => hv
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).1 <;>
                first | rfl | exact fun v hv => hv
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).2
                (hDinstalled (fun v hv => hid v hv)) <;>
                first | rfl | exact fun v hv => hv
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).2
                (hDinstalled (fun v hv => hid v hv)) <;>
                first | rfl | exact fun v hv => hv
          · simp only [hnsp, ite_true]
            refine ⟨ite_or
                (P := fun x : Option Int × Nat × SearchSt =>
                  SearchOut G level level st0 x.2.2) ?_ ?_,
              fun hid heq _ => ite_or
                (P := fun x : Option Int × Nat × SearchSt =>
                  x.2.2.canonlab.size = n ∧
                    CellsReach G x.2.2.canonlab) ?_ ?_⟩
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).1 <;>
                first | rfl | exact fun v hv => shortprune_subset hv
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).1 <;>
                first | rfl | exact fun v hv => shortprune_subset hv
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).2
                (hDinstalled (fun v hv => hid v hv)) <;>
                first | rfl | exact fun v hv => shortprune_subset hv
            · refine (hcont _ _ _ ?_ ?_ ?_ ?_ ?_).2
                (hDinstalled (fun v hv => hid v hv)) <;>
                first | rfl | exact fun v hv => shortprune_subset hv
termination_by (fuel, 1, cfuel)

theorem otherNode_ok (G : Colored n k) (ctx : Ctx)
    (hn : ctx.n = n) (inf : Nat) (hinf : inf = n + 2)
    (tcLevel : Nat) (hn0 : 0 < n)
    (fuel level numcells : Nat) (st : SearchSt)
    (hok : SearchOk G level numcells st) (h1 : 1 ≤ level)
    (hfuel : n + 1 ≤ level + fuel) :
    SearchOut G (level - 1) level st
      (otherNode ctx inf tcLevel fuel level numcells st).2 := by
  match fuel with
  | 0 =>
    exfalso
    have hb := bcount_le st.ptn level n
    have hc := hok.bc
    omega
  | fuel + 1 =>
    rw [otherNode]
    simp only [Id.run_bind, Id.run_pure]
    have hend := searchOk_end hn0 hok h1
    have hnn' : ctx.n = st.ptn.size := by
      rw [hok.ptnSize, hn]
    have hls : st.lab.size = st.ptn.size := by
      rw [hok.labSize, hok.ptnSize]
    have hRinv := refine_refInv (ctx := ctx) (level := level)
      (lab := st.lab) (ptn := st.ptn) (active := st.active)
      (numcells := numcells) (by omega) hls hend
    have hRreach : CellsReach G
        (refine ctx level st.lab st.ptn st.active numcells).lab :=
      refine_cellsReach hn hn0 hok.reach hok.labSize hok.ptnSize
        hend (fun q hq => Nat.le_trans (hok.init1 q hq) h1)
    have hRsize : (refine ctx level st.lab st.ptn st.active
        numcells).lab.size = n := by
      rw [hRinv.labSize, hok.labSize]
    have hRend : (refine ctx level st.lab st.ptn st.active
        numcells).ptn[(refine ctx level st.lab st.ptn st.active
          numcells).ptn.size - 1]! ≤ level := by
      rw [hRinv.ptnSize]
      rw [refine_frozen hnn' hls hend hend]
      exact hend
    have hdi := processnode_canonlab ctx level
      (refine ctx level st.lab st.ptn st.active numcells).numcells
    generalize hPR : otherNodePrep level (refine ctx level st.lab
      st.ptn st.active numcells).longcode
      { st with
        numnodes := st.numnodes + 1,
        lab := (refine ctx level st.lab st.ptn st.active
          numcells).lab,
        ptn := (refine ctx level st.lab st.ptn st.active
          numcells).ptn,
        active := (refine ctx level st.lab st.ptn st.active
          numcells).active } = PR
    have hPRl : PR.lab = (refine ctx level st.lab st.ptn st.active
        numcells).lab := by
      rw [← hPR, otherNodePrep_lab]
    have hPRp : PR.ptn = (refine ctx level st.lab st.ptn st.active
        numcells).ptn := by
      rw [← hPR, otherNodePrep_ptn]
    have hPRc : PR.canonlab = st.canonlab := by
      rw [← hPR, otherNodePrep_canonlab]
    have hPRf : PR.firstlab = st.firstlab := by
      rw [← hPR, otherNodePrep_firstlab]
    have hreturn : ∀ st7 : SearchSt,
        st7.lab = (refine ctx level st.lab st.ptn st.active
          numcells).lab →
        st7.ptn = (refine ctx level st.lab st.ptn st.active
          numcells).ptn →
        (st7.firstlab = st.firstlab ∨
          (st7.firstlab.size = st.lab.size ∧
            cellsPerm st.ptn level st.lab st7.firstlab)) →
        (st7.canonlab = st.canonlab ∨
          (st7.canonlab.size = st.lab.size ∧
            cellsPerm st.ptn level st.lab st7.canonlab)) →
        (st7.canonlab = st.canonlab ∨
          (st7.canonlab.size = n ∧ CellsReach G st7.canonlab)) →
        SearchOut G (level - 1) level st st7 := by
      intro st7 h7l h7p h7f h7c h7reach
      exact refine_loop_out hn hn0 hok h1 h7l h7p h7f h7c h7reach
        (SearchOut.refl G level level (by
          rw [h7l]
          exact hRreach))
    rcases Decidable.em ((refine ctx level st.lab st.ptn st.active
        numcells).numcells < ctx.n ∧
        ((PR.eqlevFirst == level) = true ∨ PR.compCanon ≥ 0))
      with hD | hD
    case inl =>
      rw [ite_eq_left hD]
      have hcount0 := refine_bcount (ctx := ctx) (level := level)
        (lab := st.lab) (ptn := st.ptn) (active := st.active)
        (numcells := numcells) hnn' hls hend
      have hcnt := hok.count
      have hD1 := hD.1
      have hlive : bcount (refine ctx level st.lab st.ptn st.active
          numcells).ptn level ctx.n < ctx.n := by
        rw [hn] at hcount0 ⊢
        rw [hn] at hD1
        omega
      rcases Decidable.em (PR.compCanon < 0) with hCC | hCC
      case inl =>
        rw [ite_eq_left hCC]
        obtain ⟨tcwA, lenwA, hmkA, hicA, hlen2A, hrangeA⟩ :=
          maketargetcell_open (lab := PR.lab) (ptn := PR.ptn)
            (tcLevel := tcLevel) (hint := PR.firsttc[level]!) h1
            (by rw [hPRp, hRinv.ptnSize, ← hnn'])
            (by rw [hPRp]; exact hRend)
            (by rw [hPRp]; exact hlive)
        rw [hPRp] at hicA
        rw [hmkA]
        dsimp only
        have hrangenA : tcwA + lenwA ≤ n := by
          rw [← hn]
          exact hrangeA
        have hWmemA : ∀ v : Nat,
            elem (worksetOf PR.lab tcwA (tcwA + lenwA - 1)) v =
              true →
            v ∈ segN (refine ctx level st.lab st.ptn st.active
              numcells).lab tcwA lenwA := by
          intro v hv
          have h0 : ((segN PR.lab tcwA
              (tcwA + lenwA - 1 + 1 - tcwA)).any
                (· == v)) = true := by
            rw [← testBit_worksetOf]
            exact hv
          rw [show tcwA + lenwA - 1 + 1 - tcwA = lenwA from by
            omega, hPRl] at h0
          rcases List.any_eq_true.mp h0 with ⟨x, hx, hbeq⟩
          have hxe : x = v := by simpa using hbeq
          rw [← hxe]
          exact hx
        have hgo : ∀ (tcell' : Nat) (st7 : SearchSt),
            st7.lab = (refine ctx level st.lab st.ptn st.active
              numcells).lab →
            st7.ptn = (refine ctx level st.lab st.ptn st.active
              numcells).ptn →
            (st7.firstlab = st.firstlab ∨
              (st7.firstlab.size = st.lab.size ∧
                cellsPerm st.ptn level st.lab st7.firstlab)) →
            (st7.canonlab = st.canonlab ∨
              (st7.canonlab.size = st.lab.size ∧
                cellsPerm st.ptn level st.lab st7.canonlab)) →
            (st7.canonlab = st.canonlab ∨
              (st7.canonlab.size = n ∧ CellsReach G st7.canonlab)) →
            (∀ v, elem tcell' v = true →
              elem (worksetOf PR.lab tcwA (tcwA + lenwA - 1)) v =
                true) →
            SearchOut G (level - 1) level st
              (otherChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
                (refine ctx level st.lab st.ptn st.active
                  numcells).numcells tcwA
                ((nextElem tcell' none).getD 0)
                (nextElem tcell' none) tcell' st7).2 := by
          intro tcell' st7 h7l h7p h7f h7cs h7c hsub
          have hok7 := refine_searchOk (st2 := st7) hn hn0 hok h1
            h7l h7p h7c
          have hloop := otherChildLoop_ok G ctx hn inf hinf tcLevel
            hn0 fuel (ctx.n + 1) level
            (refine ctx level st.lab st.ptn st.active
              numcells).numcells tcwA
            ((nextElem tcell' none).getD 0) (nextElem tcell' none)
            tcell' st7 lenwA hok7 h1 (by omega)
            (fun _ => ⟨by rw [h7p]; exact hicA, hlen2A,
              hrangenA⟩)
            (fun v hv => by
              rw [h7l]
              exact hWmemA v (hsub v hv))
            (fun v hv => nextElem_mem hv)
          exact refine_loop_out hn hn0 hok h1 h7l h7p h7f h7cs h7c
            hloop
        split
        · split
          · -- the node prunes back before its children
            refine hreturn _ ?_ ?_
                (Or.inl (firstlab_eq_of rfl hPRf))
                (canonStore_or_of rfl hPRc hPRl
                  hRinv.labSize hRinv.perm) ?_ <;>
            first
            | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
            | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
            | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
          · split
            · split
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => shortprune_subset hv
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => shortprune_subset hv
            · split
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => hv
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => hv
        · split
          · -- the node prunes back before its children
            refine hreturn _ ?_ ?_
                (Or.inl (firstlab_eq_of rfl hPRf))
                (canonStore_or_of rfl hPRc hPRl
                  hRinv.labSize hRinv.perm) ?_ <;>
            first
            | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
            | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
            | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
          · split
            · split
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => shortprune_subset hv
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => shortprune_subset hv
            · split
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => hv
              · split <;>
                  refine hgo _ _ ?_ ?_
                      (Or.inl (firstlab_eq_of rfl hPRf))
                      (canonStore_or_of rfl hPRc hPRl
                        hRinv.labSize hRinv.perm) ?_ ?_ <;>
                  first
                  | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                  | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                  | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                  | exact fun v hv => hv
      case inr =>
        rw [ite_eq_right hCC]
        obtain ⟨tcwB, lenwB, hmkB, hicB, hlen2B, hrangeB⟩ :=
          maketargetcell_open (lab := PR.lab) (ptn := PR.ptn)
            (tcLevel := tcLevel) (hint := (-1 : Int)) h1
            (by rw [hPRp, hRinv.ptnSize, ← hnn'])
            (by rw [hPRp]; exact hRend)
            (by rw [hPRp]; exact hlive)
        rw [hPRp] at hicB
        rw [hmkB]
        dsimp only
        have hrangenB : tcwB + lenwB ≤ n := by
          rw [← hn]
          exact hrangeB
        have hWmemB : ∀ v : Nat,
            elem (worksetOf PR.lab tcwB (tcwB + lenwB - 1)) v =
              true →
            v ∈ segN (refine ctx level st.lab st.ptn st.active
              numcells).lab tcwB lenwB := by
          intro v hv
          have h0 : ((segN PR.lab tcwB
              (tcwB + lenwB - 1 + 1 - tcwB)).any
                (· == v)) = true := by
            rw [← testBit_worksetOf]
            exact hv
          rw [show tcwB + lenwB - 1 + 1 - tcwB = lenwB from by
            omega, hPRl] at h0
          rcases List.any_eq_true.mp h0 with ⟨x, hx, hbeq⟩
          have hxe : x = v := by simpa using hbeq
          rw [← hxe]
          exact hx
        have hgo : ∀ (tcell' : Nat) (st7 : SearchSt),
            st7.lab = (refine ctx level st.lab st.ptn st.active
              numcells).lab →
            st7.ptn = (refine ctx level st.lab st.ptn st.active
              numcells).ptn →
            (st7.firstlab = st.firstlab ∨
              (st7.firstlab.size = st.lab.size ∧
                cellsPerm st.ptn level st.lab st7.firstlab)) →
            (st7.canonlab = st.canonlab ∨
              (st7.canonlab.size = st.lab.size ∧
                cellsPerm st.ptn level st.lab st7.canonlab)) →
            (st7.canonlab = st.canonlab ∨
              (st7.canonlab.size = n ∧ CellsReach G st7.canonlab)) →
            (∀ v, elem tcell' v = true →
              elem (worksetOf PR.lab tcwB (tcwB + lenwB - 1)) v =
                true) →
            SearchOut G (level - 1) level st
              (otherChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
                (refine ctx level st.lab st.ptn st.active
                  numcells).numcells tcwB
                ((nextElem tcell' none).getD 0)
                (nextElem tcell' none) tcell' st7).2 := by
          intro tcell' st7 h7l h7p h7f h7cs h7c hsub
          have hok7 := refine_searchOk (st2 := st7) hn hn0 hok h1
            h7l h7p h7c
          have hloop := otherChildLoop_ok G ctx hn inf hinf tcLevel
            hn0 fuel (ctx.n + 1) level
            (refine ctx level st.lab st.ptn st.active
              numcells).numcells tcwB
            ((nextElem tcell' none).getD 0) (nextElem tcell' none)
            tcell' st7 lenwB hok7 h1 (by omega)
            (fun _ => ⟨by rw [h7p]; exact hicB, hlen2B,
              hrangenB⟩)
            (fun v hv => by
              rw [h7l]
              exact hWmemB v (hsub v hv))
            (fun v hv => nextElem_mem hv)
          exact refine_loop_out hn hn0 hok h1 h7l h7p h7f h7cs h7c
            hloop
        split
        · -- the node prunes back before its children
          refine hreturn _ ?_ ?_
              (Or.inl (firstlab_eq_of rfl hPRf))
              (canonStore_or_of rfl hPRc hPRl
                hRinv.labSize hRinv.perm) ?_ <;>
          first
          | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
          | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
          | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
        · split
          · split
            · split <;>
                refine hgo _ _ ?_ ?_
                    (Or.inl (firstlab_eq_of rfl hPRf))
                    (canonStore_or_of rfl hPRc hPRl
                      hRinv.labSize hRinv.perm) ?_ ?_ <;>
                first
                | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                | exact fun v hv => shortprune_subset hv
            · split <;>
                refine hgo _ _ ?_ ?_
                    (Or.inl (firstlab_eq_of rfl hPRf))
                    (canonStore_or_of rfl hPRc hPRl
                      hRinv.labSize hRinv.perm) ?_ ?_ <;>
                first
                | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                | exact fun v hv => shortprune_subset hv
          · split
            · split <;>
                refine hgo _ _ ?_ ?_
                    (Or.inl (firstlab_eq_of rfl hPRf))
                    (canonStore_or_of rfl hPRc hPRl
                      hRinv.labSize hRinv.perm) ?_ ?_ <;>
                first
                | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                | exact fun v hv => hv
            · split <;>
                refine hgo _ _ ?_ ?_
                    (Or.inl (firstlab_eq_of rfl hPRf))
                    (canonStore_or_of rfl hPRc hPRl
                      hRinv.labSize hRinv.perm) ?_ ?_ <;>
                first
                | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
                | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
                | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
                | exact fun v hv => hv
    case inr =>
      rw [ite_eq_right hD]
      have hzsub : ∀ st9 : SearchSt, shortprune 0 st9 = 0 := by
        intro st9
        rw [shortprune]
        rcases hb : st9.autos.back? with _ | pair
        · rfl
        · exact Nat.zero_and pair.2
      have hgo : ∀ (tcell' : Nat) (st7 : SearchSt),
          st7.lab = (refine ctx level st.lab st.ptn st.active
            numcells).lab →
          st7.ptn = (refine ctx level st.lab st.ptn st.active
            numcells).ptn →
          (st7.firstlab = st.firstlab ∨
            (st7.firstlab.size = st.lab.size ∧
              cellsPerm st.ptn level st.lab st7.firstlab)) →
          (st7.canonlab = st.canonlab ∨
            (st7.canonlab.size = st.lab.size ∧
              cellsPerm st.ptn level st.lab st7.canonlab)) →
          (st7.canonlab = st.canonlab ∨
            (st7.canonlab.size = n ∧ CellsReach G st7.canonlab)) →
          tcell' = 0 →
          SearchOut G (level - 1) level st
            (otherChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
              (refine ctx level st.lab st.ptn st.active
                numcells).numcells (-1 : Int).toNat
              ((nextElem tcell' none).getD 0)
              (nextElem tcell' none) tcell' st7).2 := by
        intro tcell' st7 h7l h7p h7f h7cs h7c h70
        subst h70
        have hok7 := refine_searchOk (st2 := st7) hn hn0 hok h1
          h7l h7p h7c
        have hloop := otherChildLoop_ok G ctx hn inf hinf tcLevel
          hn0 fuel (ctx.n + 1) level
          (refine ctx level st.lab st.ptn st.active
            numcells).numcells (-1 : Int).toNat
          ((nextElem 0 none).getD 0) (nextElem 0 none) 0 st7 0
          hok7 h1 (by omega)
          (fun h0 => absurd rfl h0)
          (fun v hv => by
            rw [elem, Nat.zero_testBit] at hv
            cases hv)
          (fun v hv => nextElem_mem hv)
        exact refine_loop_out hn hn0 hok h1 h7l h7p h7f h7cs h7c
          hloop
      split
      · -- the node prunes back before its children
        refine hreturn _ ?_ ?_
            (Or.inl (firstlab_eq_of rfl hPRf))
            (canonStore_or_of rfl hPRc hPRl
              hRinv.labSize hRinv.perm) ?_ <;>
        first
        | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
        | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
        | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
      · split
        · split
          · split <;>
              refine hgo _ _ ?_ ?_
                  (Or.inl (firstlab_eq_of rfl hPRf))
                  (canonStore_or_of rfl hPRc hPRl
                    hRinv.labSize hRinv.perm) ?_ ?_ <;>
              first
              | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
              | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
              | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
              | exact hzsub _
          · split <;>
              refine hgo _ _ ?_ ?_
                  (Or.inl (firstlab_eq_of rfl hPRf))
                  (canonStore_or_of rfl hPRc hPRl
                    hRinv.labSize hRinv.perm) ?_ ?_ <;>
              first
              | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
              | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
              | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
              | exact hzsub _
        · split
          · split <;>
              refine hgo _ _ ?_ ?_
                  (Or.inl (firstlab_eq_of rfl hPRf))
                  (canonStore_or_of rfl hPRc hPRl
                    hRinv.labSize hRinv.perm) ?_ ?_ <;>
              first
              | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
              | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
              | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
              | exact rfl
          · split <;>
              refine hgo _ _ ?_ ?_
                  (Or.inl (firstlab_eq_of rfl hPRf))
                  (canonStore_or_of rfl hPRc hPRl
                    hRinv.labSize hRinv.perm) ?_ ?_ <;>
              first
              | (refine Eq.trans ?_ hPRl; exact processnode_lab ctx level _ _)
              | (refine Eq.trans ?_ hPRp; exact processnode_ptn ctx level _ _)
              | exact canonlab_or_of rfl hPRc hPRl hRsize hRreach
              | exact rfl
termination_by (fuel, 0, 0)

theorem otherChildLoop_ok (G : Colored n k) (ctx : Ctx)
    (hn : ctx.n = n) (inf : Nat) (hinf : inf = n + 2)
    (tcLevel : Nat) (hn0 : 0 < n)
    (fuel cfuel level numcells tc tv1 : Nat) (tv? : Option Nat)
    (tcell0 : Nat) (st0 : SearchSt) (len : Nat)
    (hok : SearchOk G level numcells st0) (h1 : 1 ≤ level)
    (hfuel : n + 1 ≤ level + 1 + fuel)
    (hcell : tcell0 ≠ 0 →
      IsCell st0.ptn level tc len ∧ 2 ≤ len ∧ tc + len ≤ n)
    (hmem : ∀ v, elem tcell0 v = true → v ∈ segN st0.lab tc len)
    (htv : ∀ v, tv? = some v → elem tcell0 v = true) :
    SearchOut G level level st0
      (otherChildLoop ctx inf tcLevel fuel cfuel level numcells tc
        tv1 tv? tcell0 st0).2 := by
  match cfuel, tv? with
  | 0, _ =>
    rw [otherChildLoop]
    exact SearchOut.refl G level level hok.reach
  | cfuel + 1, none =>
    rw [otherChildLoop]
    case x_1 => omega
    exact SearchOut.refl G level level hok.reach
  | cfuel + 1, some tv =>
    rw [otherChildLoop]
    have htvmem0 : elem tcell0 tv = true := htv tv rfl
    obtain ⟨hic, hlen2, hrange⟩ := hcell (elem_ne_zero htvmem0)
    obtain ⟨o, ho, hoeq⟩ := mem_segN_iff.mp (hmem tv htvmem0)
    subst hoeq
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
    have hlevn : level ≤ n := Nat.le_trans hok.bc (bcount_le _ _ _)
    have hCok := breakout_searchOk (st' := { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]! })
      hn0 hok h1 hic hlen2 hrange ho rfl
      (breakout_ptn st0.lab st0.ptn (level + 1) tc
        st0.lab[tc + o]!) rfl
    have hDout := (otherNode_ok G ctx hn inf hinf tcLevel hn0
      fuel (level + 1) (numcells + 1) _ hCok (by omega)
      (by omega)).mono (B' := level) (by omega)
    have hbase := breakout_child_out hn0 hok h1 hic hlen2 hrange
      ho hDout rfl (breakout_ptn st0.lab st0.ptn (level + 1) tc
        st0.lab[tc + o]!) rfl rfl
    rcases Decidable.em ((otherNode ctx inf tcLevel fuel
        (level + 1) (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]! }).1 <
        Int.ofNat level) with hrt | hrt
    · simp only [ite_eq_left hrt]
      exact hbase.congr rfl rfl rfl rfl
    · simp only [ite_eq_right hrt]
      have hcont : ∀ (tcell' : Nat) (stG : SearchSt),
          stG.lab = (otherNode ctx inf tcLevel fuel (level + 1)
            (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]! }).2.lab →
          stG.ptn = (otherNode ctx inf tcLevel fuel (level + 1)
            (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]! }).2.ptn →
          stG.firstlab = (otherNode ctx inf tcLevel fuel (level + 1)
            (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]! }).2.firstlab →
          stG.canonlab = (otherNode ctx inf tcLevel fuel (level + 1)
            (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]! }).2.canonlab →
          (∀ v, elem tcell' v = true → elem tcell0 v = true) →
          SearchOut G level level st0
            (otherChildLoop ctx inf tcLevel fuel cfuel level
              numcells tc tv1
              (nextElem tcell' (some st0.lab[tc + o]!)) tcell'
              (recover ctx.n inf level stG)).2 := by
        intro tcell' stG hgl hgp hgf hgc hsub
        have houtG : SearchOut G level level st0 stG :=
          hbase.congr hgl hgp hgf hgc
        have hrecout : SearchOut G level level stG
            (recover ctx.n inf level stG) := by
          rw [hn, hinf]
          exact recover_out (by omega) houtG.reach
        have hout0R := houtG.trans hrecout
        have hokR : SearchOk G level numcells
            (recover ctx.n inf level stG) := by
          refine searchOk_of_out hok h1 hout0R ?_
          intro q hqn
          rw [hn, hinf, recover_ptn]
          rcases Decidable.em (q < n ∧ stG.ptn[q]! > level)
            with hc | hc
          · rw [ite_eq_left hc]
            exact Or.inr rfl
          · rw [ite_eq_right hc]
            left
            rcases Nat.lt_or_ge level stG.ptn[q]! with hgt | hle
            · exact absurd ⟨hqn, hgt⟩ hc
            · exact hle
        have htail := otherChildLoop_ok G ctx hn inf hinf tcLevel
          hn0 fuel cfuel level numcells tc tv1
          (nextElem tcell' (some st0.lab[tc + o]!)) tcell'
          (recover ctx.n inf level stG) len hokR h1 hfuel
          (fun _ => ⟨isCell_of_low hout0R.low hic, hlen2,
            hrange⟩)
          (fun v hv => (hout0R.perm tc len hic).mem_iff.mp
            (hmem v (hsub v hv)))
          (fun v hv => nextElem_mem hv)
        exact hout0R.trans htail
      rcases hnsp : ((otherNode ctx inf tcLevel fuel (level + 1)
          (numcells + 1) { st0 with
                  lab := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).1,
                  ptn := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.1,
                  active := (breakout st0.lab st0.ptn (level + 1) tc
                    st0.lab[tc + o]!).2.2,
                  fixedpts := insert st0.fixedpts st0.lab[tc + o]! }).2.needshortprune)
        with _ | _
      · simp only [hnsp, Bool.false_eq_true, ite_false]
        refine ite_or
          (P := fun x : Option Int × SearchSt =>
            SearchOut G level level st0 x.2) ?_ ?_
        · refine hcont _ _ ?_ ?_ ?_ ?_ ?_ <;>
            first
            | rfl
            | exact fun v hv => longprune_mem hv
        · refine hcont _ _ ?_ ?_ ?_ ?_ ?_ <;>
            first | rfl | exact fun v hv => hv
      · simp only [hnsp, ite_true]
        refine ite_or
          (P := fun x : Option Int × SearchSt =>
            SearchOut G level level st0 x.2) ?_ ?_
        · refine hcont _ _ ?_ ?_ ?_ ?_ ?_ <;>
            first
            | rfl
            | exact fun v hv => shortprune_subset (longprune_mem hv)
        · refine hcont _ _ ?_ ?_ ?_ ?_ ?_ <;>
            first
            | rfl
            | exact fun v hv => shortprune_subset hv
termination_by (fuel, 1, cfuel)

end

/-! # The search output is reached -/

private theorem run_canonlab {k : Nat} (G : Colored n k) (hn0 : 0 < n) :
    (runColored G).canonlab =
      (firstPathNode { n := n, g := rowsOf G } (n + 2) 100 (n + 2) 1
        (initialPartition G).2.length
        { lab := (initialPartition G).1
          ptn := initPtn n (n + 2) (initialPartition G).2
          active := initActive (initialPartition G).2
          orbits := .ofFn (n := n) fun i => i.val
          firstcode := .replicate (n + 2) 0
          canoncode := .replicate (n + 2) 0
          firsttc := .replicate (n + 2) (-1)
          firstlab := .replicate n 0
          canonlab := .replicate n 0
          canong := .replicate n 0
          numorbits := n }).2.canonlab := by
  have h0 : runColored G = run n (rowsOf G) (initialPartition G).1
      (initialPartition G).2 := rfl
  rw [h0, run]
  simp only [Id.run_bind, Id.run_pure]
  rw [ite_eq_right (by
    intro h
    have : n = 0 := by simpa using h
    omega)]
  rfl

/-- The identity orbit array. -/
private theorem ofFn_id_getElem (v : Nat) (hv : v < n) :
    (Array.ofFn (n := n) fun i : Fin n => i.val)[v]! = v := by
  rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]

/-- The root state satisfies the search invariant. -/
theorem root_searchOk {k : Nat} (G : Colored n k)
    (hn0 : 0 < n) :
    SearchOk G 1 (initialPartition G).2.length
      { lab := (initialPartition G).1
        ptn := initPtn n (n + 2) (initialPartition G).2
        active := initActive (initialPartition G).2
        orbits := .ofFn (n := n) fun i => i.val
        firstcode := .replicate (n + 2) 0
        canoncode := .replicate (n + 2) 0
        firsttc := .replicate (n + 2) (-1)
        firstlab := .replicate n 0
        canonlab := .replicate n 0
        canong := .replicate n 0
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

/-- The transcribed search's canonical labelling has full size. -/
theorem canonlab_size {k : Nat} (G : Colored n k) :
    (runColored G).canonlab.size = n := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    have h0 : runColored G = run 0 (rowsOf G) (initialPartition G).1
        (initialPartition G).2 := rfl
    rw [h0, run]
    simp only [Id.run_bind, Id.run_pure]
    rw [ite_eq_left (by simp)]
    rfl
  · rw [run_canonlab G hn0]
    exact ((firstPathNode_ok G { n := n, g := rowsOf G } rfl (n + 2)
      rfl 100 hn0 (n + 2) 1 (initialPartition G).2.length _
      (root_searchOk G hn0) (Nat.le_refl 1) (by omega)).2
      (fun v hv => ofFn_id_getElem v hv)).1

/-- The transcribed search's canonical labelling is reached: it
fills every cell of the initial partition with that cell's own
vertices. The B2 simulation clause of the verified search refinement
programme, discharging the transcription-side residuals of
`certifyCanon?_isSome`. -/
theorem canonlab_cellsReach {k : Nat} (G : Colored n k) :
    CellsReach G (runColored G).canonlab := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    intro a len hcell
    have he : segN (initialPartition G).1 a len =
        segN (runColored G).canonlab a len := by
      refine segN_congr fun o ho => ?_
      rw [getElem!_neg _ _ (by
          rw [size_initialPartition]
          omega),
        getElem!_neg _ _ (by
          have := canonlab_size G
          omega)]
    rw [he]
  · rw [run_canonlab G hn0]
    exact ((firstPathNode_ok G { n := n, g := rowsOf G } rfl (n + 2)
      rfl 100 hn0 (n + 2) 1 (initialPartition G).2.length _
      (root_searchOk G hn0) (Nat.le_refl 1) (by omega)).2
      (fun v hv => ofFn_id_getElem v hv)).2

/-- The transcribed search's canonical labelling passes the colour
monotonicity check: one of the two transcription-side residuals of
`certifyCanon?_isSome`. -/
theorem colorSortedCheck_canonlab {k : Nat} (G : Colored n k) :
    colorSortedCheck G (runColored G).canonlab = true :=
  colorSortedCheck_of_cellsReach (canonlab_size G)
    (canonlab_cellsReach G)

/-- The transcribed search's canonical labelling is a permutation of
the vertices: the label well-formedness residual of
`certifyCanon?_isSome`. -/
theorem canonlab_perm_range {k : Nat} (G : Colored n k) :
    (runColored G).canonlab.toList.Perm (List.range n) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    have hsz := canonlab_size G
    rw [List.range_zero]
    have : (runColored G).canonlab.toList.length = 0 := by
      rw [Array.length_toList, hsz]
    rw [List.length_eq_zero_iff.mp this]
  · exact isPerm_of_cellsReach (canonlab_size G) hn0
      (canonlab_cellsReach G)

end Hex.GraphIso.Nauty
