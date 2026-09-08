/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Autos
public import HexGraphIso.Nauty.Invariant.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Cheap-automorphism ledger boundary -/

/-- The implicit automorphism pair remains valid while search stays
strictly below the level at which that pair was frozen.  At the frozen
level itself the implication is dormant: `processnode` does not insert an
implicit pair there, and a failed cheap-automorphism guard will move the
boundary before the next descent. -/
structure CheapOk (ctx : Ctx n) (rlab rptn : Array Nat) (level : Nat)
    (st : SearchSt n) : Prop where
  positive : 0 < st.noncheaplevel
  labSize : st.lab.size = n
  ptnSize : st.ptn.size = n
  rootEnd : st.ptn[st.ptn.size - 1]! ≤ 1
  pair : st.noncheaplevel < level →
    PairOk ctx.g rptn rlab 1
      (fmptn st.lab st.ptn st.noncheaplevel n).1
      (fmptn st.lab st.ptn st.noncheaplevel n).2

/-- At a node entry, the runtime bound turns the strict-boundary ledger
invariant into the premise consumed by `processnode`. -/
theorem CheapOk.ready {ctx : Ctx n} {rlab rptn : Array Nat} {level : Nat}
    {st : SearchSt n} (h : CheapOk ctx rlab rptn level st)
    (hbound : st.noncheaplevel ≤ level) (hne : level ≠ st.noncheaplevel) :
    PairOk ctx.g rptn rlab 1
      (fmptn st.lab st.ptn st.noncheaplevel n).1
      (fmptn st.lab st.ptn st.noncheaplevel n).2 :=
  h.pair (by omega)

/-- The cheap-boundary invariant depends only on the current labelling,
partition, and boundary level. -/
theorem CheapOk.ofFrames {ctx : Ctx n} {rlab rptn : Array Nat}
    {level : Nat} {st out : SearchSt n}
    (h : CheapOk ctx rlab rptn level st)
    (hlab : out.lab = st.lab) (hptn : out.ptn = st.ptn)
    (hncl : out.noncheaplevel = st.noncheaplevel) :
    CheapOk ctx rlab rptn level out := by
  constructor
  · rw [hncl]
    exact h.positive
  · rw [hlab]
    exact h.labSize
  · rw [hptn]
    exact h.ptnSize
  · rw [hptn]
    exact h.rootEnd
  · intro hlt
    rw [hncl] at hlt
    rw [hlab, hptn, hncl]
    exact h.pair hlt

/-- Reopening below `level` preserves every `fmptn` frozen at or above
the root and at or below `level`. -/
theorem recover_fmptn {st : SearchSt n} {inf level saved : Nat}
    (hsize : n ≤ st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ saved)
    (hsaved : saved ≤ level) (hinf : level < inf) :
    fmptn (Nauty.recover n inf level st).lab
        (Nauty.recover n inf level st).ptn
        saved n =
      fmptn st.lab st.ptn saved n := by
  have hcells : cells (Nauty.recover n inf level st).ptn saved n =
      cells st.ptn saved n := by
    apply cells_eq_of_low (recover_ptn_size n inf level st)
    intro q hq
    rw [recover_ptn]
    rcases Decidable.em (q < n ∧ st.ptn[q]! > level) with hc | hc
    · rw [ite_eq_left hc]
      exfalso
      rcases hq with hold | hnew
      · omega
      · rw [recover_ptn, ite_eq_left hc] at hnew
        omega
    · rw [ite_eq_right hc]
  apply Eq.symm
  apply fmptn_congr hsize hend hcells.symm
  rw [recover_lab]
  exact cellsPerm_refl _ _ _

/-- Recovery either parks the boundary just below the next child, where
the strict pair condition is dormant, or retains an older frozen pair. -/
theorem CheapOk.recover {ctx : Ctx n} {rlab rptn : Array Nat}
    {current level inf : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn current st) (hle : level ≤ current)
    (hlevel : 1 ≤ level) (hinf : level < inf) :
    CheapOk ctx rlab rptn level (Nauty.recover n inf level st) := by
  have hncl : (Nauty.recover n inf level st).noncheaplevel =
      if level < st.noncheaplevel then level + 1
      else st.noncheaplevel := by
    rw [Nauty.recover]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite SearchSt.noncheaplevel, ite_self]
  constructor
  · rw [hncl]
    split
    · omega
    · exact h.positive
  · rw [recover_lab]
    exact h.labSize
  · rw [recover_ptn_size]
    exact h.ptnSize
  · rw [recover_ptn_size, recover_ptn]
    rcases Decidable.em
        (st.ptn.size - 1 < n ∧
          st.ptn[st.ptn.size - 1]! > level) with hc | hc
    · rw [ite_eq_left hc]
      exfalso
      have := h.rootEnd
      omega
    · rw [ite_eq_right hc]
      exact h.rootEnd
  · intro hlt
    rcases Decidable.em (level < st.noncheaplevel) with hc | hc
    · rw [hncl, ite_eq_left hc] at hlt
      omega
    · have heq : (Nauty.recover n inf level st).noncheaplevel =
          st.noncheaplevel := by rw [hncl, ite_eq_right hc]
      rw [heq] at hlt ⊢
      have hpos := h.positive
      rw [recover_fmptn (Nat.le_of_eq h.ptnSize.symm)
        (Nat.le_trans h.rootEnd (by omega : 1 ≤ st.noncheaplevel))
        (by omega : st.noncheaplevel ≤ level) hinf]
      exact h.pair (by omega)

/-- Writing a boundary at or above the logical level suspends the pair
condition without changing the partition facts needed to revive it. -/
theorem CheapOk.park {ctx : Ctx n} {rlab rptn : Array Nat}
    {old current boundary : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn old st) (hpos : 0 < boundary)
    (hcurrent : current ≤ boundary) :
    CheapOk ctx rlab rptn current
      { st with noncheaplevel := boundary } := by
  refine ⟨hpos, h.labSize, h.ptnSize, h.rootEnd, ?_⟩
  simp only
  omega

/-- A valid pair at the current boundary extends the invariant through
the next logical level. -/
theorem CheapOk.next {ctx : Ctx n} {rlab rptn : Array Nat}
    {level : Nat} {st : SearchSt n}
    (h : CheapOk ctx rlab rptn level st)
    (hpair : st.noncheaplevel = level →
      PairOk ctx.g rptn rlab 1
        (fmptn st.lab st.ptn st.noncheaplevel n).1
        (fmptn st.lab st.ptn st.noncheaplevel n).2) :
    CheapOk ctx rlab rptn (level + 1) st := by
  refine ⟨h.positive, h.labSize, h.ptnSize, h.rootEnd, ?_⟩
  intro hlt
  rcases Decidable.em (st.noncheaplevel = level) with heq | hne
  · exact hpair heq
  · exact h.pair (by omega)

/-- Refinement only splits at the current level and permutes within the
old current cells, so every pair frozen at a strictly smaller level is
unchanged. -/
theorem CheapOk.refine {ctx : Ctx n} {rlab rptn : Array Nat}
    {level numcells : Nat} {st out : SearchSt n}
    (h : CheapOk ctx rlab rptn level st) (hlevel : 1 ≤ level)
    (hlab : out.lab =
      (Nauty.refine ctx level st.lab st.ptn st.active numcells).lab)
    (hptn : out.ptn =
      (Nauty.refine ctx level st.lab st.ptn st.active numcells).ptn)
    (hncl : out.noncheaplevel = st.noncheaplevel) :
    CheapOk ctx rlab rptn level out := by
  let rs := Nauty.refine ctx level st.lab st.ptn st.active numcells
  have hnnEq : n = st.ptn.size := h.ptnSize.symm
  have hnn : n ≤ st.ptn.size := Nat.le_of_eq hnnEq
  have hls : st.lab.size = st.ptn.size := h.labSize.trans h.ptnSize.symm
  have hend : st.ptn[st.ptn.size - 1]! ≤ level :=
    Nat.le_trans h.rootEnd hlevel
  have hR := refine_refInv (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) hnn hls hend
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hncl]
    exact h.positive
  · rw [hlab, hR.labSize]
    exact h.labSize
  · rw [hptn, hR.ptnSize]
    exact h.ptnSize
  · rw [hptn, hR.ptnSize]
    rw [refine_frozen hnnEq hls hend hend]
    exact h.rootEnd
  · intro hlt
    rw [hncl] at hlt
    have hpos := h.positive
    have hendSaved : st.ptn[st.ptn.size - 1]! ≤
        st.noncheaplevel := Nat.le_trans h.rootEnd (by omega)
    have hcells : cells st.ptn st.noncheaplevel n =
        cells rs.ptn st.noncheaplevel n := by
      apply Eq.symm
      apply cells_eq_of_low hR.ptnSize
      intro q hq
      rcases hq with hold | hnew
      · exact refine_frozen hnnEq hls hend
          (Nat.le_trans hold (Nat.le_of_lt hlt))
      · rcases ptn_refine_vals ctx level st.lab st.ptn st.active
            numcells q with heq | heq
        · exact heq
        · rw [heq] at hnew
          omega
    have hperm : cellsPerm st.ptn st.noncheaplevel st.lab rs.lab := by
      apply cellsPerm_coarsen (ptnC := st.ptn) (ptnF := st.ptn)
          (levC := st.noncheaplevel) (levF := level)
      · rfl
      · exact hls
      · rw [hR.labSize]
        exact hls
      · exact hR.perm
      · exact hend
      · exact hendSaved
      · intro q hq
        exact Nat.le_trans hq (Nat.le_of_lt hlt)
    have hfm : fmptn st.lab st.ptn st.noncheaplevel n =
        fmptn rs.lab rs.ptn st.noncheaplevel n :=
      fmptn_congr hnn hendSaved hcells hperm
    rw [hlab, hptn, hncl, ← hfm]
    exact h.pair hlt

/-- Individualizing inside a current cell does not change the implicit
pair frozen at an older cheap boundary. -/
theorem CheapOk.breakout {ctx : Ctx n} {rlab rptn : Array Nat}
    {level tc len o : Nat} {st out : SearchSt n}
    (h : CheapOk ctx rlab rptn (level + 1) st)
    (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hlab : out.lab =
      (Nauty.breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1)
    (hptn : out.ptn = st.ptn.set! tc (level + 1))
    (hncl : out.noncheaplevel = st.noncheaplevel) :
    CheapOk ctx rlab rptn (level + 1) out := by
  have hls : st.lab.size = st.ptn.size := h.labSize.trans h.ptnSize.symm
  have hpos := h.positive
  have hend : st.ptn[st.ptn.size - 1]! ≤ level :=
    Nat.le_trans h.rootEnd hlevel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hncl]
    exact h.positive
  · rw [hlab, breakout_lab_size]
    exact h.labSize
  · rw [hptn, Array.size_set!]
    exact h.ptnSize
  · rw [hptn, Array.size_set!]
    rw [Array.getElem!_set!_ne _ _ _ _ (by rw [h.ptnSize]; omega)]
    exact h.rootEnd
  · intro hlt
    rw [hncl] at hlt
    have hsaved : st.noncheaplevel ≤ level := by omega
    have hendSaved : st.ptn[st.ptn.size - 1]! ≤
        st.noncheaplevel := Nat.le_trans h.rootEnd (by omega)
    have hcells : cells st.ptn st.noncheaplevel n =
        cells (st.ptn.set! tc (level + 1)) st.noncheaplevel n := by
      apply Eq.symm
      apply cells_eq_of_low (by rw [Array.size_set!])
      intro q hq
      rcases Decidable.em (q = tc) with heq | hne
      · subst q
        have hopen := hcell.2.2.1 tc (Nat.le_refl tc) (by omega)
        rw [Array.getElem!_set!_self _ _ _ (by rw [h.ptnSize]; omega)] at hq
        rcases hq with hq | hq <;> omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun he => hne he.symm)]
    have hperm : cellsPerm st.ptn st.noncheaplevel st.lab
        (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1 := by
      apply cellsPerm_coarsen (ptnC := st.ptn) (ptnF := st.ptn)
          (levC := st.noncheaplevel) (levF := level)
      · rfl
      · exact hls
      · rw [breakout_lab_size]
        exact hls
      · exact breakout_cellsPerm (n := n) hcell (by rw [h.ptnSize]; exact hrange)
          hls ho
      · exact hend
      · exact hendSaved
      · intro q hq
        exact Nat.le_trans hq hsaved
    have hfm : fmptn st.lab st.ptn st.noncheaplevel n =
        fmptn (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1 (st.ptn.set! tc (level + 1))
          st.noncheaplevel n :=
      fmptn_congr (Nat.le_of_eq h.ptnSize.symm) hendSaved hcells hperm
    rw [hlab, hptn, hncl, ← hfm]
    exact h.pair hlt

/-- The initial search boundary is one, so its strict pair condition is
empty at the root. -/
theorem CheapOk.root {G : Colored n k} {ctx : Ctx n} {numcells : Nat}
    {st : SearchSt n} (hn0 : 0 < n)
    (hok : SearchOk G 1 numcells st) (hncl : st.noncheaplevel = 1) :
    CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) 1 st := by
  refine ⟨by rw [hncl]; exact Nat.zero_lt_succ 0, ?_, ?_,
    searchOk_end hn0 hok (Nat.le_refl 1), ?_⟩
  · rw [hok.labSize]
  · rw [hok.ptnSize]
  · intro hlt
    rw [hncl] at hlt
    omega

end Hex.GraphIso.Nauty
