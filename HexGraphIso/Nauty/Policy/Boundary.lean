/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Cheap
public import HexGraphIso.Nauty.SmallCell.Pairs
public import HexGraphIso.Nauty.Policy.Partition
public import HexGraphIso.Nauty.Policy.Bounds
public import HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.Reach
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A boundary retained above a call stays fixed until the call creates a deeper boundary. -/
theorem boundaryPolicy (ctx : Ctx n) (inf tcLevel bound saved : Nat) :
    Generic.BoundedPolicy ctx inf tcLevel bound (fun st : Search n => st.noncheaplevel = saved ∨ bound < st.noncheaplevel) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change (compareCodes level code st).noncheaplevel = saved ∨ bound < (compareCodes level code st).noncheaplevel
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.noncheaplevel, ite_self]
    exact h
  target := by
    intro level numcells st _ h
    change (chooseTarget false ctx tcLevel level numcells st).2.2.2.noncheaplevel = saved ∨ bound < (chooseTarget false ctx tcLevel level numcells st).2.2.2.noncheaplevel
    rw [chooseTarget_fields]
    exact h
  classify := by
    intro level numcells st h
    change (classify ctx level numcells st).2.noncheaplevel = saved ∨ bound < (classify ctx level numcells st).2.noncheaplevel
    unfold Nauty.classify
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
      apply_ite Search.noncheaplevel, ite_self]
    exact h
  leaf := by
    intro leaf level st _ h
    change (leafExit leaf level st).2.noncheaplevel = saved ∨ bound < (leafExit leaf level st).2.noncheaplevel
    rw [leafExit_noncheap]
    exact h
  cheap := by
    intro first level st hlevel h
    change (cheapCheck first level st).noncheaplevel = saved ∨ bound < (cheapCheck first level st).noncheaplevel
    unfold cheapCheck
    split
    · right
      change bound < level + 1
      omega
    · exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st hlevel h
    change (recoverLevels level (recoverPtn inf level st)).noncheaplevel = saved ∨ bound < (recoverLevels level (recoverPtn inf level st)).noncheaplevel
    rw [recover_noncheap]
    split
    · exact Or.inr (by omega)
    · exact h
  afterSweep := by
    intro first level size index st _ h
    change (afterSweep first level size index st).noncheaplevel = saved ∨ bound < (afterSweep first level size index st).noncheaplevel
    unfold afterSweep
    split <;> exact h

/-- An off-path call can only replace its entry boundary below its receiving ancestor. -/
theorem node_boundary {ctx : Ctx n} {inf tcLevel fuel level numcells : Nat}
    {st : Search n} (hlevel : 0 < level) :
    (node false ctx inf tcLevel fuel level numcells st).2.noncheaplevel = st.noncheaplevel ∨
      level ≤ (node false ctx inf tcLevel fuel level numcells st).2.noncheaplevel := by
  have h := Generic.node_bounded (boundaryPolicy ctx inf tcLevel (level - 1) st.noncheaplevel)
    fuel level numcells st (by omega) (Or.inl rfl)
  rw [← node_eq_generic] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- The saved implicit pair is meaningful only strictly below its admission boundary. -/
abbrev Boundary (G : Colored n k) (ctx : Ctx n) (level : Nat) (st : Search n) : Prop :=
  CheapOk ctx (initialPartition G).1 (initPtn n (n + 2) (initialPartition G).2) level st

/-- Bookkeeping preserves the frozen pair when its defining fields agree. -/
theorem Boundary.congr {G : Colored n k} {ctx : Ctx n} {level : Nat} {st out : Search n}
    (h : Boundary G ctx level st) (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hn : out.noncheaplevel = st.noncheaplevel) : Boundary G ctx level out :=
  h.ofFrames hl hp hn

/-- Refinement preserves every pair frozen strictly above the current node. -/
theorem Boundary.visit {G : Colored n k} {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (h : Boundary G ctx level st) (hlevel : 1 ≤ level) :
    Boundary G ctx level (visit ctx level numcells st).2.2 :=
  h.refine hlevel rfl rfl rfl

/-- The initial state has no active frozen pair. -/
theorem initial_boundary (G : Colored n k) (hn0 : 0 < n) (ctx : Ctx n) :
    Boundary G ctx 1 (initial n (initialPartition G).1 (initialPartition G).2) :=
  CheapOk.root hn0 (initial_ok G hn0) rfl

/-- A call's partition receipt transports every still-active frozen pair. -/
theorem Boundary.of_out {G : Colored n k} {ctx : Ctx n} {level : Nat} {st out : Search n}
    (h : Boundary G ctx level st) (hlevel : 1 < level)
    (hout : SearchOut G (level - 1) level st out)
    (hpos : 0 < out.noncheaplevel)
    (hn : out.noncheaplevel = st.noncheaplevel ∨ level ≤ out.noncheaplevel) :
    Boundary G ctx level out := by
  have hls : out.lab.size = st.lab.size := hout.labSize
  have hps : out.ptn.size = st.ptn.size := hout.ptnSize
  have hroot : st.ptn[st.ptn.size - 1]! ≤ 1 := h.rootEnd
  have hpositive : 0 < st.noncheaplevel := h.positive
  refine ⟨hpos, hls.trans h.labSize, hps.trans h.ptnSize, ?_, ?_⟩
  · change out.ptn[out.ptn.size - 1]! ≤ 1
    rw [hps]
    have he := hout.low (st.ptn.size - 1) (Or.inl (show st.ptn[st.ptn.size - 1]! ≤ level - 1 by omega))
    change out.ptn[st.ptn.size - 1]! = st.ptn[st.ptn.size - 1]! at he
    rw [he]
    exact h.rootEnd
  · intro hlt
    change out.noncheaplevel < level at hlt
    have he : out.noncheaplevel = st.noncheaplevel := by rcases hn with hn | hn; exact hn; omega
    have hsaved : st.noncheaplevel < level := he ▸ hlt
    have hpos := h.positive
    have hend : st.ptn[st.ptn.size - 1]! ≤ st.noncheaplevel := by omega
    have hperm : cellsPerm st.ptn st.noncheaplevel st.lab out.lab := by
      apply cellsPerm_coarsen (ptnC := st.ptn) (ptnF := st.ptn)
        (levC := st.noncheaplevel) (levF := level)
      · rfl
      · exact h.labSize.trans h.ptnSize.symm
      · exact hls.trans (h.labSize.trans h.ptnSize.symm)
      · exact hout.perm
      · omega
      · exact hend
      · intro q hq; omega
    have hcells : cells st.ptn st.noncheaplevel n = cells out.ptn st.noncheaplevel n := by
      symm
      apply cells_eq_of_low hps
      intro q hq
      apply hout.low q
      change st.ptn[q]! ≤ level - 1 ∨ out.ptn[q]! ≤ level - 1
      rcases hq with hq | hq
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hfm := fmptn_congr (nn := n) (Nat.le_of_eq h.ptnSize.symm) hend hcells hperm
    change PairOk ctx.g _ _ _ (fmptn out.lab out.ptn out.noncheaplevel n).1
      (fmptn out.lab out.ptn out.noncheaplevel n).2
    rw [he, ← hfm]
    exact h.pair hsaved

/-- An off-path child returns with the implicit pair at every surviving older boundary. -/
theorem Boundary.node {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (h : Boundary G ctx level st) (hn0 : 0 < n) (hlevel : 1 < level)
    (hok : SearchOk G level numcells st) :
    Boundary G ctx level (node false ctx (n + 2) tcLevel fuel level numcells st).2 := by
  exact h.of_out hlevel (node_out false hn0 (by omega) hok)
    (node_noncheap (bound := 0) (by omega) h.positive) (node_boundary (by omega))

/-- Recovery revives an older boundary or parks a new one below the next child. -/
theorem Boundary.recover {G : Colored n k} {ctx : Ctx n} {current level : Nat} {st : Search n}
    (h : Boundary G ctx current st) (hle : level ≤ current) (hlevel : 1 ≤ level)
    (hinf : level < n + 2) :
    Boundary G ctx level (recoverLevels level (recoverPtn (n + 2) level st)) := by
  have hr := CheapOk.recover h hle hlevel hinf
  rw [← recover_eq] at hr
  exact hr

/-- Comparing codes preserves the boundary level. -/
theorem compare_noncheap (level code : Nat) (st : Search n) :
    (compareCodes level code st).noncheaplevel = st.noncheaplevel := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.noncheaplevel, ite_self]

/-- Choosing either target preserves the boundary level. -/
theorem target_noncheap (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (chooseTarget first ctx tcLevel level numcells st).2.2.2.noncheaplevel = st.noncheaplevel := by
  cases first <;> first | rw [chooseTarget_fields] | rw [chooseFirst_fields]

/-- Classification preserves the boundary level. -/
theorem classify_noncheap (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.noncheaplevel = st.noncheaplevel := by
  unfold Nauty.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.noncheaplevel, ite_self]

/-- The guard's boundary is at most the next child's level. -/
theorem cheap_bound {level : Nat} {st : Search n} (first : Bool)
    (h : st.noncheaplevel ≤ level) : (cheapCheck first level st).noncheaplevel ≤ level + 1 := by
  unfold cheapCheck
  split
  · exact Nat.le_refl _
  · exact Nat.le_trans h (Nat.le_succ _)

/-- Recovery parks a deeper boundary at the next child's level. -/
theorem recover_bound (level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn (n + 2) level st)).noncheaplevel ≤ level + 1 := by
  rw [recover_noncheap]
  split <;> omega

/-- Comparing codes leaves the saved pair unchanged. -/
theorem Boundary.compare {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : Boundary G ctx level st) (code : Nat) :
    Boundary G ctx level (compareCodes level code st) := by
  apply h.congr (compareCodes_frame level code st).1 (compareCodes_frame level code st).2.1
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.noncheaplevel, ite_self]

/-- Target selection leaves the saved pair unchanged. -/
theorem Boundary.target {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : Boundary G ctx level st) (first : Bool) (tcLevel numcells : Nat) :
    Boundary G ctx level (chooseTarget first ctx tcLevel level numcells st).2.2.2 := by
  apply h.congr (chooseTarget_frame first ctx tcLevel level numcells st).1
    (chooseTarget_frame first ctx tcLevel level numcells st).2.1
  cases first <;> first | rw [chooseTarget_fields] | rw [chooseFirst_fields]

/-- Classification fills scratch data without changing the saved pair. -/
theorem Boundary.classify {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : Boundary G ctx level st) (numcells : Nat) :
    Boundary G ctx level (classify ctx level numcells st).2 := by
  apply h.congr (classify_frame ctx level numcells st).1 (classify_frame ctx level numcells st).2.1
  unfold Nauty.classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.noncheaplevel, ite_self]

/-- Leaf actions retain the saved pair, including after an admission. -/
theorem Boundary.leaf {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : Boundary G ctx level st) (leaf : Leaf) :
    Boundary G ctx level (leafExit leaf level st).2 :=
  h.congr (leafExit_frame leaf level st).1 (leafExit_frame leaf level st).2.1
    (leafExit_noncheap leaf level st)

/-- A successful guard validates a new boundary; a failed guard parks it below the next child. -/
theorem Boundary.cheap {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : Boundary G ctx level st) (first : Bool) (hlevel : 1 ≤ level)
    (hpair : cheapautom st.ptn level n = true →
      PairOk ctx.g (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 1
        (fmptn st.lab st.ptn level n).1 (fmptn st.lab st.ptn level n).2) :
    Boundary G ctx (level + 1) (cheapCheck first level st) := by
  unfold cheapCheck
  split
  · exact h.park (boundary := level + 1) (by omega) (Nat.le_refl _)
  · rename_i hguard
    apply h.next
    intro heq
    change st.noncheaplevel = level at heq
    have hcheap : cheapautom st.ptn level n = true := by
      cases hc : cheapautom st.ptn level n with
      | true => rfl
      | false => cases first <;> simp [heq, hc] at hguard
    change PairOk ctx.g _ _ _ (fmptn st.lab st.ptn st.noncheaplevel n).1
      (fmptn st.lab st.ptn st.noncheaplevel n).2
    rw [heq]
    exact hpair hcheap

/-- Individualizing within the current cell preserves the frozen ancestor pair. -/
theorem Boundary.child {G : Colored n k} {ctx : Ctx n} {level tc tv : Nat}
    {st : Search n} {cell : VSet n} (h : Boundary G ctx (level + 1) st)
    (first : Bool) (hlevel : 1 ≤ level) (htarget : Generic.Target (fun st => st) level tc cell st)
    (htv : cell.mem tv = true) : Boundary G ctx (level + 1) (child first level tc tv st) := by
  obtain ⟨len, hcell, hmem⟩ := htarget
  obtain ⟨hc, hlen, hrange⟩ := hcell (mem_ne_empty htv)
  obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (hmem tv htv)
  change st.lab[tc + o]! = tv at hv
  apply h.breakout hlevel hc hlen hrange ho
  · change (Nauty.child first level tc tv st).lab = _

    rw [hv]
    cases first <;> rfl
  · cases first <;> rfl
  · cases first <;> rfl

/-- A refined equitable node passing the cheap guard supplies the root ledger pair. -/
theorem refined_pair {G : Colored n k} {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (heq : Equitable ctx level (st.refined ctx level numcells).lab (st.refined ctx level numcells).ptn)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcheap : cheapautom (st.refined ctx level numcells).ptn level n = true) :
    let R := st.refined ctx level numcells
    PairOk ctx.g (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 1
      (fmptn R.lab R.ptn level n).1 (fmptn R.lab R.ptn level n).2 := by
  have hr := ((reachPolicy G ctx 0 hn0).visit level numcells st hlevel hok).1
  have hs := subtreeOk_of_cheapautom (refined_iter hn0 hlevel hok) heq hr.count.symm hcheap
  exact SubtreeOk.pair_ok hn0 hlevel hgsz hsymm hloop hs hr.reach hr.init1

/-- Returning to a parent preserves its boundary pair for the next child, including equality. -/
theorem Boundary.recover_child {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : Boundary G ctx (level + 1) st) (hlevel : 1 ≤ level) (hinf : level < n + 2) :
    Boundary G ctx (level + 1) (recoverLevels level (recoverPtn (n + 2) level st)) := by
  have hr := h.recover (Nat.le_succ _) hlevel hinf
  apply hr.next
  intro heq
  change (recoverLevels level (recoverPtn (n + 2) level st)).noncheaplevel = level at heq
  have hs : st.noncheaplevel = level := by rw [recover_noncheap] at heq; split at heq <;> omega
  change PairOk ctx.g _ _ _
    (fmptn (recoverLevels level (recoverPtn (n + 2) level st)).lab
      (recoverLevels level (recoverPtn (n + 2) level st)).ptn
      (recoverLevels level (recoverPtn (n + 2) level st)).noncheaplevel n).1
    (fmptn (recoverLevels level (recoverPtn (n + 2) level st)).lab
      (recoverLevels level (recoverPtn (n + 2) level st)).ptn
      (recoverLevels level (recoverPtn (n + 2) level st)).noncheaplevel n).2
  rw [heq, recover_eq, recover_fmptn (Nat.le_of_eq h.ptnSize.symm)
    (Nat.le_trans h.rootEnd hlevel) (Nat.le_refl _) hinf]
  have hp := h.pair (show st.noncheaplevel < level + 1 from by change st.noncheaplevel < level + 1; omega)
  change PairOk ctx.g _ _ _ (fmptn st.lab st.ptn st.noncheaplevel n).1
    (fmptn st.lab st.ptn st.noncheaplevel n).2 at hp
  rwa [hs] at hp

end Hex.GraphIso.Nauty
