/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.First.History
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Agreement with the first path carries the current partition's actual
stored-target descent. Before comparing a node, `agreed` is `level - 1`. -/
structure Aligned (ctx : Ctx n) (base : Nat) (root : RefineSt n)
    (level agreed numcells : Nat) (st : Search n) : Prop where
  bound : st.eqlevFirst ≤ agreed
  descent : st.eqlevFirst = agreed →
    DescentAt ctx st.firsttc base root level numcells st

/-- Bookkeeping that can only lower agreement retains an aligned descent. -/
theorem Aligned.mono {ctx : Ctx n} {base level agreed numcells : Nat}
    {root : RefineSt n} {st out : Search n}
    (h : Aligned ctx base root level agreed numcells st)
    (heq : out.eqlevFirst ≤ st.eqlevFirst)
    (htc : out.firsttc = st.firsttc) (hl : out.lab = st.lab) (hp : out.ptn = st.ptn) :
    Aligned ctx base root level agreed numcells out := by
  refine ⟨Nat.le_trans heq h.bound, ?_⟩
  intro hmatch
  have hold : st.eqlevFirst = agreed := by have := h.bound; omega
  rw [htc]
  exact (h.descent hold).congr hl hp

/-- Comparing a code activates exactly the pending history of its node. -/
theorem Aligned.compare {ctx : Ctx n} {base level numcells code : Nat}
    {root : RefineSt n} {st : Search n}
    (h : Aligned ctx base root level (level - 1) numcells st) (hlevel : 0 < level) :
    Aligned ctx base root level level numcells (compareCodes level code st) := by
  have heq := compareCodes_eqlev level code st
  have htc : (compareCodes level code st).firsttc = st.firsttc :=
    congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      ((referencePolicy ctx 0 0).compare level code st)
  obtain ⟨hl, hp, _, _⟩ := compareCodes_frame level code st
  constructor
  · rw [heq]
    split <;> have := h.bound <;> omega
  · intro hmatch
    have hold : st.eqlevFirst = level - 1 := by
      rw [heq] at hmatch
      split at hmatch
      · exact ‹st.eqlevFirst = level - 1 ∧ code = st.firstcode[level]!›.1
      · have := h.bound
        omega
    rw [htc]
    exact (h.descent hold).congr hl hp

/-- A target mismatch discards alignment; every retained comparison keeps it. -/
theorem Aligned.target {ctx : Ctx n} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : Aligned ctx base root level level numcells st) :
    Aligned ctx base root level level numcells
      (chooseTarget false ctx tcLevel level numcells st).2.2.2 := by
  obtain ⟨hl, hp, _, _⟩ := chooseTarget_frame false ctx tcLevel level numcells st
  exact h.mono (chooseTarget_le ctx tcLevel level numcells st)
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      ((referencePolicy ctx 0 tcLevel).target level numcells st)) hl hp

/-- Classification does not change the aligned partition or its comparison. -/
theorem Aligned.classify {ctx : Ctx n} {base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : Aligned ctx base root level level numcells st) :
    Aligned ctx base root level level numcells (classify ctx level numcells st).2 := by
  obtain ⟨hl, hp, _, _⟩ := classify_frame ctx level numcells st
  exact h.mono (Nat.le_of_eq (classify_eqlev ctx level numcells st))
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (classify_reference ctx level numcells st)) hl hp

/-- Leaf actions retain the current descent, including when returning to an ancestor. -/
theorem Aligned.leaf {ctx : Ctx n} {base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : Aligned ctx base root level level numcells st) (leaf : Leaf) :
    Aligned ctx base root level level numcells (leafExit leaf level st).2 := by
  obtain ⟨hl, hp, _, _⟩ := leafExit_frame leaf level st
  exact h.mono (Nat.le_of_eq (leafExit_eqlev leaf level st))
    (congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      (leafExit_reference leaf level st)) hl hp

/-- Testing whether a partition is cheap changes only the cheap boundary. -/
theorem Aligned.cheap {ctx : Ctx n} {base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : Aligned ctx base root level level numcells st) (first : Bool) :
    Aligned ctx base root level level numcells (cheapCheck first level st) := by
  unfold cheapCheck
  split
  · exact h.mono (Nat.le_refl _) rfl rfl rfl
  · exact h

/-- A surviving target choice agrees with the recorded first-path target. -/
theorem Aligned.target_eq {ctx : Ctx n} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : Aligned ctx base root level level numcells st)
    (href : FirstRef ctx tcLevel base root st) (hdepth : Depth href.last st)
    (hkeep : (chooseTarget false ctx tcLevel level numcells st).2.2.2.eqlevFirst = level)
    (hnc : numcells < n) (hlevel : 0 < level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsmall : SubtreeOk ctx base root) :
    (chooseTarget false ctx tcLevel level numcells st).1 = st.firsttc[level]! := by
  have heq : st.eqlevFirst = level := by
    have := chooseTarget_le ctx tcLevel level numcells st
    have := h.bound
    omega
  exact (h.descent heq).target href hdepth heq hkeep hnc hlevel hgsz hsymm hloop hsmall

/-- Individualization prepares the next pending history, for either parent-sweep flag. -/
theorem Aligned.child {G : Colored n k} {ctx : Ctx n} {base level numcells tc tv : Nat}
    {root : RefineSt n} {st : Search n} {cell : VSet n}
    (h : Aligned ctx base root level level numcells st) (first : Bool)
    (hsize : ctx.g.size = n) (hroot : IterOk ctx base root)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true)
    (hrecord : st.eqlevFirst = level → st.firsttc[level]! = Int.ofNat tc) :
    let next := child first level tc tv st
    let r := visit ctx (level + 1) (numcells + 1) next
    Aligned ctx base root (level + 1) level r.1 r.2.2 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · cases first <;> exact h.bound
  · intro heq
    have heq' : st.eqlevFirst = level := by cases first <;> exact heq
    have hn0 : 0 < n := by have := VSet.mem_lt htv; omega
    have hnext := ((reachPolicy G ctx 0 hn0).child first level numcells tc tv cell st
      hlevel hok htarget htv).1
    obtain ⟨len, hcell, hmem⟩ := htarget
    obtain ⟨hic, hlen, hrange⟩ := hcell (mem_ne_empty htv)
    obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (hmem tv htv)
    have hltn : level < n := by
      have hbc := hnext.bc
      have hb := bcount_le (Nauty.child first level tc tv st).ptn (level + 1) n
      change level + 1 ≤ bcount (Nauty.child first level tc tv st).ptn (level + 1) n at hbc
      omega
    have hcell' : (tc, tc + len - 1) ∈ cells st.ptn level n := by
      exact isCell_mem_cells hic (by change n ≤ st.ptn.size; rw [hok.ptnSize]; exact Nat.le_refl _) (searchOk_end hn0 hok hlevel) (by omega)
    have hh := (h.descent heq').child (o := o) hsize hroot hltn hcell' (by omega) (by omega)
      (hrecord heq')
    change st.lab[tc + o]! = tv at he
    rw [he] at hh
    let current := (Nauty.child false level tc tv st).refined ctx (level + 1) (numcells + 1)
    refine ⟨current, ?_, ?_, ?_, ?_⟩
    · cases first <;> exact hh
    · cases first <;> rfl
    · cases first <;> rfl
    · cases first <;> rfl

/-- Recovery bounds first-code agreement by the receiving frame. -/
theorem recover_eqlev (inf level : Nat) (st : Search n) :
    (Nauty.recover inf level st).eqlevFirst = min st.eqlevFirst level := by
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.eqlevFirst, ite_self]
  split <;> omega

/-- A child that cannot restore an earlier divergence retains the parent history on recovery. -/
theorem Aligned.recover {G : Colored n k} {ctx : Ctx n} {base level numcells : Nat}
    {root : RefineSt n} {st out : Search n}
    (h : Aligned ctx base root level level numcells st)
    (hok : SearchOk G level numcells st)
    (hout : SearchOut G level level st out)
    (htc : out.firsttc = st.firsttc)
    (hdiv : st.eqlevFirst < level → out.eqlevFirst < level) :
    Aligned ctx base root level level numcells
      (Nauty.recover (n + 2) level out) := by
  constructor
  · rw [recover_eqlev]
    omega
  · intro hmatch
    have hold : st.eqlevFirst = level := by
      by_cases heq : st.eqlevFirst = level
      · exact heq
      · have hb := h.bound
        have hd := hdiv (by omega)
        rw [recover_eqlev] at hmatch
        omega
    have hs : (Nauty.recover (n + 2) level out).firsttc = st.firsttc := by
      have href := (referencePolicy ctx (n + 2) 0).recover level out
      have h := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) href
      exact h.trans htc
    rw [hs]
    exact (h.descent hold).recover hok hout

/-- An actual off-path child return has precisely the divergence and frame
properties required to recover its parent's aligned history. -/
theorem Aligned.child_return {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel base level numcells tc tv : Nat}
    {root : RefineSt n} {st : Search n} {cell : VSet n}
    (h : Aligned ctx base root level level numcells st) (first : Bool)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2
    Aligned ctx base root level level numcells
      (Nauty.recover (n + 2) level { out with fixedpts := out.fixedpts.erase tv }) := by
  let ch := Nauty.child first level tc tv st
  let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  have hn0 : 0 < n := by have := VSet.mem_lt htv; omega
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hlevel hok htarget htv
  have hresult := node_out false hn0 (by omega) hch.1 (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
  have hout : SearchOut G level level st out := hch.2 _ (by simpa only [Nat.add_sub_cancel, policy, Generic.Policy.child] using hresult)
  have htc : out.firsttc = st.firsttc := by
    have hr := node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch
    have hc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hr
    change out.firsttc = ch.firsttc at hc
    cases first <;> exact hc
  have hd : st.eqlevFirst < level → out.eqlevFirst < level := by
    intro hlow
    apply node_diverged (by omega)
    cases first <;> exact hlow
  apply h.recover hok
  · exact hout.congr rfl rfl rfl rfl
  · exact htc
  · exact hd

end Hex.GraphIso.Nauty
