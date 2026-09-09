/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- At a cheap first-path ancestor, retain its saved first descent and the
current descent selected by the live agreement counter. -/
def CheapHistory (ctx : Ctx n) (tcLevel level agreed numcells : Nat) (st : Search n) : Prop :=
  st.noncheaplevel ≤ st.gcaFirst →
    ∃ root, ∃ href : FirstRef ctx tcLevel st.gcaFirst root st,
      Depth href.last st ∧ SubtreeOk ctx st.gcaFirst root ∧
      Aligned ctx st.gcaFirst root level agreed numcells st

/-- Transport a frozen first ancestor through a local operation. -/
theorem CheapHistory.transport {ctx : Ctx n} {tcLevel level agreed numcells level' agreed' numcells' : Nat}
    {st out : Search n} (h : CheapHistory ctx tcLevel level agreed numcells st)
    (hr : out.reference = st.reference) (hg : out.gcaFirst = st.gcaFirst)
    (hn : out.noncheaplevel ≤ st.gcaFirst → st.noncheaplevel ≤ st.gcaFirst)
    (hd : ∀ last, Depth last st → Depth last out)
    (ha : ∀ root, Aligned ctx st.gcaFirst root level agreed numcells st →
      Aligned ctx st.gcaFirst root level' agreed' numcells' out) :
    CheapHistory ctx tcLevel level' agreed' numcells' out := by
  intro hcheap
  rw [hg] at hcheap ⊢
  obtain ⟨root, href, hdepth, hsmall, halign⟩ := h (hn hcheap)
  exact ⟨root, href.congr hr, hd href.last hdepth, hsmall, ha root halign⟩

/-- Code comparison retains the frozen ancestor and activates the pending node history. -/
theorem CheapHistory.compare {ctx : Ctx n} {tcLevel level numcells code : Nat} {st : Search n}
    (h : CheapHistory ctx tcLevel level (level - 1) numcells st)
    (hlevel : 0 < level) (hcode : code < codeSentinel) :
    CheapHistory ctx tcLevel level level numcells (compareCodes level code st) := by
  apply h.transport (out := compareCodes level code st) ((referencePolicy ctx 0 tcLevel).compare level code st)
    ((gcaPolicy ctx 0 tcLevel).compare level code st)
  · unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.noncheaplevel, ite_self]
    exact id
  · intro last hd
    exact compareCodes_depth hd hcode
  · intro root ha
    exact ha.compare hlevel

/-- A retained target comparison preserves its history and saved sentinel bound. -/
theorem CheapHistory.target {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : CheapHistory ctx tcLevel level level numcells st) :
    CheapHistory ctx tcLevel level level numcells (chooseTarget false ctx tcLevel level numcells st).2.2.2 := by
  have hr := (referencePolicy ctx 0 tcLevel).target level numcells st
  apply h.transport hr ((gcaPolicy ctx 0 tcLevel).target level numcells st)
  · change (chooseTarget false ctx tcLevel level numcells st).2.2.2.noncheaplevel ≤ st.gcaFirst → _
    rw [chooseTarget_fields]
    exact id
  · intro last hd
    exact hd.mono (chooseTarget_le ctx tcLevel level numcells st) hr
  · intro root ha
    exact ha.target

/-- Classification preserves the live first-path history. -/
theorem CheapHistory.classify {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : CheapHistory ctx tcLevel level level numcells st) :
    CheapHistory ctx tcLevel level level numcells (Nauty.classify ctx level numcells st).2 := by
  apply h.transport (classify_reference ctx level numcells st)
    ((gcaPolicy ctx 0 tcLevel).classify level numcells st)
  · unfold Nauty.classify
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
      apply_ite Search.noncheaplevel, ite_self]
    exact id
  · intro last hd
    exact hd.mono (Nat.le_of_eq (classify_eqlev ctx level numcells st))
      (classify_reference ctx level numcells st)
  · intro root ha
    exact ha.classify

/-- Leaf actions preserve the live first-path history until the receiving frame recovers it. -/
theorem CheapHistory.leaf {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : CheapHistory ctx tcLevel level level numcells st) (leaf : Leaf) :
    CheapHistory ctx tcLevel level level numcells (leafExit leaf level st).2 := by
  apply h.transport (leafExit_reference leaf level st) (leafExit_gca leaf level st)
  · rw [leafExit_noncheap]
    exact id
  · intro last hd
    exact hd.mono (Nat.le_of_eq (leafExit_eqlev leaf level st)) (leafExit_reference leaf level st)
  · intro root ha
    exact ha.leaf leaf

/-- A failed guard below the first ancestor cannot make that ancestor cheap. -/
theorem CheapHistory.cheap {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : CheapHistory ctx tcLevel level level numcells st) (first : Bool)
    (hg : st.gcaFirst ≤ level) :
    CheapHistory ctx tcLevel level level numcells (cheapCheck first level st) := by
  apply h.transport (out := cheapCheck first level st) ((referencePolicy ctx 0 tcLevel).cheap first level st)
    ((gcaPolicy ctx 0 tcLevel).cheap first level st)
  · unfold cheapCheck
    split
    · change level + 1 ≤ st.gcaFirst → _
      omega
    · exact id
  · intro last hd
    unfold cheapCheck
    split <;> exact hd
  · intro root ha
    exact ha.cheap first

/-- The sweep target is recorded whenever cheap first-path agreement is retained. -/
def CheapRecorded (level tc : Nat) (st : Search n) : Prop :=
  st.noncheaplevel ≤ st.gcaFirst → st.eqlevFirst = level → st.firsttc[level]! = Int.ofNat tc

/-- A cheap-boundary update retains the recorded target when its ancestor remains cheap. -/
theorem CheapRecorded.cheap {level tc : Nat} {st : Search n}
    (h : CheapRecorded level tc st) (first : Bool) (hg : st.gcaFirst ≤ level) :
    CheapRecorded level tc (cheapCheck first level st) := by
  unfold cheapCheck
  split
  · intro hc
    change level + 1 ≤ st.gcaFirst at hc
    omega
  · exact h

/-- A target selected at a cheap ancestor is the stored target position. -/
theorem CheapHistory.recorded {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (h : CheapHistory ctx tcLevel level level numcells st) (hnc : numcells < n) (hlevel : 0 < level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let r := chooseTarget false ctx tcLevel level numcells st
    CheapRecorded level r.1.toNat r.2.2.2 := by
  intro r hcheap hkeep
  have hg : r.2.2.2.gcaFirst = st.gcaFirst := (gcaPolicy ctx 0 tcLevel).target level numcells st
  have hn : r.2.2.2.noncheaplevel = st.noncheaplevel := by
    dsimp only [r]
    rw [chooseTarget_fields]
  have ht : r.2.2.2.firsttc = st.firsttc :=
    congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
      ((referencePolicy ctx 0 tcLevel).target level numcells st)
  obtain ⟨root, href, hd, hs, ha⟩ := h (by rwa [hg, hn] at hcheap)
  have hpos := ha.target_eq href hd hkeep hnc hlevel hgsz hsymm hloop hs
  have hold : st.eqlevFirst = level := by
    have hb := ha.bound
    have hle := chooseTarget_le ctx tcLevel level numcells st
    change r.2.2.2.eqlevFirst ≤ st.eqlevFirst at hle
    omega
  change r.2.2.2.firsttc[level]! = Int.ofNat r.1.toNat
  rw [ht, chooseTarget_cast hnc hold]
  exact hpos.symm

/-- A sweep's stored target prepares the next actual child history. -/
theorem CheapHistory.child {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells tc tv : Nat}
    {st : Search n} {cell : VSet n}
    (h : CheapHistory ctx tcLevel level level numcells st) (first : Bool)
    (hsize : ctx.g.size = n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true)
    (hrecord : CheapRecorded level tc st) :
    let next := Nauty.child first level tc tv st
    let r := visit ctx (level + 1) (numcells + 1) next
    CheapHistory ctx tcLevel (level + 1) level r.1 r.2.2 := by
  intro next r hcheap
  have hg : r.2.2.gcaFirst = st.gcaFirst := by cases first <;> rfl
  have hn : r.2.2.noncheaplevel = st.noncheaplevel := by cases first <;> rfl
  have hr : r.2.2.reference = st.reference := by cases first <;> rfl
  have hc : st.noncheaplevel ≤ st.gcaFirst := by rwa [hg, hn] at hcheap
  obtain ⟨root, href, hd, hs, ha⟩ := h hc
  rw [hg]
  refine ⟨root, href.congr hr, ?_, hs, ?_⟩
  · cases first <;> exact hd
  · exact ha.child first hsize hs.it hlevel hok htarget htv (hrecord hc)

/-- Recovering an actual child preserves the history at its receiving ancestor. -/
theorem CheapHistory.child_return {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {st : Search n} {cell : VSet n}
    (h : CheapHistory ctx tcLevel level level numcells st) (first : Bool)
    (hg : st.gcaFirst ≤ level) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2
    let result := recoverLevels level (recoverPtn (n + 2) level
      { out with fixedpts := out.fixedpts.erase tv })
    CheapHistory ctx tcLevel level level numcells result ∧ (CheapRecorded level tc st → CheapRecorded level tc result) := by
  let ch := Nauty.child first level tc tv st
  let out := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  let left := { out with fixedpts := out.fixedpts.erase tv }
  let result := recoverLevels level (recoverPtn (n + 2) level left)
  have hrch : ch.reference = st.reference := by cases first <;> rfl
  have hrout : out.reference = st.reference :=
    (node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).trans hrch
  have hr : result.reference = st.reference :=
    ((referencePolicy ctx (n + 2) tcLevel).recover level left).trans hrout
  have hgout : out.gcaFirst = st.gcaFirst := by
    have hc : ch.gcaFirst = st.gcaFirst := by cases first <;> rfl
    exact (node_gca ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).trans hc
  have hgr : result.gcaFirst = st.gcaFirst :=
    ((gcaPolicy ctx (n + 2) tcLevel).recover level left).trans hgout
  have cheapBack : result.noncheaplevel ≤ result.gcaFirst → st.noncheaplevel ≤ st.gcaFirst := by
    intro hcheap
    by_cases hc : st.noncheaplevel ≤ st.gcaFirst
    · exact hc
    · have hch : st.gcaFirst < ch.noncheaplevel := by cases first <;> exact Nat.lt_of_not_ge hc
      have ho : st.gcaFirst < out.noncheaplevel := node_noncheap (by omega) hch
      rw [hgr, show result.noncheaplevel =
        if level < left.noncheaplevel then level + 1 else left.noncheaplevel from
          recover_noncheap (n + 2) level left] at hcheap
      change st.gcaFirst < left.noncheaplevel at ho
      split at hcheap <;> omega
  change CheapHistory ctx tcLevel level level numcells result ∧ (CheapRecorded level tc st → CheapRecorded level tc result)
  constructor
  · intro hcheap
    obtain ⟨root, href, hd, hs, ha⟩ := h (cheapBack hcheap)
    rw [hgr]
    refine ⟨root, href.congr hr, ?_, hs, ha.child_return first hlevel hok htarget htv⟩
    have hdch : Depth href.last ch := by cases first <;> exact hd
    have hdout : Depth href.last out := node_depth hdch
    exact hdout.mono (recover_le (n + 2) level left)
      ((referencePolicy ctx (n + 2) tcLevel).recover level left)
  · intro hrecord hcheap hmatch
    have hc := cheapBack hcheap
    obtain ⟨root, href, hd, hs, ha⟩ := h hc
    have heq : st.eqlevFirst = level := by
      by_cases heq : st.eqlevFirst = level
      · exact heq
      · have hb := ha.bound
        have hch : ch.eqlevFirst < level := by cases first <;> change st.eqlevFirst < level <;> omega
        have ho : out.eqlevFirst < level := node_diverged (by omega) hch
        have hl := recover_le (n + 2) level left
        change result.eqlevFirst ≤ out.eqlevFirst at hl
        omega
    have ht := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) hr
    change result.firsttc = st.firsttc at ht
    rw [ht]
    exact hrecord hc heq

/-- The live history supplies the restored first-leaf admission test at every prepared node. -/
theorem CheapHistory.first_checked {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st out : Search n} (h : CheapHistory ctx tcLevel level level numcells st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hok : SearchOk G level numcells st)
    (hauto : Nauty.classify ctx level numcells st = (.autoFirst, out))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    checkAutom ctx.g out.workperm = true := by
  by_cases hc : st.noncheaplevel ≤ st.gcaFirst
  · obtain ⟨root, href, hd, hs, ha⟩ := h hc
    exact ha.first_checked href hd hs hok hauto hinv.scratch hgsz hsymm hloop
  · exact classify_first_scanned hauto (by omega) hinv.scratch hinv.firstSize hinv.first
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach) hsymm hloop

/-- Both automorphism classifications produce a checked scratch permutation. -/
theorem CheapHistory.checked {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (h : CheapHistory ctx tcLevel level level numcells st)
    (hinv : RunInv G ctx st) (hn0 : 0 < n) (hok : SearchOk G level numcells st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let r := Nauty.classify ctx level numcells st
    r.1 = .autoFirst ∨ r.1 = .autoCanon → checkAutom ctx.g r.2.workperm = true := by
  intro r hauto
  rcases hauto with hf | hc
  · exact h.first_checked hinv hn0 hok (Prod.ext hf rfl) hgsz hsymm hloop
  · exact classify_canon_checked (Prod.ext hc rfl) hinv.cache hinv.scratch hinv.canonical.1
      (isPerm_of_cellsReach hinv.canonical.1 hn0 hinv.canonical.2)
      hok.labSize (isPerm_of_cellsReach hok.labSize hn0 hok.reach)

end Hex.GraphIso.Nauty
