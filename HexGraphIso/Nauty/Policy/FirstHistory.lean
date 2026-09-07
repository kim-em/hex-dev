/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstPath
public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.Equitable.Root
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- The refinement state at a search node, before target bookkeeping. -/
def Search.refined (ctx : Ctx n) (level numcells : Nat) (st : Search n) : RefineSt n :=
  refine ctx level st.lab st.ptn st.active numcells

/-- First-path preparation retains the refined partition and writes its target. -/
theorem prepareFirst_fields (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    r.2.2.2.2.lab = (st.refined ctx level numcells).lab ∧
    r.2.2.2.2.ptn = (st.refined ctx level numcells).ptn ∧
    r.2.2.2.2.firsttc = st.firsttc.set! level r.2.1 := by
  unfold Generic.prepareFirst
  change (chooseTarget true ctx tcLevel level _ _).2.2.2.lab = _ ∧
    (chooseTarget true ctx tcLevel level _ _).2.2.2.ptn = _ ∧
    (chooseTarget true ctx tcLevel level _ _).2.2.2.firsttc = _
  rw [chooseFirst_fields]
  exact ⟨rfl, rfl, rfl⟩

/-- The child's refinement is exactly the mathematical individualization step. -/
theorem firstChild_refined (ctx : Ctx n) (tcLevel level numcells tv : Nat) (st : Search n) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    (child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)).refined
      ctx (level + 1) (r.1 + 1) =
    childSt ctx level (st.refined ctx level numcells) r.2.1.toNat tv := by
  obtain ⟨hl, hp, _⟩ := prepareFirst_fields ctx tcLevel level numcells st
  dsimp only
  unfold cheapCheck
  split
  all_goals
    change refine ctx (level + 1)
      (breakout n (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.lab
        (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.ptn
        (level + 1) (Generic.prepareFirst ctx tcLevel level numcells st).2.1.toNat tv).1
      (Array.set! (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.ptn
        (Generic.prepareFirst ctx tcLevel level numcells st).2.1.toNat (level + 1))
      (VSet.empty.insert (Generic.prepareFirst ctx tcLevel level numcells st).2.1.toNat)
      ((Generic.prepareFirst ctx tcLevel level numcells st).1 + 1) = _
  all_goals rw [hl, hp]
  all_goals rfl

/-- The first descent never changes a target slot above its current level. -/
theorem firstPath_before {ctx : Ctx n} {tcLevel fuel level numcells last slot : Nat}
    {st leaf : Search n}
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hslot : slot < level) : leaf.firsttc[slot]! = st.firsttc[slot]! := by
  induction hpath with
  | leaf fuel level numcells st hdisc =>
    rw [(prepareFirst_fields ctx tcLevel level numcells st).2.2]
    exact Array.getElem!_set!_ne _ _ _ _ (by omega)
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih (by omega)]
    change (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).firsttc[slot]! = _
    unfold cheapCheck
    split
    all_goals try dsimp only
    all_goals rw [(prepareFirst_fields ctx tcLevel level numcells st).2.2]
    all_goals exact Array.getElem!_set!_ne _ _ _ _ (by omega)

/-- The target array retains its allocated size along the first descent. -/
theorem firstPath_size {ctx : Ctx n} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf) :
    leaf.firsttc.size = st.firsttc.size := by
  induction hpath with
  | leaf fuel level numcells st hdisc =>
    rw [(prepareFirst_fields ctx tcLevel level numcells st).2.2, Array.size_set!]
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih]
    change (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).firsttc.size = _
    unfold cheapCheck
    split
    all_goals try dsimp only
    all_goals rw [(prepareFirst_fields ctx tcLevel level numcells st).2.2, Array.size_set!]

/-- A valid node's refinement has the state invariant used by descent paths. -/
theorem refined_iter {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) :
    IterOk ctx level (st.refined ctx level numcells) := by
  have hend := searchOk_end hn0 hok hlevel
  have hr := refine_stOk (ctx := ctx) (active := st.active) (numcells := numcells)
    hok.labSize (labOk_of_reach hok.labSize hok.reach) hok.ptnSize hend
  have hv := ((reachPolicy G ctx 100 hn0).visit level numcells st hlevel hok).1
  refine ⟨hr, labInj_of_reach hr.labSize hn0 hv.reach, ?_, ?_⟩
  · intro q hq
    rcases ptn_refine_vals ctx level st.lab st.ptn st.active numcells q with he | he
    · change (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! = _ at he
      change (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! ≤ level ∨
        (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! = n + 2
      rw [he]
      exact hok.vals q hq
    · change (refine ctx level st.lab st.ptn st.active numcells).ptn[q]! = _ at he
      exact Or.inl (Nat.le_of_eq he)
  · have := hok.bc
    have := bcount_le st.view.ptn level n
    omega

/-- A first-path target uses the unhinted specification rule. -/
theorem prepareFirst_choice {ctx : Ctx n} {tcLevel level numcells : Nat} {st : Search n}
    (hopen : (Generic.prepareFirst ctx tcLevel level numcells st).1 ≠ n)
    (hit : IterOk ctx level (st.refined ctx level numcells))
    (heq : Equitable ctx level (st.refined ctx level numcells).lab
      (st.refined ctx level numcells).ptn) :
    (Generic.prepareFirst ctx tcLevel level numcells st).2.1 =
      Int.ofNat (specTargetcell ctx (st.refined ctx level numcells).lab
        (st.refined ctx level numcells).ptn level tcLevel) := by
  have hm := maketargetcell_eq_spec (tcLevel := tcLevel) heq hit.ok.labOk
    hit.ok.labSize hit.ok.ptnSize hit.ok.ptnEnd
  change (st.refined ctx level numcells).numcells ≠ n at hopen
  unfold Generic.prepareFirst
  change (chooseTarget true ctx tcLevel level (st.refined ctx level numcells).numcells
    (recordFirst level (st.refined ctx level numcells).longcode
      (visit ctx level numcells st).2.2)).1 = _
  unfold chooseTarget
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
    bne_iff_ne.mpr hopen, Id.run_pure]
  change Int.ofNat (maketargetcell ctx (st.refined ctx level numcells).lab
    (st.refined ctx level numcells).ptn level tcLevel (-1)).1 = _
  rw [hm]
  rfl

/-- A selected child of the prepared first path has a valid entry partition. -/
theorem firstChild_ok {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells tv : Nat} {st : Search n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view)
    (htv : (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1.nextElem none = some tv) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    SearchOk G (level + 1) (r.1 + 1)
      (child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)).view := by
  let r := Generic.prepareFirst ctx tcLevel level numcells st
  obtain ⟨hr, ht⟩ := prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hok
  have hc := (reachPolicy G ctx tcLevel hn0).cheap true level r.1 r.2.2.2.2 hr
  exact ((reachPolicy G ctx tcLevel hn0).child true level r.1 r.2.1.toNat tv r.2.2.1
    (cheapCheck true level r.2.2.2.2) hlevel hc.1 (ht.of_out hc.2)
    (VSet.nextElem_mem htv)).1

/-- A stored head target and its suffix form one consecutive history. -/
theorem Targets.cons {store : Array Int} {base tc : Nat} {xs : List Nat}
    (hhead : store[base]! = Int.ofNat tc) (htail : Targets store (base + 1) xs) :
    Targets store base (tc :: xs) := by
  intro i hi
  cases i with
  | zero => simpa using hhead
  | succ i =>
    simpa only [List.getElem!_cons_succ, show base + (i + 1) = base + 1 + i by omega]
      using htail i (by simpa using hi)

/-- The actual first descent yields a selected mathematical path whose
target positions are retained in the final first-target array. -/
theorem firstPath_history {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells last : Nat} {st leaf : Search n}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view)
    (heq : Equitable ctx level (st.refined ctx level numcells).lab
      (st.refined ctx level numcells).ptn)
    (hsize : n < st.firsttc.size) :
    ∃ path U, DescPath ctx level (st.refined ctx level numcells) path last U ∧
      Selects ctx tcLevel level (st.refined ctx level numcells) path ∧
      Targets leaf.firsttc level (path.map Prod.fst) ∧
      U.lab = leaf.lab ∧ U.ptn = leaf.ptn ∧ (∀ i, i < n → U.ptn[i]! ≤ last) := by
  induction hpath with
  | leaf fuel level numcells st hdisc =>
    let U := st.refined ctx level numcells
    obtain ⟨hl, hp, _⟩ := prepareFirst_fields ctx tcLevel level numcells st
    refine ⟨[], U, .refl _ _, trivial, (fun _ h => by simp at h), hl.symm, hp.symm, ?_⟩
    have hr := (prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hok).1
    have hc : n = bcount U.ptn level n := by
      have h := hdisc.symm.trans hr.count
      change n = bcount (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.ptn level n at h
      simpa only [hp] using h
    have hall : (List.range n).countP (fun i => decide (U.ptn[i]! ≤ level)) =
        (List.range n).length := by
      simpa only [bcount, List.length_range] using hc.symm
    intro i hi
    exact of_decide_eq_true (List.countP_eq_length.mp hall i (List.mem_range.mpr hi))
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let R := st.refined ctx level numcells
    have hit := refined_iter (ctx := ctx) hn0 hlevel hok
    obtain ⟨hr, ht⟩ := prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hok
    obtain ⟨hl, hp, hstore⟩ := prepareFirst_fields ctx tcLevel level numcells st
    have hnc : r.1 < n := by
      have hc : r.1 = bcount r.2.2.2.2.view.ptn level n := hr.count
      have hb := bcount_le r.2.2.2.2.view.ptn level n
      change r.1 ≠ n at hopen
      omega
    have hlt : level < n := by
      have hc : r.1 = bcount r.2.2.2.2.view.ptn level n := hr.count
      have hb : level ≤ bcount r.2.2.2.2.view.ptn level n := hr.bc
      omega
    have hmem := VSet.nextElem_mem htv
    obtain ⟨len, htcell, hseg⟩ := ht
    obtain ⟨hcell, hlen, hrange⟩ := htcell (mem_ne_empty hmem)
    change r.2.1.toNat + len ≤ n at hrange
    obtain ⟨o, ho, hlabel⟩ := mem_segN_iff.mp (hseg tv hmem)
    change r.2.2.2.2.lab[r.2.1.toNat + o]! = tv at hlabel
    rw [hl] at hlabel
    have hcellR : IsCell R.ptn level r.2.1.toNat len := by
      change IsCell r.2.2.2.2.ptn level r.2.1.toNat len at hcell
      rw [hp] at hcell
      exact hcell
    have hc : (r.2.1.toNat, r.2.1.toNat + len - 1) ∈ cells R.ptn level n :=
      isCell_mem_cells hcellR (by rw [hit.ok.ptnSize]; exact Nat.le_refl _) hit.ok.ptnEnd (by omega)
    have hne : r.2.1.toNat < r.2.1.toNat + len - 1 := by omega
    have ho' : o ≤ r.2.1.toNat + len - 1 - r.2.1.toNat := by omega
    have hchoice := prepareFirst_choice hopen hit heq
    have htarget : specTargetcell ctx R.lab R.ptn level tcLevel = r.2.1.toNat := by
      change r.2.1 = Int.ofNat (specTargetcell ctx R.lab R.ptn level tcLevel) at hchoice
      rw [hchoice]
      rfl
    have hacc : bcount R.ptn level n = R.numcells := by
      have h := hr.count
      change r.1 = bcount r.2.2.2.2.ptn level n at h
      rw [hp] at h
      exact h.symm
    have heqchild := equitable_breakout hit.ok.labSize hit.ok.ptnSize hit.ok.ptnEnd
      hit.valsWeak hit.ok.labOk hit.inj hsymm heq hc hne ho' hacc
    let child := Engine.child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)
    have hchild := firstChild_ok hn0 hlevel hok htv
    have hstep : child.refined ctx (level + 1) (r.1 + 1) =
        childSt ctx level R r.2.1.toNat R.lab[r.2.1.toNat + o]! := by
      rw [firstChild_refined, ← hlabel]
    have hce : Equitable ctx (level + 1) (child.refined ctx (level + 1) (r.1 + 1)).lab
        (child.refined ctx (level + 1) (r.1 + 1)).ptn := by
      rw [hstep]
      exact heqchild
    have hcs : n < child.firsttc.size := by
      change n < (cheapCheck true level r.2.2.2.2).firsttc.size
      unfold cheapCheck
      split
      all_goals try dsimp only
      all_goals rw [hstore, Array.size_set!]
      all_goals exact hsize
    obtain ⟨path, U, hdesc, hsel, htargets, hUL, hUP, hdisc⟩ := ih (by omega) hchild hce hcs
    change DescPath ctx (level + 1) (child.refined ctx (level + 1) (r.1 + 1)) path last U at hdesc
    change Selects ctx tcLevel (level + 1) (child.refined ctx (level + 1) (r.1 + 1)) path at hsel
    rw [hstep] at hdesc hsel
    refine ⟨(r.2.1.toNat, o) :: path, U, .step _ _ _ hlt hc hne ho' hdesc,
      ⟨htarget, hsel⟩, Targets.cons ?_ htargets, hUL, hUP, hdisc⟩
    rw [firstPath_before tail (by omega)]
    have hw : child.firsttc[level]! = (st.firsttc.set! level r.2.1)[level]! := by
      change (cheapCheck true level r.2.2.2.2).firsttc[level]! = _
      unfold cheapCheck
      split
      all_goals try dsimp only
      all_goals rw [hstore]
      all_goals rfl
    change child.firsttc[level]! = Int.ofNat r.2.1.toNat
    rw [hw]
    change (st.firsttc.set! level r.2.1)[level]! = _
    rw [Array.getElem!_set!_self _ _ _ (by omega), hchoice]
    rfl

/-- The saved first reference carries the selected descent history even
after the full engine call has searched later siblings. -/
theorem firstPath_saved {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel fuel level numcells last : Nat} {st leaf : Search n}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view)
    (heq : Equitable ctx level (st.refined ctx level numcells).lab
      (st.refined ctx level numcells).ptn)
    (hsize : n < st.firsttc.size) :
    let out := (node true ctx inf tcLevel fuel level numcells st).2
    ∃ path U, DescPath ctx level (st.refined ctx level numcells) path last U ∧
      Selects ctx tcLevel level (st.refined ctx level numcells) path ∧
      Targets out.firsttc level (path.map Prod.fst) ∧
      U.lab = out.firstlab ∧ (∀ i, i < n → U.ptn[i]! ≤ last) := by
  obtain ⟨path, U, hd, hs, ht, hl, _, hdisc⟩ :=
    firstPath_history hn0 hsymm hpath hlevel hok heq hsize
  have href := firstPath_reference (inf := inf) hpath
  have htc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) href
  have hfirst := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2) href
  change (node true ctx inf tcLevel fuel level numcells st).2.firsttc =
    leaf.firsttc.set! (last + 1) (-1) at htc
  change (node true ctx inf tcLevel fuel level numcells st).2.firstlab = leaf.lab at hfirst
  refine ⟨path, U, hd, hs, ?_, hl.trans hfirst.symm, hdisc⟩
  rw [htc]
  apply ht.set_after
  have hlen := hd.length
  simp only [List.length_map]
  omega

/-- The initial colour partition refines to an equitable root. -/
theorem initial_equitable (G : Colored n k) (hn0 : 0 < n) :
    let st := initial n (initialPartition G).1 (initialPartition G).2
    let r := st.refined { g := rowsOf G } 1 (initialPartition G).2.length
    Equitable { g := rowsOf G } 1 r.lab r.ptn := by
  have hok := initial_ok G hn0
  apply refine_equitable hok.labSize (labOk_of_reach hok.labSize hok.reach)
    hok.ptnSize (searchOk_end hn0 hok (Nat.le_refl _))
    (labInj_of_reach hok.labSize hn0 hok.reach)
    (initial_nodeOk G hn0).starts
    (rowsOf_symm G) hok.count.symm (certInv_initial G hn0)

/-- A nonempty engine run stores the leaf of a selected descent from the
refined colour partition, together with its complete target history. -/
theorem runState_history (G : Colored n k) (hn0 : 0 < n) :
    let st := initial n (initialPartition G).1 (initialPartition G).2
    let out := (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2
    ∃ last path U,
      DescPath { g := rowsOf G } 1 (st.refined { g := rowsOf G } 1
        (initialPartition G).2.length) path last U ∧
      Selects { g := rowsOf G } 100 1 (st.refined { g := rowsOf G } 1
        (initialPartition G).2.length) path ∧
      Targets out.firsttc 1 (path.map Prod.fst) ∧
      U.lab = out.firstlab ∧ (∀ i, i < n → U.ptn[i]! ≤ last) := by
  have horbit : ∀ v, v < n →
      (initial n (initialPartition G).1 (initialPartition G).2).orbits[v]! = v := by
    intro v hv
    change (Array.ofFn (n := n) fun i : Fin n => i.val)[v]! = v
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]
  obtain ⟨last, leaf, hpath⟩ := firstPath_exists (ctx := { g := rowsOf G })
    (tcLevel := 100) (fuel := n + 2) hn0 (Nat.le_refl _) (initial_ok G hn0) horbit (by omega)
  have hs := firstPath_saved (inf := n + 2) hn0 (rowsOf_symm G) hpath (Nat.le_refl _)
    (initial_ok G hn0) (initial_equitable G hn0) (by simp [initial])
  refine ⟨last, ?_⟩
  unfold runState
  rw [ite_eq_right (show (n == 0) ≠ true by simp; omega)]
  exact hs

end Hex.GraphIso.Nauty.Engine
