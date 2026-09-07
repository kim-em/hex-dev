/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Reach
public import HexGraphIso.Nauty.Policy.Fuel
public import HexGraphIso.Nauty.Policy.Effect
public import HexGraphIso.Nauty.Policy.Engine
public import HexGraphIso.Nauty.Invariant.Reach
public import HexGraphIso.Nauty.Invariant.Autos
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.Reach
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A frame-preserving engine operation satisfies the local reach rules. -/
theorem frame_local {G : Colored n k} {level numcells : Nat} {st out : Search n}
    (hok : SearchOk G level numcells st.view)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.firstlab = st.firstlab ∨ out.firstlab = st.lab)
    (hc : out.canonlab = st.canonlab ∨ out.canonlab = st.lab) :
    Generic.Local G Search.view level numcells st out :=
  ⟨frame_ok hok hl hp hc, frame_out hok hl hp hf hc⟩

/-- A target constructed from a live partition has the cell membership
required by the generic sweep, for any target hint. -/
theorem maketargetcell_target {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {st : Search n} (hint : Int)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) (hnc : numcells < n) :
    let r := maketargetcell ctx st.lab st.ptn level tcLevel hint
    Generic.Target Search.view level r.1 r.2.1 st := by
  have hend := searchOk_end hn0 hok hlevel
  have hlive : bcount st.ptn level n < n := by
    have hcount := hok.count
    change numcells = bcount st.ptn level n at hcount
    omega
  obtain ⟨tc, len, hr, hcell, hlen, hrange⟩ :=
    maketargetcell_open (ctx := ctx) (lab := st.lab) (ptn := st.ptn) (tcLevel := tcLevel)
      (hint := hint) hlevel hok.ptnSize hend hlive
  dsimp only
  rw [hr]
  refine ⟨len, fun _ => ⟨hcell, hlen, hrange⟩, ?_⟩
  intro v hv
  rw [mem_worksetOf] at hv
  have hm := (Bool.and_eq_true _ _).mp hv |>.2
  rw [show tc + len - 1 + 1 - tc = len by omega] at hm
  obtain ⟨w, hw, heq⟩ := List.any_eq_true.mp hm
  have hwv : w = v := beq_iff_eq.mp heq
  exact hwv ▸ hw

/-- The empty target set requires no cell witness. -/
theorem target_empty (level tc : Nat) (st : Search n) :
    Generic.Target Search.view level tc VSet.empty st :=
  ⟨0, fun h => (h rfl).elim, fun _ h => by simp at h⟩

/-- Any selected target is a nontrivial cell of the current partition.
Bookkeeping performed while selecting it does not change that partition. -/
theorem chooseTarget_target {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {st : Search n} (first : Bool)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) :
    let r := chooseTarget first ctx tcLevel level numcells st
    Generic.Target Search.view level r.1.toNat r.2.1 r.2.2.2 := by
  obtain ⟨hl, hp, hf, hc⟩ := chooseTarget_frame first ctx tcLevel level numcells st
  have hout : SearchOut G level level st.view
      (chooseTarget first ctx tcLevel level numcells st).2.2.2.view :=
    frame_out hok hl hp (Or.inl hf) (Or.inl hc)
  apply Generic.Target.of_out (hout := hout)
  unfold chooseTarget
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst,
    apply_ite Prod.snd, ite_self]
  cases first with
  | true =>
    simp only [Bool.not_true, Bool.false_and, ite_true, Bool.false_eq_true,
      ite_false]
    split
    · have hnc : numcells < n := by
        have hbound := bcount_le st.ptn level n
        have hcount := hok.count
        simp only [Search.view] at hcount
        rename_i hne
        have := bne_iff_ne.mp hne
        omega
      exact maketargetcell_target (-1) hn0 hlevel hok hnc
    · exact target_empty level _ st
  | false =>
    simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false]
    split
    · rename_i hguard
      have hnc : numcells < n := of_decide_eq_true ((Bool.and_eq_true _ _).mp hguard).1
      exact maketargetcell_target _ hn0 hlevel hok hnc
    · exact target_empty level _ st

/-- The concrete engine meets every local partition rule of the generic
search. No automorphism or comparison-correctness premise is needed. -/
theorem reachPolicy (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) (hn0 : 0 < n) :
    Generic.ReachPolicy G ctx (n + 2) tcLevel Search.view where
  visit := by
    intro level numcells st hlevel hok
    constructor
    · exact refine_searchOk hn0 hok hlevel rfl rfl (Or.inl rfl)
    · intro out hout
      exact refine_loop_out (ctx := ctx) (STL := (visit ctx level numcells st).2.2.view)
        hn0 hok hlevel rfl rfl
        (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hout
  record := by
    intro level code numcells st hok
    exact frame_local hok rfl rfl (Or.inl rfl) (Or.inl rfl)
  compare := by
    intro level code numcells st hok
    obtain ⟨hl, hp, hf, hc⟩ := compareCodes_frame level code st
    exact frame_local hok hl hp (Or.inl hf) (Or.inl hc)
  target := by
    intro first level numcells st hlevel hok
    obtain ⟨hl, hp, hf, hc⟩ := chooseTarget_frame first ctx tcLevel level numcells st
    exact ⟨frame_local hok hl hp (Or.inl hf) (Or.inl hc),
      chooseTarget_target first hn0 hlevel hok⟩
  firstterminal := by
    intro level numcells st hok
    exact frame_local hok rfl rfl (Or.inr rfl) (Or.inr rfl)
  classify := by
    intro level numcells st hok
    obtain ⟨hl, hp, hf, hc⟩ := classify_frame ctx level numcells st
    exact frame_local hok hl hp (Or.inl hf) (Or.inl hc)
  leaf := by
    intro leaf level numcells st hok
    obtain ⟨hl, hp, hf, hc⟩ := leafExit_frame leaf level st
    exact frame_local hok hl hp (Or.inl hf) hc
  cheap := by
    intro first level numcells st hok
    change Generic.Local G Search.view level numcells st (cheapCheck first level st)
    unfold cheapCheck
    split <;> exact frame_local hok rfl rfl (Or.inl rfl) (Or.inl rfl)
  child := by
    intro first level numcells tc tv cell st hlevel hok htarget htv
    obtain ⟨len, hcell, hmem⟩ := htarget
    obtain ⟨hic, hlen, hrange⟩ := hcell (mem_ne_empty htv)
    obtain ⟨o, ho, heq⟩ := mem_segN_iff.mp (hmem tv htv)
    have hl : (child first level tc tv st).view.lab =
        (breakout n st.view.lab st.view.ptn (level + 1) tc st.view.lab[tc + o]!).1 := by
      rw [← heq]
      cases first <;> rfl
    have hp : (child first level tc tv st).view.ptn = st.view.ptn.set! tc (level + 1) := by
      cases first <;> rfl
    have hf : (child first level tc tv st).view.firstlab = st.view.firstlab := by
      cases first <;> rfl
    have hc : (child first level tc tv st).view.canonlab = st.view.canonlab := by
      cases first <;> rfl
    refine ⟨breakout_searchOk hn0 hok hlevel hic hlen hrange ho hl hp hc, ?_⟩
    intro out hout
    exact breakout_child_out hn0 hok hlevel hic hlen hrange ho hout hl hp hf hc
  afterChild := fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩
  leave := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
  short := by
    intro cell st v hv
    exact Nauty.shortprune_subset (st := st.view) hv
  long := by
    intro cell st v hv
    exact Nauty.longprune_subset hv
  recover := by
    intro level numcells st out hlevel hok hout
    have hbound : level + 1 < n + 2 := by
      have := hok.bc
      have := bcount_le st.view.ptn level n
      omega
    have hr := hout.trans (recover_out hbound hout.reach)
    change Generic.Local G Search.view level numcells st
      (recoverLevels level (recoverPtn (n + 2) level out))
    constructor
    · rw [view_recover]
      apply searchOk_of_out hok hlevel hr
      intro q hq
      rw [recover_ptn]
      split
      · exact Or.inr rfl
      · exact Or.inl (by omega)
    · rw [view_recover]
      exact hr
  afterSweep := by
    intro first level size index st
    change Generic.FrameEq Search.view st (afterSweep first level size index st)
    unfold afterSweep
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every engine node preserves the caller's partition frame. -/
theorem node_out {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) :
    SearchOut G (level - 1) level st.view
      (node first ctx (n + 2) tcLevel fuel level numcells st).2.view := by
  rw [node_eq_generic]
  exact Generic.node_reach (reachPolicy G ctx tcLevel hn0) first fuel level numcells st hlevel hok

/-- Every engine sweep preserves its parent partition frame. -/
theorem sweep_out {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel cfuel level numcells tc tv1 index : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : Search n}
    (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view)
    (htarget : Generic.Target Search.view level tc cell st)
    (hcursor : ∀ v, cursor = some v → cell.mem v = true) :
    SearchOut G level level st.view
      (sweep first ctx (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.view := by
  rw [sweep_eq_generic]
  exact Generic.sweep_reach (reachPolicy G ctx tcLevel hn0) first fuel cfuel level numcells tc tv1
    index cursor cell st hlevel hok htarget hcursor

/-- The engine's nonempty initial state has the coloured root partition. -/
theorem initial_ok (G : Colored n k) (hn0 : 0 < n) :
    SearchOk G 1 (initialPartition G).2.length
      (initial n (initialPartition G).1 (initialPartition G).2).view :=
  root_searchOk G hn0

/-- Running the engine preserves the root partition frame and stores
only labellings reached from its original colour cells. -/
theorem runState_out (G : Colored n k) (hn0 : 0 < n) :
    SearchOut G 0 1
      (initial n (initialPartition G).1 (initialPartition G).2).view
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2.view := by
  unfold runState
  rw [ite_eq_right (show (n == 0) ≠ true by simp; omega)]
  exact node_out true hn0 (Nat.le_refl _) (initial_ok G hn0)

/-- A nonempty run keeps a current labelling in the original colour cells. -/
theorem lab_cellsReach (G : Colored n k) (hn0 : 0 < n) :
    CellsReach G
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2.lab :=
  (runState_out G hn0).reach

/-- The final canonical array is either the untouched initial placeholder
or a full labelling reached from the original colour cells. -/
theorem canonlab_or (G : Colored n k) (hn0 : 0 < n) :
    (runColored G).canonlab = Array.replicate n 0 ∨
      ((runColored G).canonlab.size = n ∧ CellsReach G (runColored G).canonlab) :=
  (runState_out G hn0).canon

/-- The engine cannot exhaust a sufficient node bound on a valid partition. -/
theorem node_noFuel {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) (hfuel : n + 1 ≤ level + fuel) :
    (node first ctx (n + 2) tcLevel fuel level numcells st).1 ≠ .fuel := by
  rw [node_eq_generic]
  exact Generic.node_noFuel (reachPolicy G ctx tcLevel hn0) leafExit_noFuel
    first fuel level numcells st hlevel hok hfuel

/-- The engine cannot exhaust sufficient node and cursor bounds in a sweep. -/
theorem sweep_noFuel {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel cfuel level numcells tc tv1 index : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : Search n}
    (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view)
    (htarget : Generic.Target Search.view level tc cell st)
    (hcursor : ∀ v, cursor = some v → cell.mem v = true)
    (hfuel : n ≤ level + fuel) (hcfuel : Generic.CursorFuel n cfuel cursor) :
    (sweep first ctx (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).1 ≠ .fuel := by
  rw [sweep_eq_generic]
  exact Generic.sweep_noFuel (reachPolicy G ctx tcLevel hn0) leafExit_noFuel
    first fuel cfuel level numcells tc tv1 index cursor cell st hlevel hok htarget hcursor hfuel hcfuel

/-- The root engine run never exhausts its recursion bounds. -/
theorem runState_noFuel (G : Colored n k) :
    (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).1 ≠ .fuel := by
  unfold runState
  split
  · intro h
    cases h
  · rename_i hn
    have hn0 : 0 < n := by
      have hne : n ≠ 0 := by simpa using hn
      omega
    exact node_noFuel true hn0 (Nat.le_refl _) (initial_ok G hn0) (by omega)

end Hex.GraphIso.Nauty.Engine
