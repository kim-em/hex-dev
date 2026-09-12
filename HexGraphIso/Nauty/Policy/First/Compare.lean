/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.CodeCalls
public import HexGraphIso.Nauty.Policy.First.Run
import all HexGraphIso.Nauty.Policy.CodeCalls
import all HexGraphIso.Nauty.Policy.First.Run
import all HexGraphIso.Nauty.Policy.First.History
import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.ReturnCodes
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Writing the next refinement code extends its stored prefix. -/
theorem StoredCodes.push {store : Array Nat} {base : Nat} {cs : List Nat}
    (h : StoredCodes store base cs) (hsize : base + cs.length < store.size) (code : Nat) :
    StoredCodes (store.set! (base + cs.length) code) base (cs ++ [code]) := by
  intro i hi
  by_cases heq : i = cs.length
  · subst i
    rw [Array.getElem!_set!_self _ _ _ hsize]
    simp
  · have hilt : i < cs.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega), getElem!_append_left hilt]
    exact h i hilt

/-- First-path preparation leaves canonical code storage allocated. -/
theorem prepareFirst_canoncode (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.canoncode = st.canoncode := by
  unfold Generic.prepareFirst
  change (chooseTarget true ctx tcLevel level _ _).2.2.2.canoncode = _
  rw [chooseFirst_fields]
  rfl

/-- The prepared first node has stored its incoming prefix followed by
its own actual refinement code. -/
theorem FirstPre.code_prefix {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (h : FirstPre G ctx level numcells st) {cs : List Nat}
    (hlen : cs.length + 1 = level) (hcs : StoredCodes st.firstcode 1 cs) :
    StoredCodes (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.firstcode 1
      (cs ++ [(st.refined ctx level numcells).longcode]) := by
  rw [prepareFirst_code, ← hlen, Nat.add_comm cs.length 1]
  apply hcs.push
  have hbc := h.partition.bc
  have hb := bcount_le st.ptn level n
  rw [h.codes]
  omega

/-- The first child's settled code machines survive all later siblings,
whose incumbents can only improve the value installed by that child. -/
theorem firstSweep_codes {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (level numcells tc tv index : Nat) (cell : VSet n) (st : Search n)
    (horbit : st.orbits[tv]! = tv) (hfuel : n ≤ level + fuel) (hcursor : n ≤ tv + (cfuel + 1))
    (cs bs fs : List Nat) (hlen : cs.length = level)
    (hchild : ReturnCodes ctx cs bs fs (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child true level tc tv st)).2)
    (hready : let out := (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
        (child true level tc tv st)).2
      let left := { afterChildFirst level tv out with fixedpts := out.fixedpts.erase tv }
      SweepPre G ctx tcLevel true level numcells tc tv none cell
        (Nauty.recover (n + 2) level left)) :
    let before := (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child true level tc tv st)).2
    let result := sweep true ctx (n + 2) tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st
    ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows (before.key ctx bs) (result.2.2.key ctx bs') := by
  dsimp only at hready ⊢
  rw [sweep]
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, Bool.false_and, ite_true]
  generalize hcall : node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
    (child true level tc tv st) = result at hchild hready ⊢
  obtain ⟨exit, out⟩ := result
  let left := { afterChildFirst level tv out with fixedpts := out.fixedpts.erase tv }
  let ready := Nauty.recover (n + 2) level left
  have hleft : ReturnCodes ctx cs bs fs left := hchild.fields rfl rfl rfl
  have hcomp : Comparison ctx cs bs fs ready := by
    simpa only [hlen] using hleft.recover (n + 2)
  have hnonpos : ready.compCanon ≤ 0 := recover_nonpos hleft.nonpos (n + 2) level
  have hkey : ready.key ctx bs = out.key ctx bs := recover_key ctx bs (n + 2) level left
  have hcontinue : ∀ smaller index, (∀ v, smaller.mem v = true → cell.mem v = true) →
      let result := sweep true ctx (n + 2) tcLevel fuel cfuel level numcells tc tv
        (smaller.nextElem (some tv)) smaller index ready
      ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows (out.key ctx bs) (result.2.2.key ctx bs') := by
    intro smaller index hsub
    have hp : SweepPre G ctx tcLevel true level numcells tc tv (smaller.nextElem (some tv)) smaller ready := by
      refine ⟨?_, hready.positive, hready.partition, hready.target.subset hsub,
        (fun _ hv => VSet.nextElem_mem hv), hready.stored, hready.ancestor, hready.canonAncestor, hready.history,
        hready.recorded, hready.equitable, hready.boundary, hready.cheapBound, hready.path, hready.small⟩
      intro _ v hv
      have hn := (VSet.nextElem_eq_some_iff.mp hv).2.1
      change tv + 1 ≤ v at hn
      omega
    obtain ⟨bs', hr, hg⟩ := sweep_codes (index := index) hn0 hgsz hsymm hloop hp hfuel
      (Generic.CursorFuel.next hcursor) hlen hcomp (Or.inl hnonpos)
    exact ⟨bs', hr, hkey ▸ hg⟩
  cases exit with
  | fuel => exact ⟨bs, hleft, Generic.Grows.refl _⟩
  | done => exact hcontinue cell _ (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact ⟨bs, hleft, Generic.Grows.refl _⟩
    · cases short with
      | false => exact hcontinue cell _ (fun _ hv => hv)
      | true =>
        exact hcontinue (shortprune cell left) _
          (fun _ hv => Nauty.shortprune_subset (st := left) hv)

/-- The actual first descent initializes the code machines; each ancestor
then uses the same off-path comparison theorem for its remaining siblings. -/
theorem firstPath_codes {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n} (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hin : FirstPre G ctx level numcells st) (hcanon : st.canoncode.size = n + 2)
    (hfuel : n + 1 ≤ level + fuel) {cs : List Nat} (hlen : cs.length + 1 = level)
    (hstore : StoredCodes st.firstcode 1 cs) (hlt : ∀ c ∈ cs, c < codeSentinel) :
    ∃ fs bs, cs <+: fs ∧ fs.length = last ∧
      ReturnCodes ctx cs bs fs (node true ctx (n + 2) tcLevel fuel level numcells st).2 := by
  induction hpath generalizing cs with
  | leaf fuel level numcells st hdisc =>
    let codes := cs ++ [(st.refined ctx level numcells).longcode]
    have hlength : codes.length = level := by simp only [codes, List.length_append, List.length_singleton]; omega
    have hbound : codes.length ≤ n := by
      have := hin.partition.bc
      have := bcount_le st.ptn level n
      omega
    have hnonempty : codes ≠ [] := by simp [codes]
    have hstored := hin.code_prefix (tcLevel := tcLevel) hlen hstore
    have hvalues : ∀ i, 1 ≤ i → i ≤ codes.length →
        (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.firstcode[i]! = codes[i - 1]! := by
      intro i hi hb
      have hs := hstored (i - 1) (by change i - 1 < codes.length; omega)
      simpa only [show 1 + (i - 1) = i by omega] using hs
    have hcsize : (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.canoncode.size = n + 2 := by
      rw [prepareFirst_canoncode, hcanon]
    have hfsize := (prepareFirst_stores ctx tcLevel level numcells st).1.trans hin.codes
    have hcodeslt : ∀ c ∈ codes, c < codeSentinel := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hlt c hc
      · have he := List.mem_singleton.mp hc
        subst c
        exact refine_longcode_lt ctx level st.lab st.ptn st.active numcells
    have hm := comparison_firstterminal (ctx := ctx) hnonempty hcsize hfsize hbound hvalues hcodeslt
    have hr := hm.returned (by change (0 : Int) ≤ 0; omega)
    refine ⟨codes, codes, ⟨[_], rfl⟩, hlength, ?_⟩
    rw [node_first]
    simp only [hdisc, beq_self_eq_true, ite_true, Id.run_pure]
    simpa only [hlength] using hr.prefix (show cs <+: codes from ⟨[_], rfl⟩)
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let ready := cheapCheck true level r.2.2.2.2
    let ch := child true level r.2.1.toNat tv ready
    let codes := cs ++ [(st.refined ctx level numcells).longcode]
    have hlength : codes.length = level := by simp only [codes, List.length_append, List.length_singleton]; omega
    have hentry := hin.child hn0 hsymm htv hgsz hloop
    have hcanonChild : ch.canoncode.size = n + 2 := by
      change ready.canoncode.size = n + 2
      unfold ready cheapCheck
      split <;> change r.2.2.2.2.canoncode.size = n + 2
      all_goals rw [prepareFirst_canoncode, hcanon]
    have hstored : StoredCodes ch.firstcode 1 codes := by
      change StoredCodes ready.firstcode 1 codes
      unfold ready cheapCheck
      split <;> exact hin.code_prefix hlen hstore
    have hcodeslt : ∀ c ∈ codes, c < codeSentinel := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hlt c hc
      · have he := List.mem_singleton.mp hc
        subst c
        exact refine_longcode_lt ctx level st.lab st.ptn st.active numcells
    obtain ⟨fs, bs, hpref, hlast, hchild⟩ := ih hentry hcanonChild (by omega)
      (show codes.length + 1 = level + 1 by omega) hstored hcodeslt
    have hsafe := firstPath_safe hn0 hgsz hsymm hloop tail hentry
    have hready := firstChild_ready hin hn0 hsymm hopen htv horbit tail hsafe hgsz hloop
    have hs := firstSweep_codes (cfuel := n) hn0 hgsz hsymm hloop level r.1 r.2.1.toNat tv 0
      r.2.2.1 ready horbit (by omega) (by omega) codes bs fs hlength hchild hready
    refine ⟨fs, ?_⟩
    rw [node_first]
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ite_false, htv, Option.getD_some]
    generalize hsval : sweep true ctx (n + 2) tcLevel fuel (n + 1) level r.1 r.2.1.toNat
      tv (some tv) r.2.2.1 0 ready = result at hs ⊢
    obtain ⟨exit, index, out⟩ := result
    obtain ⟨bs', hr, _⟩ := hs
    have hp : cs <+: codes := ⟨[_], rfl⟩
    cases exit with
    | fuel => exact ⟨bs', hp.trans hpref, hlast, hr.prefix hp⟩
    | unwind => exact ⟨bs', hp.trans hpref, hlast, hr.prefix hp⟩
    | done => exact ⟨bs', hp.trans hpref, hlast, (hr.afterSweep true level r.2.2.2.1 index).prefix hp⟩

/-- Every nonempty coloured search run returns settled code comparisons,
with the first reference and incumbent supplied by its actual descent. -/
theorem runState_codes (G : Colored n k) (hn0 : 0 < n) :
    ∃ fs bs, ReturnCodes { g := rowsOf G } [] bs fs
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2 := by
  obtain ⟨last, leaf, hpath⟩ := initial_path G hn0
  have hp := initial_firstPre G hn0
  obtain ⟨fs, bs, _, _, hr⟩ := firstPath_codes hn0 (size_rowsOf G) (rowsOf_symm G)
    (rowsOf_loopless G) hpath hp (by change (Array.replicate (n + 2) 0).size = n + 2; simp)
    (by omega) (cs := []) rfl (by intro i hi; cases hi) (by simp)
  refine ⟨fs, bs, ?_⟩
  rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn0)]
  exact hr

/-- The completed nonempty run exposes a readable installed incumbent. -/
theorem runState_incumbent (G : Colored n k) (hn0 : 0 < n) :
    ∃ key, (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2.best
      { g := rowsOf G } = some key := by
  obtain ⟨fs, bs, hr⟩ := runState_codes G hn0
  rw [hr.read]
  simp only [SearchState.key, hr.nonempty, ite_false]
  exact ⟨_, rfl⟩

end Hex.GraphIso.Nauty
