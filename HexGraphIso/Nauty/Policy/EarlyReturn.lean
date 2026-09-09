/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Calls
public import HexGraphIso.Nauty.Policy.Prepared
public import HexGraphIso.Nauty.Policy.ReturnOrigin
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.MaxAncestors
import all HexGraphIso.Nauty.Policy.ReturnOrigin
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- An off-path return retains its emitting classification and state until
an enclosing sweep receives it. Only fixed-point cleanup intervenes. -/
def EarlyReturn (ctx : Ctx n) (target : Nat) (short : Bool) (out : Search n) : Prop :=
  ∃ level numcells before,
    let c := classify ctx level numcells before
    let emitted := leafExit c.1 level c.2
    emitted.1 = .unwind target short ∧
      out = { emitted.2 with fixedpts := out.fixedpts }

/-- Removing an individualized point preserves the unconsumed emission. -/
theorem EarlyReturn.leave {ctx : Ctx n} {target tv : Nat} {short : Bool} {st : Search n}
    (h : EarlyReturn ctx target short st) :
    EarlyReturn ctx target short { st with fixedpts := st.fixedpts.erase tv } := by
  obtain ⟨level, numcells, before, he, hs⟩ := h
  exact ⟨level, numcells, before, he, by rw [hs]⟩

private theorem compare_same (level code : Nat) (st : Search n) :
    (compareCodes level code st).allsamelevel = st.allsamelevel := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.allsamelevel, ite_self]

private theorem classify_same (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.allsamelevel = st.allsamelevel := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.allsamelevel, ite_self]

private theorem leafExit_same (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.allsamelevel = st.allsamelevel := by
  cases leaf <;> unfold leafExit pruneReturn install admit pushAuto
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals rfl

private theorem recover_same (inf level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn inf level st)).allsamelevel = st.allsamelevel := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.allsamelevel, ite_self]

private def earlyContract (ctx : Ctx n) : Generic.Contract (Search n) n where
  nodePre _ first _ _ _ := first = false
  nodePost _ _ level _ st out := out.2.allsamelevel = st.allsamelevel ∧ ∀ target short,
    out.1 = .unwind target short → (target < level - 1 ∨ short = true) → EarlyReturn ctx target short out.2
  sweepPre _ _ first _ _ _ _ _ _ _ _ := first = false
  sweepPost _ _ _ level _ _ _ _ _ _ st out := out.2.2.allsamelevel = st.allsamelevel ∧ ∀ target short,
    out.1 = .unwind target short → (target < level ∨ short = true) → EarlyReturn ctx target short out.2.2

private theorem earlyPolicy (ctx : Ctx n) (inf tcLevel : Nat) :
    Generic.CallPolicy ctx inf tcLevel (earlyContract ctx) where
  node_zero := by intros; simp [earlyContract]
  sweep_none := by intros; simp [earlyContract]
  sweep_zero := by intros; simp [earlyContract]
  node_step := by
    intro fuel hs first level numcells st hf
    cases hf
    let p := prepareOther ctx tcLevel level numcells st
    let c := classify ctx level p.1 p.2.2.2.2.2
    let out := leafExit c.1 level c.2
    have hsame : out.2.allsamelevel = st.allsamelevel := by
      rw [leafExit_same, classify_same]
      dsimp only [p, prepareOther]
      rw [chooseTarget_fields, compare_same]
      rfl
    have he : ∀ target short, out.1 = .unwind target short → EarlyReturn ctx target short out.2 := by
      intro target short hexit
      exact ⟨level, p.1, p.2.2.2.2.2, hexit, rfl⟩
    have hh := hs false level p.1 p.2.2.1.toNat ((p.2.2.2.1.nextElem none).getD 0)
      (p.2.2.2.1.nextElem none) p.2.2.2.1 0 (cheapCheck false level out.2) rfl
    have hhs := hh.1
    have hh := hh.2
    change ∀ target short, _ = Generic.Exit.unwind target short → (target < level ∨ short = true) →
      EarlyReturn ctx target short _ at hh
    let result := match out.1 with
      | .done =>
        let r := Generic.sweepCall ctx inf tcLevel fuel (n + 1) false level p.1 p.2.2.1.toNat
          ((p.2.2.2.1.nextElem none).getD 0) (p.2.2.2.1.nextElem none) p.2.2.2.1 0
          (cheapCheck false level out.2)
        match r.1 with
        | .done => (Generic.Exit.unwind (level - 1) false, afterSweep false level p.2.2.2.2.1 r.2.1 r.2.2)
        | _ => (r.1, r.2.2)
      | _ => out
    change result.2.allsamelevel = st.allsamelevel ∧ ∀ target short,
      result.1 = .unwind target short → (target < level - 1 ∨ short = true) →
      EarlyReturn ctx target short result.2
    constructor
    · have hcheap : (cheapCheck false level out.2).allsamelevel = out.2.allsamelevel := by
        unfold cheapCheck
        split <;> rfl
      have hhs := hhs.trans (hcheap.trans hsame)
      dsimp only [result]
      cases hx : out.1 with
      | fuel => exact hsame
      | unwind => exact hsame
      | done => dsimp only; split <;> exact hhs
    dsimp only [result]
    cases hx : out.1 with
    | fuel => simp only [hx]; intros; contradiction
    | unwind => exact fun target short h _ => he target short h
    | done =>
      dsimp only
      split
      · intro target short heq hlt
        cases heq
        rcases hlt with hlt | hlt
        · omega
        · cases hlt
      · exact fun target short heq hlt => hh target short heq (by rcases hlt with hlt | hlt; exact Or.inl (by omega); exact Or.inr hlt)
  sweep_step := by
    intro fuel cfuel hn hs first level numcells tc tv1 tv cell index st hf
    cases hf
    let raw := Generic.nodeCall ctx inf tcLevel fuel false (level + 1) (numcells + 1)
      (child false level tc tv st)
    have hd := hn false (level + 1) (numcells + 1) (child false level tc tv st) rfl
    have hds := hd.1
    have hd := hd.2
    change ∀ target short, raw.1 = .unwind target short → (target < level + 1 - 1 ∨ short = true) →
      EarlyReturn ctx target short raw.2 at hd
    have hh : ∀ cell, ∀ target short,
        (Generic.sweepCall ctx inf tcLevel fuel cfuel false level numcells tc tv1
          (cell.nextElem (some tv)) cell index
          (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv }))).1 =
            .unwind target short → (target < level ∨ short = true) → EarlyReturn ctx target short
        (Generic.sweepCall ctx inf tcLevel fuel cfuel false level numcells tc tv1
          (cell.nextElem (some tv)) cell index
          (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv }))).2.2 := by
      intro cell
      exact (hs false level numcells tc tv1 (cell.nextElem (some tv)) cell index
        (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv })) rfl).2
    have hhs : ∀ cell, (Generic.sweepCall ctx inf tcLevel fuel cfuel false level numcells tc tv1
        (cell.nextElem (some tv)) cell index
        (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv }))).2.2.allsamelevel = st.allsamelevel := by
      intro cell
      have hr := (hs false level numcells tc tv1 (cell.nextElem (some tv)) cell index
        (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv })) rfl).1
      exact hr.trans ((recover_same inf level _).trans hds)
    change (Generic.sweepStep inf _ _ false level numcells tc tv1 tv cell index st).2.2.allsamelevel = st.allsamelevel ∧
      ∀ target short, (Generic.sweepStep inf _ _ false level numcells tc tv1 tv cell index st).1 =
      .unwind target short → (target < level ∨ short = true) → EarlyReturn ctx target short _
    unfold Generic.sweepStep Generic.advance Generic.resume
    simp only [Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true, Bool.true_and, ↓reduceIte]
    dsimp only [raw] at hd hh hhs
    generalize hraw : Generic.nodeCall ctx inf tcLevel fuel false (level + 1) (numcells + 1)
      (child false level tc tv st) = result at hd hh hhs hds ⊢
    obtain ⟨exit, state⟩ := result
    cases exit with
    | fuel => exact ⟨hds, by simp⟩
    | done =>
      simp only [Id.run_pure]
      split <;> exact ⟨hhs _, hh _⟩
    | unwind target short =>
      simp only [Id.run_pure, apply_ite Id.run]
      split
      · refine ⟨hds, ?_⟩
        intro t s heq hlt
        cases heq
        exact (hd target short rfl (by simpa only [Nat.add_sub_cancel] using hlt)).leave
      · cases short <;> simp only [Bool.false_eq_true, ↓reduceIte]
        all_goals split <;> exact ⟨hhs _, hh _⟩

/-- An off-path node returning past its immediate receiver supplies its
actual leaf origin for either short-flag value. -/
theorem node_early (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n)
    {target : Nat} {short : Bool}
    (he : (node false ctx inf tcLevel fuel level numcells st).1 = .unwind target short)
    (ht : target < level - 1) :
    EarlyReturn ctx target short (node false ctx inf tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic] at he ⊢
  exact (Generic.node_calls (earlyPolicy ctx inf tcLevel) false fuel level numcells st rfl).2
    target short he (Or.inl ht)

/-- Every short off-path return retains its actual leaf origin, even
when its immediate parent receives it. Exhausted sweeps return false. -/
theorem node_short_early (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n)
    {target : Nat}
    (he : (node false ctx inf tcLevel fuel level numcells st).1 = .unwind target true) :
    EarlyReturn ctx target true (node false ctx inf tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic] at he ⊢
  exact (Generic.node_calls (earlyPolicy ctx inf tcLevel) false fuel level numcells st rfl).2
    target true he (Or.inr rfl)

/-- Off-path search preserves the all-same boundary exactly. -/
theorem node_same (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n) :
    (node false ctx inf tcLevel fuel level numcells st).2.allsamelevel = st.allsamelevel := by
  rw [node_eq_generic]
  exact (Generic.node_calls (earlyPolicy ctx inf tcLevel) false fuel level numcells st rfl).1

/-- The two ancestor counters and two pruning boundaries bound every
leaf return from below. The bounds are stated on the emitted state. -/
theorem leafExit_floor (leaf : Leaf) (level : Nat) (st : Search n)
    (bound target : Nat) (short : Bool) :
    let out := leafExit leaf level st
    bound ≤ out.2.gcaFirst → bound ≤ out.2.gcaCanon →
    bound < out.2.noncheaplevel → bound < out.2.allsamelevel →
    out.1 = .unwind target short → bound ≤ target := by
  cases leaf <;> unfold leafExit pruneReturn install admit pushAuto
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals try dsimp only
  all_goals intro hf hc hn ha he
  all_goals cases he
  all_goals try dsimp only at *
  all_goals try simp only [Int.ofNat_eq_natCast] at *
  all_goals omega

/-- Above both pruning boundaries, an unconsumed return cannot cross
either ancestor counter. This applies to short and non-short exits. -/
theorem EarlyReturn.floor {ctx : Ctx n} {target bound : Nat} {short : Bool} {out : Search n}
    (h : EarlyReturn ctx target short out)
    (hf : bound ≤ out.gcaFirst) (hc : bound ≤ out.gcaCanon)
    (hn : bound < out.noncheaplevel) (ha : bound < out.allsamelevel) : bound ≤ target := by
  obtain ⟨level, numcells, before, he, hs⟩ := h
  rw [hs] at hf hc hn ha
  exact leafExit_floor _ level _ bound target short hf hc hn ha he

/-- An actual off-path call cannot cross an ancestor above both pruning
boundaries. All four output bounds follow from the call's entry state. -/
theorem node_floor {ctx : Ctx n} {inf tcLevel fuel level numcells bound target : Nat}
    {st : Search n} {short : Bool} (hb : bound < level)
    (hf : bound ≤ st.gcaFirst) (hc : bound ≤ st.gcaCanon)
    (hn : bound < st.noncheaplevel) (ha : bound < st.allsamelevel)
    (he : (node false ctx inf tcLevel fuel level numcells st).1 = .unwind target short) :
    bound ≤ target := by
  by_cases hlt : bound ≤ target
  · exact hlt
  have hr := node_early ctx inf tcLevel fuel level numcells st he (by omega)
  have hgf : bound ≤ (node false ctx inf tcLevel fuel level numcells st).2.gcaFirst := by
    rwa [node_gca]
  have hgc : bound ≤ (node false ctx inf tcLevel fuel level numcells st).2.gcaCanon := by
    rw [node_eq_generic]
    exact Generic.node_bounded (Max.canonFloor ctx inf tcLevel bound) fuel level numcells st hb hc
  have hsame : bound < (node false ctx inf tcLevel fuel level numcells st).2.allsamelevel := by
    rwa [node_same]
  have hbound := hr.floor hgf hgc (node_noncheap hb hn) hsame
  omega

/-- A valid visit below a first-path receiver returns to that receiver
when it lies above the noncheap and all-same boundaries. -/
theorem NodePre.return_eq {k : Nat} {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel fuel level numcells target : Nat} {short : Bool} {st : Search n}
    (h : NodePre G ctx tcLevel level numcells st)
    (hf : level - 1 ≤ st.gcaFirst) (hc : level - 1 ≤ st.gcaCanon)
    (hn : level - 1 < st.noncheaplevel) (ha : level - 1 < st.allsamelevel)
    (he : (node false ctx inf tcLevel fuel level numcells st).1 = .unwind target short) :
    target = level - 1 := by
  have hl := h.positive
  have hlow := node_floor (by omega : level - 1 < level) hf hc hn ha he
  have hhigh := h.node_bound inf target short he
  omega

end Hex.GraphIso.Nauty
