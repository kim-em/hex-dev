/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxEmit
public import HexGraphIso.Nauty.Policy.MaxPrefix
import all HexGraphIso.Nauty.Policy.MaxCheap
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.Comparison
import all HexGraphIso.Nauty.Policy.CodeCalls
import all HexGraphIso.Nauty.Policy.Canonical
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Prune
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Rejection cannot arise from a positive incoming code comparison. -/
theorem bad_nonpos {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (h : (classify ctx level numcells st).1 = .bad) : st.compCanon ≤ 0 := by
  by_cases hc : st.compCanon ≤ 0
  · exact hc
  have hp : 0 < st.compCanon := by omega
  unfold classify at h
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, scatter_eq,
    show ¬st.compCanon < 0 by omega, decide_false, Bool.and_false, Bool.false_eq_true,
    beq_eq_false_iff_ne.mpr (show st.compCanon ≠ 0 by omega), hp, ite_true] at h
  repeat' split at h
  all_goals cases h <;> contradiction

/-- Row classification retains the frozen equal-code level. -/
theorem classify_eqlevCanon (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.eqlevCanon = st.eqlevCanon := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.eqlevCanon, ite_self]

/-- A rejected leaf retains the sharp choice between the code comparison
and the cheap boundary in its actual return target. -/
theorem bad_target {level target : Nat} {short : Bool} {st : Search n}
    (he : (leafExit .bad level st).1 = .unwind target short) :
    st.eqlevCanon.toNat ≤ target ∨ target = st.noncheaplevel - 1 := by
  unfold leafExit at he
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
  split at he
  all_goals
    obtain ⟨t, s, hx, hbound⟩ := pruneReturn_target level { st with
      maxlevel := _, numbadleaves := st.numbadleaves + 1 }
    rw [he] at hx
    cases hx
    exact hbound

/-- An actual rejected node covers its own full subtree and retains the
fragment upper bound, whether rejection happens before or at a leaf. -/
theorem NodeInput.bad_bound {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hbad : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .bad)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Generic.Bounded (f.key ctx tcLevel) (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx) ∧
      Generic.Covers (f.key ctx tcLevel) ((f.emit ctx tcLevel).2.best ctx) := by
  let p := prepareOther ctx tcLevel f.level f.numcells f.entry
  by_cases hd : p.1 = n
  · have hb := h.leaf_best hd hgsz hsymm hloop
    change (f.emit ctx tcLevel).2.best ctx = some (incMax (f.entry.key ctx bs) (f.key ctx tcLevel)) at hb
    refine ⟨Generic.Bounded.of_eq hb, ?_⟩
    rw [hb]
    exact Generic.Covers.incMax _ _
  · have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
    have hlen := h.frame.length
    have hdepth := h.frame.depth
    obtain ⟨hin, hc⟩ := h.entry
    have hm := hc.prepare (tcLevel := tcLevel) (numcells := f.numcells) (by omega)
    simp only [hlen] at hm
    have hcomparison : Comparison ctx (f.codes ++ [p.2.1]) bs fs p.2.2.2.2.2 := hm.1
    have hlength : (f.codes ++ [p.2.1]).length = f.level := by
      simp only [List.length_append, List.length_singleton, hlen]
    have hclass : (classify ctx (f.codes ++ [p.2.1]).length p.1 p.2.2.2.2.2).1 = .bad := by
      rw [hlength]; exact hbad
    have hr := hcomparison.prune hd hclass
    rw [hlength] at hr
    have hread : (f.emit ctx tcLevel).2.best ctx = p.2.2.2.2.2.key ctx bs :=
      hr.1.read.trans hr.2.2.1
    have hb := hread.trans hm.2
    have hneg := (classify_pruned hd (show (classify ctx f.level p.1 p.2.2.2.2.2).1 = .bad from hbad)).1
    have hle := hcomparison.canonical.subtree_le (ctx := ctx) hneg tcLevel (n - f.level)
    rw [hb]
    refine ⟨Generic.Bounded.refl _ _, ?_⟩
    rw [← hm.2]
    refine ⟨incKey ctx bs p.2.2.2.2.2.canonlab, ?_, ?_⟩
    · simp only [Search.key, hc.nonempty, ↓reduceIte]
      rfl
    · rw [Frame.key, show n + 1 - f.level = n - f.level + 1 by omega]
      exact hle

/-- Both row rejection and nonterminal code rejection satisfy the complete
emitting rule, with code-supported and cheap returns kept distinct. -/
theorem NodeInput.bad_result {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {target : Nat} {short : Bool}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hbad : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .bad)
    (hexit : (f.emit ctx tcLevel).1 = .unwind target short)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Generic.Result (f.key ctx tcLevel) (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx)
      (f.level - 1) (Witness ctx tcLevel (parents.frames ctx tcLevel)) (f.emit ctx tcLevel).1 := by
  obtain ⟨hb, hc⟩ := h.bad_bound hbad hgsz hsymm hloop
  obtain ⟨hin, hcomp⟩ := h.entry
  have ht := hin.leaf_bound hexit
  refine ⟨hb, ?_⟩
  rw [hexit]
  refine ⟨by omega, ?_⟩
  split
  · exact hc
  · rename_i hneq
    have hbelow : target < f.level - 1 := by omega
    let p := prepareOther ctx tcLevel f.level f.numcells f.entry
    let c := classify ctx f.level p.1 p.2.2.2.2.2
    have he : (leafExit .bad f.level c.2).1 = .unwind target short := by
      change (leafExit c.1 f.level c.2).1 = .unwind target short at hexit
      rwa [hbad] at hexit
    rcases bad_target he with hcode | hcheap
    · have heq := classify_eqlevCanon ctx f.level p.1 p.2.2.2.2.2
      change c.2.eqlevCanon = p.2.2.2.2.2.eqlevCanon at heq
      rw [heq] at hcode
      have hlen := h.frame.length
      have hdepth := h.frame.depth
      have hm := hcomp.prepare (tcLevel := tcLevel) (numcells := f.numcells) (by omega)
      simp only [hlen] at hm
      have hcomparison : Comparison ctx (f.codes ++ [p.2.1]) bs fs p.2.2.2.2.2 := hm.1
      have hlength : (f.codes ++ [p.2.1]).length = f.level := by
        simp only [List.length_append, List.length_singleton, hlen]
      have hn : p.2.2.2.2.2.compCanon ≤ 0 := bad_nonpos hbad
      have hneg : p.2.2.2.2.2.compCanon < 0 := by
        rcases hcomparison.canonical.tri with ⟨_, he, _⟩ | ⟨j, _, _, _, _, _, hd⟩
        · rw [hlength] at he
          rw [he] at hcode
          change f.level ≤ target at hcode
          omega
        · rcases hd with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
      apply h.code_witness hbelow
      intro tail
      have hp := hcomparison.canonical.ancestor_le (ctx := ctx) hneg
        (level := target + 1) (by omega) (by rw [hlength]; omega) tail
      rw [List.take_append, show target + 1 - f.codes.length = 0 by omega,
        List.take_zero, List.append_nil] at hp
      have hcover : Generic.Covers (prefixKey (f.codes.take (target + 1)) tail)
          (p.2.2.2.2.2.key ctx bs) := by
        exact ⟨incKey ctx bs p.2.2.2.2.2.canonlab,
          by simp only [Search.key, hcomp.nonempty, ↓reduceIte], hp⟩
      have hbefore : p.2.2.2.2.2.key ctx bs = f.entry.key ctx bs := hm.2
      rw [hbefore] at hcover
      exact hcover.grow hb.grows
    · have hn := f.emit_noncheap ctx tcLevel
      have hs := leafExit_noncheap c.1 f.level c.2
      change (f.emit ctx tcLevel).2.noncheaplevel = c.2.noncheaplevel at hs
      exact h.cheap_witness hbelow (by omega) hc hb.grows hgsz hsymm hloop

/-- The rejection rule discharges the whole node obligation, including
row rejection, frozen code pruning, and arbitrary-depth cheap returns. -/
theorem bad_rule (G : Colored n k) (tcLevel : Nat) :
    NodeRule G tcLevel false (fun level numcells st => verdict G tcLevel level numcells st = .bad) := by
  intro fuel _ level numcells st hbad cs bs fs parents h
  let ctx : Ctx n := { g := rowsOf G }
  let f : Frame n := ⟨level, numcells, cs, st⟩
  let p := prepareOther ctx tcLevel level numcells st
  let c := classify ctx level p.1 p.2.2.2.2.2
  have hclass : c.1 = .bad := hbad
  have hdone : (f.emit ctx tcLevel).1 ≠ .done := by
    intro he
    have hi := (leafExit_done c.1 level c.2).mp he
    rw [hclass] at hi
    cases hi
  have hnf := leafExit_noFuel c.1 level c.2
  obtain ⟨target, short, hexit⟩ : ∃ target short, (f.emit ctx tcLevel).1 = .unwind target short := by
    cases he : (f.emit ctx tcLevel).1 with
    | done => exact (hdone he).elim
    | fuel => exact (hnf he).elim
    | unwind target short => exact ⟨target, short, rfl⟩
  have hr := h.bad_result hclass hexit (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  rw [f.emit_step _ hdone]
  exact hr

end Hex.GraphIso.Nauty.Max
