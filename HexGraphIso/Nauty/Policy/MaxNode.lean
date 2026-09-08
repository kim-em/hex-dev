/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxInit
public import HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxBound
import all HexGraphIso.Nauty.Policy.MaxChoice
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxUnwind
import all HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.ExitBound
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- Finishing a sweep changes only traversal bookkeeping. -/
theorem afterSweep_best (ctx : Ctx n) (first : Bool) (level size index : Nat) (st : Search n) :
    (afterSweep first level size index st).best ctx = st.best ctx := by
  unfold afterSweep
  split <;> rfl

/-- An internal node enters exactly the sweep described by its frozen frame. -/
theorem Loop.node_step {ctx : Ctx n} {tcLevel : Nat} {l : Loop n}
    (next : Generic.SweepFn (Search n) n)
    (hfirst : l.first = true → (l.prepare ctx tcLevel).1 ≠ n)
    (hother : l.first = false →
      let p := prepareOther ctx tcLevel l.node.level l.node.numcells l.node.entry
      (classify ctx l.node.level p.1 p.2.2.2.2.2).1 = .internal) :
    Generic.nodeStep ctx tcLevel next l.first l.node.level l.node.numcells l.node.entry =
      let p := l.prepare ctx tcLevel
      let result := next l.first l.node.level p.1 p.2.1.toNat
        ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
      match result.1 with
      | .done => (.unwind (l.node.level - 1) false,
          afterSweep l.first l.node.level p.2.2.2.1 result.2.1 result.2.2)
      | exit => (exit, result.2.2) := by
  have hi : l.first = false →
      let p := prepareOther ctx tcLevel l.node.level l.node.numcells l.node.entry
      classify ctx l.node.level p.1 p.2.2.2.2.2 = (.internal, p.2.2.2.2.2) :=
    fun hf => classify_internal_state (hother hf)
  unfold Generic.nodeStep
  unfold Loop.prepare at hfirst ⊢
  unfold prepareOther at hi
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.firstterminal,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck,
    Generic.Policy.afterSweep] at hfirst hi ⊢
  generalize hv : visit ctx l.node.level l.node.numcells l.node.entry = v at hfirst hi ⊢
  obtain ⟨nc, code, st⟩ := v
  cases hf : l.first
  · simp only [Bool.false_eq_true, ↓reduceIte] at hfirst hi ⊢
    generalize ht : chooseTarget false ctx tcLevel l.node.level nc (compareCodes l.node.level code st) = t at hi ⊢
    obtain ⟨tc, cell, len, out⟩ := t
    dsimp only at hi ⊢
    rw [hi hf]
    simp only [leafExit, show (Generic.Leaf.internal != Generic.Leaf.internal) = false from rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Id.run_pure]
    generalize hr : next false l.node.level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck false l.node.level out) = r
    obtain ⟨exit, index, result⟩ := r
    cases exit <;> rfl
  · simp only [↓reduceIte] at hfirst hi ⊢
    have hn := hfirst hf
    generalize ht : chooseTarget true ctx tcLevel l.node.level nc (recordFirst l.node.level code st) = t
    obtain ⟨tc, cell, len, out⟩ := t
    simp only [beq_eq_false_iff_ne.mpr hn, Bool.false_eq_true, ↓reduceIte]
    generalize hr : next true l.node.level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck true l.node.level out) = r
    obtain ⟨exit, index, result⟩ := r
    cases exit <;> rfl

/-- The initialized actual sweep supplies both bounds and the exact
ancestor witness needed by its enclosing node. -/
theorem NodeInput.internal_result {G : Colored n k} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G { g := rowsOf G } tcLevel (fuel + 1) first f bs fs parents)
    (hs : (contract G tcLevel).sweepValid fuel (n + 1)
      (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel (n + 1)))
    (hfirst : first = true → (Generic.prepareFirst { g := rowsOf G } tcLevel
      f.level f.numcells f.entry).1 ≠ n)
    (hother : first = false →
      let p := prepareOther { g := rowsOf G } tcLevel f.level f.numcells f.entry
      (classify { g := rowsOf G } f.level p.1 p.2.2.2.2.2).1 = .internal) :
    let ctx : Ctx n := { g := rowsOf G }
    let result := Generic.nodeStep ctx tcLevel
      (Generic.sweepCall ctx (n + 2) tcLevel fuel (n + 1)) first f.level f.numcells f.entry
    Generic.Result (f.key ctx tcLevel) (f.entry.key ctx bs) (result.2.best ctx) (f.level - 1)
      (Witness ctx tcLevel (parents.frames ctx tcLevel)) result.1 := by
  intro ctx result
  let l : Loop n := ⟨f, first⟩
  let p := l.prepare ctx tcLevel
  have hi : SweepInput G ctx tcLevel fuel (n + 1) first f.level p.1 p.2.1.toNat
      ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
      l bs fs parents := by
    cases first
    · exact h.other_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) (hother rfl)
    · exact h.first_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) (hfirst rfl)
  have hnc : p.1 < n := by
    have hh : p.1 = bcount p.2.2.2.2.ptn f.level n := hi.base.count
    have hb := bcount_le p.2.2.2.2.ptn f.level n
    have he : p.1 ≠ n := by
      cases first
      · exact ((classify_internal ..).mp (hother rfl)).2
      · exact hfirst rfl
    omega
  let next : Generic.SweepFn (Search n) n := Generic.sweepCall ctx (n + 2) tcLevel fuel (n + 1)
  let sr := next first f.level p.1 p.2.1.toNat ((p.2.2.1.nextElem none).getD 0)
    (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
  have hr := (hs first f.level p.1 p.2.1.toNat ((p.2.2.1.nextElem none).getD 0)
    (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2 trivial).1 l bs fs parents hi
  change Generic.Result (l.bound ctx tcLevel) (p.2.2.2.2.key ctx bs) (sr.2.2.best ctx) f.level
    (Witness ctx tcLevel ((parents.frames ctx tcLevel).insert f)) sr.1 at hr
  have hb := l.node_bound h.frame h.entry hi.window hi.len hi.range hnc hr.bounded
  have hstep := l.node_step next (fun _ => Nat.ne_of_lt hnc) hother
  change result = (match sr.1 with
    | .done => (.unwind (f.level - 1) false, afterSweep first f.level p.2.2.2.1 sr.2.1 sr.2.2)
    | exit => (exit, sr.2.2)) at hstep
  have hbound := Generic.sweep_bound first ctx (n + 2) tcLevel fuel (n + 1) f.level p.1 p.2.1.toNat
    ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
  change ∀ target short, sr.1 = .unwind target short → target < f.level at hbound
  rw [hstep]
  cases he : sr.1 with
  | fuel => exact ⟨hb, trivial⟩
  | done =>
    dsimp only
    rw [afterSweep_best]
    refine ⟨hb, Nat.le_refl _, ?_⟩
    simp only [↓reduceIte]
    rcases hi.choice with ht | hd
    · rw [l.bound_eq h.frame hi.window hi.len hi.range ht]
      simpa only [he, Generic.ExitCover] using hr.coverage
    · exact hd.grow hr.bounded.grows
  | unwind target short =>
    have ht := hbound target short he
    have hw : Witness ctx tcLevel ((parents.frames ctx tcLevel).insert f) target (sr.2.2.best ctx) := by
      have hc := hr.coverage
      rw [he] at hc
      simpa only [Generic.ExitCover, ite_eq_right (by omega : target ≠ f.level)] using hc.2
    refine ⟨hb, by omega, ?_⟩
    split
    · rename_i hp
      subst target
      exact Witness.resolve hw
    · rename_i hp
      exact (Witness.below (by omega : target < f.level - 1)).mp hw

/-- The first internal branch satisfies its complete local maximum rule. -/
theorem first_branch (G : Colored n k) (tcLevel : Nat) :
    NodeRule G tcLevel true (fun level numcells st =>
      (Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).1 ≠ n) := by
  intro fuel hs level numcells st hn cs bs fs parents hi
  exact hi.internal_result hs (fun _ => hn) (by intro hf; cases hf)

/-- The off-path internal branch permits hinted dominated descent and
positive comparison overwrites under the same maximum contract. -/
theorem other_branch (G : Colored n k) (tcLevel : Nat) :
    NodeRule G tcLevel false (fun level numcells st => verdict G tcLevel level numcells st = .internal) := by
  intro fuel hs level numcells st hn cs bs fs parents hi
  exact hi.internal_result hs (by intro hf; cases hf) (fun _ => hn)

end Hex.GraphIso.Nauty.Engine.Max
