/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Node
public import HexGraphIso.Nauty.Policy.Max.Trace
import all HexGraphIso.Nauty.Policy.Max.Node
import all HexGraphIso.Nauty.Policy.Max.Trace
import all HexGraphIso.Nauty.Policy.Max.Init
import all HexGraphIso.Nauty.Policy.Max.Emit
import all HexGraphIso.Nauty.Policy.Max.Carry
import all HexGraphIso.Nauty.Policy.Max.Rules
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A discrete first node installs its prepared leaf without a sweep. -/
theorem Frame.first_step {ctx : Ctx n} {tcLevel : Nat} {f : Frame n}
    (next : Generic.SweepFn (Search n) n)
    (hn : (Generic.prepareFirst ctx tcLevel f.level f.numcells f.entry).1 = n) :
    Generic.nodeStep ctx tcLevel next true f.level f.numcells f.entry =
      (.unwind (f.level - 1) false,
        firstterminal f.level (Generic.prepareFirst ctx tcLevel f.level f.numcells f.entry).2.2.2.2) := by
  unfold Generic.nodeStep
  dsimp only [Generic.prepareFirst] at hn ⊢
  simp only [ite_true, hn, beq_self_eq_true, Id.run_pure]
  rfl

/-- An internal node transports the entire suffix trace through its
ordinary completion or unchanged nonlocal exit. -/
theorem NodeInput.internal_keeps {G : Colored n k} {tcLevel fuel : Nat}
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
    Keeps parents result.1 result.2 := by
  intro ctx result
  let l : Loop n := ⟨f, first⟩
  let p := l.prepare ctx tcLevel
  have hi : SweepInput G ctx tcLevel fuel (n + 1) first f.level p.1 p.2.1.toNat
      ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
      l bs fs parents := by
    cases first
    · exact h.other_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) (hother rfl)
    · exact h.first_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) (hfirst rfl)
  let next : Generic.SweepFn (Search n) n := Generic.sweepCall ctx (n + 2) tcLevel fuel (n + 1)
  let sr := next first f.level p.1 p.2.1.toNat ((p.2.2.1.nextElem none).getD 0)
    (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
  have hr := (hs first f.level p.1 p.2.1.toNat ((p.2.2.1.nextElem none).getD 0)
    (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2 trivial).2 l bs fs parents hi
  change Keeps parents sr.1 sr.2.2 at hr
  have hnc : l.first = true → (l.prepare ctx tcLevel).1 ≠ n := by
    cases first
    · intro he; cases he
    · exact hfirst
  have he := l.node_step next hnc hother
  change result = (match sr.1 with
    | .done => (.unwind (f.level - 1) false, afterSweep first f.level p.2.2.2.1 sr.2.1 sr.2.2)
    | exit => (exit, sr.2.2)) at he
  rw [he]
  cases hx : sr.1 with
  | fuel => simpa only [hx] using hr
  | unwind target short => simpa only [hx] using hr
  | done =>
    intro t q hq hf _ γ hγ
    have ht : (afterSweep first f.level p.2.2.2.1 sr.2.1 sr.2.2).genTrace = sr.2.2.genTrace := by
      unfold afterSweep
      split <;> rfl
    rw [ht] at hγ
    exact hr t q hq hf (by rw [hx]; trivial) γ hγ

/-- Every node preserves accumulated generators at surviving first
ancestors, using the same smaller sweep contract as its key bounds. -/
theorem node_trace (G : Colored n k) (tcLevel : Nat) : NodeTraceRule G tcLevel := by
  intro fuel hs first level numcells st cs bs fs parents h
  let ctx : Ctx n := { g := rowsOf G }
  let f : Frame n := ⟨level, numcells, cs, st⟩
  cases first with
  | true =>
    by_cases hn : (Generic.prepareFirst ctx tcLevel level numcells st).1 = n
    · rw [f.first_step _ hn]
      apply (h.scope.keeps (.unwind (level - 1) false)).congr
      change (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.genTrace = st.genTrace
      exact (prepareFirst_stores ctx tcLevel level numcells st).2.2.2.2
    · exact h.internal_keeps hs (fun _ => hn) (by intro hf; cases hf)
  | false =>
    let p := prepareOther ctx tcLevel level numcells st
    let c := classify ctx level p.1 p.2.2.2.2.2
    by_cases hi : c.1 = .internal
    · exact h.internal_keeps hs (by intro hf; cases hf) (fun _ => hi)
    · have hd : (f.emit ctx tcLevel).1 ≠ .done := by
        intro he
        exact hi ((leafExit_done c.1 level c.2).mp he)
      rw [f.emit_step _ hd]
      exact h.emit_keeps (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)

end Hex.GraphIso.Nauty.Max
