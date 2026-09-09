/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Visit
public import HexGraphIso.Nauty.Policy.Max.Carry
public import HexGraphIso.Nauty.Policy.Max.Rules
import all HexGraphIso.Nauty.Policy.Max.Visit
import all HexGraphIso.Nauty.Policy.Max.Carry
import all HexGraphIso.Nauty.Policy.Max.Unwind
import all HexGraphIso.Nauty.Policy.Max.Entry
import all HexGraphIso.Nauty.Policy.Max.Suspend
import all HexGraphIso.Nauty.Policy.Max.Rules
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Prepare
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Invariant.PathStab
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Cleanup and recovery retain every generator returned by the child. -/
theorem received_trace (first : Bool) (inf level tv1 tv : Nat) (out : Search n) :
    let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    (Nauty.recover inf level left).genTrace = out.genTrace := by
  intro middle left
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.genTrace, ite_self]
  dsimp only [left, middle]
  split <;> rfl

/-- The actual child input supplies preservation of its complete output
trace from the same smaller contract that supplies its key bounds. -/
theorem SweepInput.child_keeps {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel)) :
    let ctx : Ctx n := { g := rowsOf G }
    let p : Parent n := ⟨l, st, tv, bs, fs⟩
    let result := Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st)
    Keeps (parents.push p) result.1 result.2 := by
  intro ctx p result
  have hp := h.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  change NodeInput G ctx tcLevel fuel (first && tv == tv1)
    (p.child ctx tcLevel) bs fs (parents.push p) at hp
  have he : p.child ctx tcLevel =
      ⟨level + 1, numcells + 1, l.codes ctx, Nauty.child first level tc tv st⟩ := by
    simp only [p, ctx, Parent.child, h.first_eq, h.level_eq, h.numcells_eq, h.tc_eq]
  rw [he] at hp
  have hr := (hn (first && tv == tv1) (level + 1) (numcells + 1)
    (Nauty.child first level tc tv st) trivial).2 (l.codes ctx) bs fs (parents.push p) hp
  simpa only [result, Generic.nodeCall, ← node_eq_generic] using hr

/-- A received child's accumulated generators supply both the current
frozen first-loop carriers and every older saved first-frame carrier. -/
theorem SweepInput.received_generators {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first short : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (hcall : Nauty.node (first && tv == tv1) { g := rowsOf G } (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = (.unwind level short, out)) :
    let ctx : Ctx n := { g := rowsOf G }
    let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := Nauty.recover (n + 2) level left
    (first = true → ∀ γ ∈ ready.genTrace,
      CellStab (l.prepare ctx tcLevel).2.2.2.2.ptn level
        (l.prepare ctx tcLevel).2.2.2.2.lab γ) ∧
    (∀ t p, parents t = some p → p.loop.first = true →
      ∀ γ ∈ ready.genTrace, CellStab p.state.ptn t p.state.lab γ) := by
  intro ctx middle left ready
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  have hr := h.child_keeps hn
  dsimp only at hr
  rw [hcall] at hr
  have ht : ready.genTrace = out.genTrace := received_trace first (n + 2) level tv1 tv out
  constructor
  · intro hf γ hγ
    rw [ht] at hγ
    have hp : (parents.push p) level = some p := by simp only [Parents.push, p, ← h.level_eq, ↓reduceIte]
    have hh : CellStab st.ptn level st.lab γ :=
      hr level p hp (h.first_eq.symm.trans hf) (Nat.le_refl _) γ hγ
    have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
    have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
    have he := h.effect.ptn_eq h.base h.partition
    change st.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn at he
    rw [he] at hh
    exact LocalAutos.reindexStab hh (cellsPerm_symm h.effect.perm)
      h.base.ptnSize h.partition.labSize h.base.labSize (searchOk_end hn0 h.base hl)
  · intro t q hq hf γ hγ
    rw [ht] at hγ
    have htl := (h.scope.valid t q hq).2.1
    have hp : (parents.push p) t = some q := by
      simpa only [Parents.push, p, ← h.level_eq, show t ≠ level by omega, ↓reduceIte] using hq
    exact hr t q hp hf (by omega) γ hγ

/-- The full visiting maximum rule has no assumed return-local generator
premises: both are obtained from the actual smaller child contract. -/
theorem visit (G : Colored n k) (tcLevel : Nat) : SweepRule G tcLevel true := by
  intro fuel cfuel hn hs first level numcells tc tv1 tv cell index st hv l bs fs parents h
  exact h.visit hn hs hv (fun _ _ hc => h.received_generators hn hc)

end Hex.GraphIso.Nauty.Max
