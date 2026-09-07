/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Reference
import all HexGraphIso.Nauty.Policy.Reference
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.VSet.Basic

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ α : Type} [Policy σ n]

/-- Refine the first path, save its code, and select its target. -/
def prepareFirst (ctx : Ctx n) (tcLevel level numcells : Nat) (st : σ) :
    Nat × Int × VSet n × Nat × σ :=
  let r := Policy.visit ctx level numcells st
  (r.1, Policy.chooseTarget true ctx tcLevel level r.1
    (Policy.recordFirst (n := n) level r.2.1 r.2.2))

/-- The first child determines the saved reference of an entire first-path
sweep, even when that child returns past the receiving frame. -/
theorem sweep_first_reference {ctx : Ctx n} {inf tcLevel : Nat} {project : σ → α}
    (h : ReferencePolicy ctx inf tcLevel project)
    (hfirst : ∀ level tv st,
      project (Policy.afterChildFirst (n := n) level tv st) = project st)
    (fuel cfuel level numcells tc tv index : Nat) (cell : VSet n) (st : σ)
    (horbit : Policy.orbit (n := n) st tv = tv) :
    project (sweep true ctx inf tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st).2.2 =
    project (node true ctx inf tcLevel fuel (level + 1) (numcells + 1)
      (Policy.child (n := n) true level tc tv st)).2 := by
  have hpast : ∀ cell : VSet n, Past true tv (cell.nextElem (some tv)) := by
    intro cell _ v hv
    have hnext := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hnext
    omega
  have hcontinue : ∀ cell index out,
      project (sweep true ctx inf tcLevel fuel cfuel level numcells tc tv
        (cell.nextElem (some tv)) cell index
        (Policy.recover (n := n) inf level out)).2.2 = project out := by
    intro cell index out
    exact (sweep_reference h true fuel cfuel level numcells tc tv index _ cell _
      (hpast cell)).trans (h.recover level out)
  rw [sweep]
  unfold sweepStep
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, Bool.false_and, ite_true]
  generalize hr : node true ctx inf tcLevel fuel (level + 1) (numcells + 1)
    (Policy.child (n := n) true level tc tv st) = result
  obtain ⟨exit, out⟩ := result
  have heq := (h.leave tv (Policy.afterChildFirst (n := n) level tv out)).trans
    (hfirst level tv out)
  cases exit with
  | fuel => exact heq
  | done => exact (hcontinue _ _ _).trans heq
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact heq
    · cases short <;> exact (hcontinue _ _ _).trans heq

/-- A successful first descent records each preparation and the child
actually selected before any sibling search can run. -/
inductive FirstPath (ctx : Ctx n) (tcLevel : Nat) :
    Nat → Nat → Nat → σ → Nat → σ → Prop where
  | leaf (fuel level numcells : Nat) (st : σ)
      (hdiscrete : (prepareFirst ctx tcLevel level numcells st).1 = n) :
      FirstPath ctx tcLevel (fuel + 1) level numcells st level
        (prepareFirst ctx tcLevel level numcells st).2.2.2.2
  | step {fuel level numcells last : Nat} {st leaf : σ} {tv : Nat}
      (hopen : (prepareFirst ctx tcLevel level numcells st).1 ≠ n)
      (htv : (prepareFirst ctx tcLevel level numcells st).2.2.1.nextElem none = some tv)
      (horbit : Policy.orbit (n := n)
        (Policy.cheapCheck (n := n) true level
          (prepareFirst ctx tcLevel level numcells st).2.2.2.2) tv = tv)
      (tail : FirstPath ctx tcLevel fuel (level + 1)
        ((prepareFirst ctx tcLevel level numcells st).1 + 1)
        (Policy.child (n := n) true level
          (prepareFirst ctx tcLevel level numcells st).2.1.toNat tv
          (Policy.cheapCheck (n := n) true level
            (prepareFirst ctx tcLevel level numcells st).2.2.2.2)) last leaf) :
      FirstPath ctx tcLevel (fuel + 1) level numcells st last leaf

/-- The full search saves precisely the leaf reached by its first descent. -/
theorem FirstPath.reference {ctx : Ctx n} {inf tcLevel : Nat} {project : σ → α}
    (h : ReferencePolicy ctx inf tcLevel project)
    (hfirst : ∀ level tv st,
      project (Policy.afterChildFirst (n := n) level tv st) = project st)
    {fuel level numcells last : Nat} {st leaf : σ}
    (path : FirstPath ctx tcLevel fuel level numcells st last leaf) :
    project (node true ctx inf tcLevel fuel level numcells st).2 =
      project (Policy.firstterminal (n := n) last leaf) := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    unfold prepareFirst at hdisc ⊢
    dsimp only at hdisc
    rw [node]
    unfold nodeStep
    simp only [ite_true, hdisc, beq_self_eq_true, Id.run_pure]
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    have href := sweep_first_reference h hfirst fuel n level
      (prepareFirst ctx tcLevel level numcells st).1
      (prepareFirst ctx tcLevel level numcells st).2.1.toNat tv 0
      (prepareFirst ctx tcLevel level numcells st).2.2.1
      (Policy.cheapCheck (n := n) true level
        (prepareFirst ctx tcLevel level numcells st).2.2.2.2) horbit
    rw [node]
    unfold nodeStep
    change project (Id.run do
      let r := prepareFirst ctx tcLevel level numcells st
      if r.1 == n then
        return (.unwind (level - 1) false, Policy.firstterminal (n := n) level r.2.2.2.2)
      let s := sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0
        (Policy.cheapCheck (n := n) true level r.2.2.2.2)
      match s.1 with
      | .done => return (.unwind (level - 1) false,
          Policy.afterSweep (n := n) true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2)).2 = _
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ite_false,
      htv, Option.getD_some]
    generalize hs : sweep true ctx inf tcLevel fuel (n + 1) level
      (prepareFirst ctx tcLevel level numcells st).1
      (prepareFirst ctx tcLevel level numcells st).2.1.toNat tv (some tv)
      (prepareFirst ctx tcLevel level numcells st).2.2.1 0
      (Policy.cheapCheck (n := n) true level
        (prepareFirst ctx tcLevel level numcells st).2.2.2.2) = result at href ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | fuel => exact href.trans ih
    | unwind => exact href.trans ih
    | done => exact (h.afterSweep true level _ index out).trans (href.trans ih)

end Hex.GraphIso.Nauty.Generic
