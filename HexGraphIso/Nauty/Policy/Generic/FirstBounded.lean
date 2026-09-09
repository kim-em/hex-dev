/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generic.Leftmost
public import HexGraphIso.Nauty.Policy.Generic.Bounded
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Generic.Bounded
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.VSet.Basic

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ α : Type} [Policy σ n]

/-- An invariant established by the first child survives the entire sweep,
including a return past the receiving frame. -/
theorem sweep_first_bounded {ctx : Ctx n} {inf tcLevel bound : Nat} {P : σ → Prop}
    (h : BoundedPolicy ctx inf tcLevel bound P)
    (hfirst : ∀ level tv st, P st → P (Policy.afterChildFirst (n := n) level tv st))
    (fuel cfuel level numcells tc tv index : Nat) (cell : VSet n) (st : σ)
    (hlevel : bound ≤ level) (horbit : Policy.orbit (n := n) st tv = tv)
    (hchild : P (node true ctx inf tcLevel fuel (level + 1) (numcells + 1)
      (Policy.child (n := n) true level tc tv st)).2) :
    P (sweep true ctx inf tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st).2.2 := by
  have hpast : ∀ cell : VSet n, Past true tv (cell.nextElem (some tv)) := by
    intro cell _ v hv
    have hnext := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hnext
    omega
  have hcontinue : ∀ cell index out, P out →
      P (sweep true ctx inf tcLevel fuel cfuel level numcells tc tv
        (cell.nextElem (some tv)) cell index
        (Policy.recover (n := n) inf level out)).2.2 := by
    intro cell index out hin
    exact sweep_bounded h true fuel cfuel level numcells tc tv index _ cell _
      (hpast cell) hlevel (h.recover level out hlevel hin)
  rw [sweep]
  unfold sweepStep advance resume
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, Bool.false_and, ite_true]
  generalize hr : node true ctx inf tcLevel fuel (level + 1) (numcells + 1)
    (Policy.child (n := n) true level tc tv st) = result at hchild ⊢
  obtain ⟨exit, out⟩ := result
  have heq := h.leave tv (Policy.afterChildFirst (n := n) level tv out)
    (hfirst level tv out hchild)
  cases exit with
  | fuel => exact heq
  | done => exact hcontinue _ _ _ heq
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact heq
    · cases short <;> exact hcontinue _ _ _ heq

/-- An invariant established at the first leaf survives the full search. -/
theorem FirstPath.bounded {ctx : Ctx n} {inf tcLevel bound : Nat} {P : σ → Prop}
    (h : BoundedPolicy ctx inf tcLevel bound P)
    (hfirst : ∀ level tv st, P st → P (Policy.afterChildFirst (n := n) level tv st))
    {fuel level numcells last : Nat} {st leaf : σ}
    (path : FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : bound ≤ level)
    (hterminal : P (Policy.firstterminal (n := n) last leaf)) :
    P (node true ctx inf tcLevel fuel level numcells st).2 := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    unfold prepareFirst at hdisc hterminal
    dsimp only at hdisc
    rw [node]
    unfold nodeStep
    simpa only [ite_true, hdisc, beq_self_eq_true, Id.run_pure] using hterminal
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    have href := sweep_first_bounded h hfirst fuel n level
      (prepareFirst ctx tcLevel level numcells st).1
      (prepareFirst ctx tcLevel level numcells st).2.1.toNat tv 0
      (prepareFirst ctx tcLevel level numcells st).2.2.1
      (Policy.cheapCheck (n := n) true level
        (prepareFirst ctx tcLevel level numcells st).2.2.2.2) (by omega) horbit (ih (by omega) hterminal)
    rw [node]
    unfold nodeStep
    change P (Id.run do
      let r := prepareFirst ctx tcLevel level numcells st
      if r.1 == n then
        return (.unwind (level - 1) false, Policy.firstterminal (n := n) level r.2.2.2.2)
      let s := sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0
        (Policy.cheapCheck (n := n) true level r.2.2.2.2)
      match s.1 with
      | .done => return (.unwind (level - 1) false,
          Policy.afterSweep (n := n) true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2)).2
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
    | fuel => exact href
    | unwind => exact href
    | done => exact h.afterSweep true level _ index out (by omega) href

end Hex.GraphIso.Nauty.Generic
