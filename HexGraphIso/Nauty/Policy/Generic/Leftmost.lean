/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generic.Reference
import all HexGraphIso.Nauty.Policy.Generic.Reference
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.VSet.Basic

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ α : Type} {γ : Type} [Policy σ n (γ := γ)]

/-- Refine the first path, save its code, and select its target. -/
def prepareFirst (ctx : γ) (tcLevel level numcells : Nat) (st : σ) :
    Nat × Int × VSet n × Nat × σ :=
  let r := Policy.visit ctx level numcells st
  (r.1, Policy.chooseTarget true ctx tcLevel level r.1
    (Policy.recordFirst (n := n) level r.2.1 r.2.2))

/-- An invariant established by the first child survives the entire sweep,
including a return past the receiving frame. -/
theorem sweep_first_stable {ctx : γ} {inf tcLevel : Nat} {P : σ → Prop}
    {validCode : Nat → Prop} {validLeaf : Leaf → σ → Prop}
    (h : StablePolicy ctx inf tcLevel P validCode validLeaf)
    (hfirst : ∀ level tv st, P st → P (Policy.afterChildFirst (n := n) level tv st))
    (fuel cfuel level numcells tc tv index : Nat) (cell : VSet n) (st : σ)
    (horbit : Policy.orbit (n := n) st tv = tv)
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
    exact sweep_stable h true fuel cfuel level numcells tc tv index _ cell _
      (hpast cell) (h.recover level out hin)
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

/-- A successful first descent records each preparation and the child
actually selected before any sibling search can run. -/
inductive FirstPath (ctx : γ) (tcLevel : Nat) :
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

/-- An invariant established at the first leaf survives the full search. -/
theorem FirstPath.stable {ctx : γ} {inf tcLevel : Nat} {P : σ → Prop}
    {validCode : Nat → Prop} {validLeaf : Leaf → σ → Prop}
    (h : StablePolicy ctx inf tcLevel P validCode validLeaf)
    (hfirst : ∀ level tv st, P st → P (Policy.afterChildFirst (n := n) level tv st))
    (hfinish : ∀ level size index st, P st → P (Policy.afterSweep (n := n) true level size index st))
    {fuel level numcells last : Nat} {st leaf : σ}
    (path : FirstPath ctx tcLevel fuel level numcells st last leaf)
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
    have href := sweep_first_stable h hfirst fuel n level
      (prepareFirst ctx tcLevel level numcells st).1
      (prepareFirst ctx tcLevel level numcells st).2.1.toNat tv 0
      (prepareFirst ctx tcLevel level numcells st).2.2.1
      (Policy.cheapCheck (n := n) true level
        (prepareFirst ctx tcLevel level numcells st).2.2.2.2) horbit (ih hterminal)
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
    | done => exact hfinish level _ index out href

/-- The first child determines the reference retained by its entire sweep. -/
theorem sweep_first_reference {ctx : γ} {inf tcLevel : Nat} {project : σ → α}
    (h : ReferencePolicy ctx inf tcLevel project)
    (hfirst : ∀ level tv st,
      project (Policy.afterChildFirst (n := n) level tv st) = project st)
    (fuel cfuel level numcells tc tv index : Nat) (cell : VSet n) (st : σ)
    (horbit : Policy.orbit (n := n) st tv = tv) :
    project (sweep true ctx inf tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st).2.2 =
    project (node true ctx inf tcLevel fuel (level + 1) (numcells + 1)
      (Policy.child (n := n) true level tc tv st)).2 :=
  sweep_first_stable (h.stable _) (fun level tv st hin => (hfirst level tv st).trans hin)
    fuel cfuel level numcells tc tv index cell st horbit rfl

/-- The full search saves precisely the leaf reached by its first descent. -/
theorem FirstPath.reference {ctx : γ} {inf tcLevel : Nat} {project : σ → α}
    (h : ReferencePolicy ctx inf tcLevel project)
    (hfirst : ∀ level tv st,
      project (Policy.afterChildFirst (n := n) level tv st) = project st)
    {fuel level numcells last : Nat} {st leaf : σ}
    (path : FirstPath ctx tcLevel fuel level numcells st last leaf) :
    project (node true ctx inf tcLevel fuel level numcells st).2 =
      project (Policy.firstterminal (n := n) last leaf) :=
  path.stable (h.stable _) (fun level tv st hin => (hfirst level tv st).trans hin)
    (fun level size index st hin => (h.afterSweep true level size index st).trans hin) rfl

end Hex.GraphIso.Nauty.Generic
