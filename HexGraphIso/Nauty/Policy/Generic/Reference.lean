/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generic.Stable

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ α : Type} [Policy σ n]

/-- Local operations outside the first descent preserve a projection
of the policy state, such as the first labelling, codes, and target array. -/
structure ReferencePolicy (ctx : Ctx n) (inf tcLevel : Nat) (project : σ → α) : Prop where
  visit : ∀ level numcells st, project (Policy.visit ctx level numcells st).2.2 = project st
  compare : ∀ level code st, project (Policy.compareCodes (n := n) level code st) = project st
  target : ∀ level numcells st,
    project (Policy.chooseTarget false ctx tcLevel level numcells st).2.2.2 = project st
  classify : ∀ level numcells st, project (Policy.classify ctx level numcells st).2 = project st
  leaf : ∀ leaf level st, project (Policy.leafExit (n := n) leaf level st).2 = project st
  cheap : ∀ first level st, project (Policy.cheapCheck (n := n) first level st) = project st
  child : ∀ first level tc tv st, project (Policy.child (n := n) first level tc tv st) = project st
  leave : ∀ tv st, project (Policy.leaveChild (n := n) tv st) = project st
  recover : ∀ level st, project (Policy.recover (n := n) inf level st) = project st
  afterSweep : ∀ first level size index st,
    project (Policy.afterSweep (n := n) first level size index st) = project st

variable {ctx : Ctx n} {inf tcLevel : Nat} {project : σ → α}

/-- Equal projections preserve the invariant of matching a fixed reference. -/
theorem ReferencePolicy.stable (h : ReferencePolicy ctx inf tcLevel project) (ref : α) :
    StablePolicy ctx inf tcLevel (fun st => project st = ref) where
  code := fun _ _ _ => trivial
  visit := fun level numcells st hin => (h.visit level numcells st).trans hin
  compare := fun level code st _ hin => (h.compare level code st).trans hin
  target := fun level numcells st hin => (h.target level numcells st).trans hin
  classify := fun level numcells st hin => ⟨(h.classify level numcells st).trans hin, trivial⟩
  leaf := fun leaf level st _ hin => (h.leaf leaf level st).trans hin
  cheap := fun first level st hin => (h.cheap first level st).trans hin
  child := fun first level tc tv st hin => (h.child first level tc tv st).trans hin
  leave := fun tv st hin => (h.leave tv st).trans hin
  recover := fun level st hin => (h.recover level st).trans hin
  afterSweep := fun first level size index st hin => (h.afterSweep first level size index st).trans hin

/-- An off-path node preserves the projected reference fields. -/
theorem node_reference (h : ReferencePolicy ctx inf tcLevel project)
    (fuel level numcells : Nat) (st : σ) :
    project (node false ctx inf tcLevel fuel level numcells st).2 = project st :=
  node_stable (h.stable (project st)) fuel level numcells st rfl

/-- Later siblings preserve the projected reference fields. -/
theorem sweep_reference (h : ReferencePolicy ctx inf tcLevel project)
    (first : Bool) (fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : σ) (hpast : Past first tv1 cursor) :
    project (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 =
      project st :=
  sweep_stable (h.stable (project st)) first fuel cfuel level numcells tc tv1 index cursor cell st hpast rfl

end Hex.GraphIso.Nauty.Generic
