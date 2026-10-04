/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRoots
public import HexRealClosure.RootPolicy

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- Choose the finite isolation policy while retaining each root's actual
immutable owner, selected value and predecessor coefficient embedding. -/
@[expose] def Context.rootsWith (parent : Context registry) (policy : Isolation.Policy)
    (p : DensePoly parent.Value) : RootSet parent :=
  RootSet.ofOutput parent (Roots.Policy.roots policy parent.sign parent.signature p)

/-- Diagnostic policy roots before native materialization. -/
@[expose] def Context.rootsWith? (parent : Context registry) (policy : Isolation.Policy)
    (p : DensePoly parent.Value) : Except SignDet.BuildError (RootSet parent) :=
  (Roots.Policy.roots? policy parent.sign parent.signature p).map (RootSet.ofOutput parent)

/-- Finite results retain the actual policy producer's entries and labels. -/
theorem Context.rootsWith_finite {parent : Context registry} (policy : Isolation.Policy)
    (p : DensePoly parent.Value) {out : List (RootEntry parent)}
    (returned : parent.rootsWith policy p = .finite out) :
    ∃ entries, Roots.Policy.roots policy parent.sign parent.signature p = .finite entries ∧
      out = entries.map (RootEntry.ofEntry parent) := by
  cases produced : Roots.Policy.roots policy parent.sign parent.signature p with
  | all => simp [Context.rootsWith, RootSet.ofOutput, produced] at returned
  | finite entries =>
    exact ⟨entries, rfl, by simpa [Context.rootsWith, RootSet.ofOutput, produced] using returned.symm⟩

end Hex.RealClosure.Tower
