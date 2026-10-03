/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerRoots

public section

namespace RealClosureConsumer

open Hex Hex.RealClosure Hex.RealClosure.Tower HexPolyMathlib.Interpret

variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Compose native producer totality, completeness, multiplicities and order.
The common model is explicit; the theorem does not assert joint realization
of infinitesimal queries in the ordinary real field. -/
theorem tower_roots (model : Model parent K) (p : DensePoly parent.Value)
    (nonzero : interpret model.value model.zero_iff p ≠ 0) :
    ∃ out, parent.roots p = .finite out ∧
      parent.roots? p = .ok (.finite out) ∧
      (out.map (fun entry => entry.denote model)).Pairwise (· < ·) ∧
      (∀ x label, (∃ entry ∈ out, entry.denote model = x ∧ entry.multiplicity = label) ↔
        (interpret model.value model.zero_iff p).IsRoot x ∧
          label = (interpret model.value model.zero_iff p).rootMultiplicity x) := by
  cases returned : parent.roots p with
  | all => exact False.elim (nonzero ((Context.roots_all model p).mp returned))
  | finite out =>
    refine ⟨out, rfl, ?_, Context.roots_sorted model p returned, ?_⟩
    · exact (Context.roots?_success model p).trans (congrArg Except.ok returned)
    · exact fun x label => Context.roots_spec model p returned x label

/-- info: 'RealClosureConsumer.tower_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tower_roots

end RealClosureConsumer
