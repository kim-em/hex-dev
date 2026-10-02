/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRoots
public import HexRealClosureMathlib.TowerModel
public import HexRealClosureMathlib.RootTotal
public import HexRealClosureMathlib.TransportPolynomial

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Interpret the actual root context in the same ambient real closed field
as its coefficient context. No model is an executable constructor argument. -/
@[expose] noncomputable def Root.model (root : Root parent) (model : Model parent K) :
    Model root.context K := by
  cases root with
  | point value => exact model
  | selected descriptor extension built =>
    cases built
    exact model.adjoin descriptor

/-- Interpret the stored native value through its actual extension model. -/
@[expose] noncomputable def Root.denote (root : Root parent) (model : Model parent K) : K :=
  (root.model model).value root.value

/-- Native materialization preserves the root selected by the producer. -/
theorem Root.denote_selection (root : Root parent) (model : Model parent K) :
    root.denote model = root.selection.value model.value model.zero_iff
      model.one model.add model.sub model.mul model.nat model.sign := by
  cases root with
  | point value => rfl
  | selected descriptor extension built =>
    cases built
    exact model.adjoin_generator descriptor

/-- The explicit coefficient embedding preserves every predecessor value. -/
theorem Root.embed_value (root : Root parent) (model : Model parent K) (a : parent.Value) :
    (root.model model).value (root.embed a) = model.value a := by
  cases root with
  | point value => rfl
  | selected descriptor extension built =>
    cases built
    exact model.adjoin_embed descriptor a

/-- Embedding a polynomial preserves its actual coefficient interpretation. -/
theorem Root.embedPoly_value (root : Root parent) (model : Model parent K)
    (p : DensePoly parent.Value) :
    HexPolyMathlib.Interpret.interpret (root.model model).value (root.model model).zero_iff
      (root.embedPoly p) = HexPolyMathlib.Interpret.interpret model.value model.zero_iff p := by
  have zero : root.embed 0 = 0 := (root.model model).zero_iff _ |>.mp (by
    rw [root.embed_value model]
    exact (model.zero_iff 0).mpr rfl)
  apply Polynomial.ext
  intro i
  rw [HexPolyMathlib.Interpret.coeff_interpret, HexPolyMathlib.Interpret.coeff_interpret]
  have coefficient := Transport.polynomial_coeff root.embed zero p i
  change (root.embedPoly p).coeff i = root.embed (p.coeff i) at coefficient
  rw [coefficient, root.embed_value model]

/-- Native polynomial sign queries agree with evaluation at the selected root. -/
theorem Root.signAt_value (root : Root parent) (model : Model parent K)
    (p : DensePoly parent.Value) :
    root.signAt p = (SignType.sign
      ((HexPolyMathlib.Interpret.interpret model.value model.zero_iff p).eval
        (root.denote model)) : Int) := by
  rw [Root.signAt, (root.model model).sign,
    ← HexPolyMathlib.Interpret.eval_interpret (root.model model).value
      (root.model model).zero_iff (root.model model).add (root.model model).mul]
  rw [root.embedPoly_value model]
  rfl

/-- Compatible native root comparison succeeds and uses their common ambient
order, even when the roots own different child contexts. -/
theorem Root.compare?_correct (a b : Root parent) (model : Model parent K) :
    a.compare? b = .ok (Ord.compare (a.denote model) (b.denote model)) := by
  rw [Root.compare?, a.denote_selection model, b.denote_selection model]
  exact Isolation.Root.compare_correct model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv model.div _ _

/-- The ordinary native comparison returns the exact common ambient order. -/
theorem Root.compare_correct (a b : Root parent) (model : Model parent K) :
    a.compare b = Ord.compare (a.denote model) (b.denote model) := by
  simp only [Root.compare, a.compare?_correct b model]

/-- The value carried by one native root entry in its actual root context. -/
@[expose] noncomputable def RootEntry.denote (entry : RootEntry parent) (model : Model parent K) : K :=
  entry.root.denote model

theorem RootEntry.denote_ofEntry (entry : Roots.Entry parent.sign parent.signature)
    (model : Model parent K) :
    (RootEntry.ofEntry parent entry).denote model = entry.value model.value model.zero_iff
      model.one model.add model.sub model.mul model.nat model.sign := by
  exact (Root.ofSelection parent entry.root).denote_selection model |>.trans
    (by rw [Root.selection_ofSelection]; rfl)

/-- Native roots retain the universal output exactly for semantic zero. -/
theorem Context.roots_all (model : Model parent K) (p : DensePoly parent.Value) :
    parent.roots p = .all ↔ HexPolyMathlib.Interpret.interpret model.value model.zero_iff p = 0 := by
  have generic := Roots.roots_all model.value model.zero_iff model.one model.add model.sub
    model.mul model.nat model.sign model.neg model.inv model.div parent.signature p
  cases produced : Roots.roots parent.sign parent.signature p with
  | all => simpa [produced, Context.roots, RootSet.ofOutput] using generic
  | finite entries => simpa [produced, Context.roots, RootSet.ofOutput] using generic

/-- Native finite entries have exact coverage and original multiplicities,
interpreting their actual stored values in the common ambient model. -/
theorem Context.roots_spec (model : Model parent K) (p : DensePoly parent.Value)
    {out : List (RootEntry parent)} (returned : parent.roots p = .finite out)
    (x : K) (label : Nat) :
    (∃ entry ∈ out, entry.denote model = x ∧ entry.multiplicity = label) ↔
      (HexPolyMathlib.Interpret.interpret model.value model.zero_iff p).IsRoot x ∧
        label = (HexPolyMathlib.Interpret.interpret model.value model.zero_iff p).rootMultiplicity x := by
  obtain ⟨entries, produced, rfl⟩ := Context.roots_finite p returned
  rw [← Roots.roots_spec model.value model.zero_iff model.one model.add model.sub
    model.mul model.nat model.sign model.neg model.inv model.div p produced x label]
  constructor
  · rintro ⟨entry, member, value, multiplicity⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ⟨original, present, (RootEntry.denote_ofEntry original model).symm.trans value,
      multiplicity⟩
  · rintro ⟨entry, member, value, multiplicity⟩
    exact ⟨RootEntry.ofEntry parent entry, List.mem_map.mpr ⟨entry, member, rfl⟩,
      (RootEntry.denote_ofEntry entry model).trans value, multiplicity⟩

/-- The actual native root values are strictly increasing across all factors. -/
theorem Context.roots_sorted (model : Model parent K) (p : DensePoly parent.Value)
    {out : List (RootEntry parent)} (returned : parent.roots p = .finite out) :
    (out.map (fun entry => entry.denote model)).Pairwise (· < ·) := by
  obtain ⟨entries, produced, rfl⟩ := Context.roots_finite p returned
  simpa only [List.map_map, Function.comp_def, RootEntry.denote_ofEntry] using
    Roots.roots_sorted model.value model.zero_iff model.one model.add model.sub model.mul
      model.nat model.sign model.neg model.inv model.div p produced

/-- Every root of a nonzero native polynomial occurs as an actual stored
value returned by the complete native producer, with its coefficient embedding. -/
theorem Model.root_exists (model : Model parent K) (p : DensePoly parent.Value)
    (nonzero : HexPolyMathlib.Interpret.interpret model.value model.zero_iff p ≠ 0)
    (x : K) (root : (HexPolyMathlib.Interpret.interpret model.value model.zero_iff p).IsRoot x) :
    ∃ out, parent.roots p = .finite out ∧ ∃ entry ∈ out, entry.denote model = x := by
  cases produced : parent.roots p with
  | all => exact False.elim (nonzero ((Context.roots_all model p).mp produced))
  | finite out =>
    obtain ⟨entry, member, value, _⟩ := (Context.roots_spec model p produced x
      ((HexPolyMathlib.Interpret.interpret model.value model.zero_iff p).rootMultiplicity x)).mpr
        ⟨root, rfl⟩
    exact ⟨out, rfl, entry, member, value⟩

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Root.embed_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.embed_value

/-- info: 'Hex.RealClosure.Tower.Root.signAt_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.signAt_value

/-- info: 'Hex.RealClosure.Tower.Root.compare_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.compare_correct

/-- info: 'Hex.RealClosure.Tower.Context.roots_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.roots_all

/-- info: 'Hex.RealClosure.Tower.Context.roots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.roots_spec

/-- info: 'Hex.RealClosure.Tower.Context.roots_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.roots_sorted

/-- info: 'Hex.RealClosure.Tower.Model.root_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.root_exists
