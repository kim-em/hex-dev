/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TowerRoots
public import HexRealClosureTheory.TowerAlgebraic
public import HexRealClosureTheory.TowerUnion

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {context : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Every actual value in a native root context is algebraic over the input's
whole mathematical field, including points, reducible defining polynomials and nonmonic heads. -/
theorem Root.values_algebraic (root : Root context) (model : Model context K)
    (a : root.context.Value) : IsAlgebraic model.field ((root.model model).value a) := by
  cases root with
  | point value =>
    change context.Value at a
    change IsAlgebraic model.field (model.value a)
    have algebraic := isAlgebraic_algebraMap (A := K) (model.toValue a)
    rw [Subfield.algebraMap_ofSubfield] at algebraic
    change IsAlgebraic model.field ((model.toValue a : model.field) : K) at algebraic
    rwa [model.coe_toValue a] at algebraic
  | selected descriptor extension built =>
    cases built
    exact model.adjoin_algebraic descriptor a

/-- Interpret the entire actual root context inside the algebraic union,
preserving all its native arithmetic, sign and equality laws. -/
@[expose] noncomputable def Root.unionModel (root : Root context) (model : Model context K) :
    Model root.context (Union.Carrier model.field K) :=
  (root.model model).restrictUnion (root.values_algebraic model)

theorem Root.unionModel_value (root : Root context) (model : Model context K)
    (a : root.context.Value) :
    ((root.unionModel model).value a : K) = (root.model model).value a := rfl

end Hex.RealClosure.Tower

namespace Hex.RealClosure.Tower.Model
open HexPolyTheory HexPolyTheory.Interpret

variable {registry : BaseContext.Registry} {context : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Choose a stored representative of a value already in the input field.
This semantic coefficient lift is used only to prove native coverage. -/
noncomputable def representative (model : Model context K) (a : model.field) : context.Value :=
  (model.toValue_surjective a).choose

theorem representative_value (model : Model context K) (a : model.field) :
    model.value (model.representative a) = (a : K) :=
  congrArg Subtype.val (model.toValue_surjective a).choose_spec

/-- A polynomial over the input's mathematical field has native coefficients.
It is a proof construction; executable callers supply their stored polynomial. -/
noncomputable def nativePoly (model : Model context K) (p : Polynomial model.field) :
    DensePoly context.Value :=
  Transport.polynomial model.representative (equiv.symm p)

theorem nativePoly_value (model : Model context K) (p : Polynomial model.field) :
    interpret model.value model.zero_iff (model.nativePoly p) = p.map model.field.subtype := by
  have zero : model.representative 0 = 0 := (model.zero_iff _).mp (by
    rw [model.representative_value]; rfl)
  apply Polynomial.ext
  intro i
  rw [coeff_interpret, nativePoly, Transport.polynomial_coeff _ zero,
    model.representative_value, Polynomial.coeff_map]
  have coefficient : (equiv.symm p).coeff i = p.coeff i := by
    rw [← coeff_toPolynomial, ← equiv_apply, equiv.apply_symm_apply]
  rw [coefficient]
  rfl

/-- Any element algebraic over the input's entire interpreted field has a
native selected-root presentation produced by `Context.roots`. Its native
context and predecessor embedding are the actual returned objects. -/
theorem algebraic_root (model : Model context K) (x : K) (algebraic : IsAlgebraic model.field x) :
    ∃ p : DensePoly context.Value, ∃ out,
      context.roots p = .finite out ∧ ∃ entry ∈ out, entry.denote model = x := by
  obtain ⟨p, nonzero, root⟩ := algebraic
  have nonzero' : interpret model.value model.zero_iff (model.nativePoly p) ≠ 0 := by
    rw [model.nativePoly_value]
    exact (Polynomial.map_ne_zero_iff model.field.subtype.injective).mpr nonzero
  have root' : (interpret model.value model.zero_iff (model.nativePoly p)).IsRoot x := by
    rw [model.nativePoly_value, Polynomial.IsRoot.def, Polynomial.eval_map]
    simpa only [Polynomial.aeval_def, Subfield.algebraMap_ofSubfield] using root
  exact ⟨model.nativePoly p, model.root_exists _ nonzero' x root'⟩

/-- Every element of the relative algebraic union is represented by an actual
native root entry over the original coefficient context. -/
theorem union_coverage (model : Model context K) (x : Union.Carrier model.field K) :
    ∃ p : DensePoly context.Value, ∃ out,
      context.roots p = .finite out ∧ ∃ entry ∈ out, entry.denote model = (x : K) :=
  model.algebraic_root (x : K) ((Union.mem_iff _).mp x.property)

/-- Native complete-root presentations describe exactly the algebraic union.
Both directions refer to actual producer entries and their stored native values. -/
theorem roots_iff_union (model : Model context K) (x : K) :
    (∃ p : DensePoly context.Value, ∃ out,
      context.roots p = .finite out ∧ ∃ entry ∈ out, entry.denote model = x) ↔
        x ∈ Union.field model.field K := by
  constructor
  · rintro ⟨p, out, produced, entry, member, value⟩
    rw [← value]
    exact (Union.mem_iff _).mpr (entry.root.values_algebraic model entry.root.value)
  · intro member
    exact model.algebraic_root x ((Union.mem_iff _).mp member)

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.algebraic_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.algebraic_root

/-- info: 'Hex.RealClosure.Tower.Model.union_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.union_coverage

/-- info: 'Hex.RealClosure.Tower.Root.unionModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Root.unionModel

/-- info: 'Hex.RealClosure.Tower.Model.roots_iff_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.roots_iff_union
