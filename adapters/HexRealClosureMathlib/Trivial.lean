/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Trivial
public import HexRealClosureMathlib.Canonical
public import HexRealClosureMathlib.RootTotal
public import HexRealAlgebraicMathlib.Roots
public import Mathlib.Data.List.Sort

public section

namespace Hex.RealClosure.Trivial.Rational

private theorem ratNeg (q : Rat) : ratCast (-q) = -ratCast q := by simp [ratCast]
private theorem ratInv (q : Rat) : ratCast q⁻¹ = (ratCast q)⁻¹ := by simp [ratCast]

/-- The backend coefficient conversion denotes the original rational polynomial. -/
theorem polynomial_real (p : DensePoly Rat) : (polynomial p).toPolynomial = realPoly p := by
  ext i
  rw [polynomial, RealAlgebraicPoly.coeff_ofArray, realPoly, HexPolyMathlib.Interpret.coeff_interpret]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map,
    DensePoly.coeff, DensePoly.toArray]
  cases h : p.coeffs[i]? with
  | some q => simp [ratCast]
  | none =>
    simp only [Option.map_none, Option.getD_none, RealAlgebraicNumber.zero_toReal]
    exact ((ratZero (0 : Rat)).mpr rfl).symm

/-- The actual converted generic root agrees with its selected real value. -/
theorem canonical_real {context : Nat} (root : Isolation.Root (Sturm.orderSign : Rat → Int) context) :
    (canonical root).toReal = root.value ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign := by
  cases root with
  | point q => simp [canonical, Isolation.Root.value, ratCast]
  | selected descriptor => exact Hex.RealClosure.Root.toCanonical_real descriptor

/-- The complete generic comparison succeeds and agrees with the existing
real-algebraic backend after the actual root conversion. -/
theorem compare_eq {context : Nat} (a b : Isolation.Root (Sturm.orderSign : Rat → Int) context) :
    a.compare b = .ok (compare a b) := by
  rw [compare, RealAlgebraicNumber.compare_eq, canonical_real, canonical_real]
  exact Isolation.Root.compare_correct ratCast ratZero ratOne ratAdd ratSub ratMul
    ratNat ratSign ratNeg ratInv ratDiv a b

private theorem count_ext (a b : RealRootCount) (root : a.root = b.root)
    (multiplicity : a.multiplicity = b.multiplicity) : a = b := by
  cases a
  cases b
  cases root
  cases multiplicity
  rfl

/-- Conversion retains the selected value of an actual generic entry. -/
theorem entry_real {context : Nat} (e : Roots.Entry (Sturm.orderSign : Rat → Int) context) :
    (entry e).root.toReal = e.value ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign :=
  canonical_real e.root

private theorem entries_spec {context : Nat} (p : DensePoly Rat)
    {out : List (Roots.Entry (Sturm.orderSign : Rat → Int) context)}
    (returned : Roots.roots Sturm.orderSign context p = .finite out) (s : RealRootCount) :
    s ∈ out.map entry ↔ (realPoly p).IsRoot s.root.toReal ∧
      s.multiplicity = (realPoly p).rootMultiplicity s.root.toReal := by
  have spec := Roots.roots_spec ratCast ratZero ratOne ratAdd ratSub ratMul ratNat
    ratSign ratNeg ratInv ratDiv p returned s.root.toReal s.multiplicity
  change _ ↔ (realPoly p).IsRoot s.root.toReal ∧
    s.multiplicity = (realPoly p).rootMultiplicity s.root.toReal at spec
  rw [← spec]
  constructor
  · intro member
    obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
    exact ⟨e, present, (entry_real e).symm, rfl⟩
  · rintro ⟨e, present, value, multiplicity⟩
    apply List.mem_map.mpr
    exact ⟨e, present, count_ext _ _
      (RealAlgebraicNumber.toReal_injective ((entry_real e).trans value)) multiplicity⟩

private theorem entries_sorted {context : Nat} (p : DensePoly Rat)
    {out : List (Roots.Entry (Sturm.orderSign : Rat → Int) context)}
    (returned : Roots.roots Sturm.orderSign context p = .finite out) :
    (out.map entry).Pairwise (fun a b => a.root.toReal < b.root.toReal) := by
  have ordered := Roots.roots_sorted ratCast ratZero ratOne ratAdd ratSub ratMul ratNat
    ratSign ratNeg ratInv ratDiv p returned
  rw [List.pairwise_map] at ordered ⊢
  apply ordered.imp
  intro a b less
  simpa only [entry_real] using less

private theorem backend_spec (p : DensePoly Rat) {out : Array RealRootCount}
    (returned : (polynomial p).roots = .finite out) (s : RealRootCount) :
    s ∈ out.toList ↔ (realPoly p).IsRoot s.root.toReal ∧
      s.multiplicity = (realPoly p).rootMultiplicity s.root.toReal := by
  have member (e : RealRootCount) (present : e ∈ out.toList) :
      e ∈ (polynomial p).roots.toArray := by
    simpa [returned, RealRootSet.toArray, RealRootSet.finite?] using present
  constructor
  · intro present
    have root := (RealAlgebraicPoly.contains_roots_iff (polynomial p) s.root.toReal).mp
      (by rw [returned]; exact ⟨s, present, rfl⟩)
    rw [polynomial_real] at root
    have multiplicity := RealAlgebraicPoly.roots_multiplicity (polynomial p) s (member s present)
    rw [polynomial_real] at multiplicity
    exact ⟨root, multiplicity⟩
  · rintro ⟨root, multiplicity⟩
    have contains := (RealAlgebraicPoly.contains_roots_iff (polynomial p) s.root.toReal).mpr
      (by rw [polynomial_real]; exact root)
    rw [returned, RealRootSet.Contains] at contains
    obtain ⟨e, present, value⟩ := contains
    have actual := RealAlgebraicPoly.roots_multiplicity (polynomial p) e (member e present)
    rw [polynomial_real, value] at actual
    have same := count_ext e s (RealAlgebraicNumber.toReal_injective value)
      (actual.trans multiplicity.symm)
    exact same ▸ present

/-- After actual canonical conversion, the generic rational route is exactly
the existing complete real-algebraic root API, including `all`, order and
positive multiplicities. No root-identity or Tarski algorithm is duplicated. -/
theorem roots_eq (context : Nat) (p : DensePoly Rat) :
    roots context p = (polynomial p).roots := by
  have all := Roots.roots_all ratCast ratZero ratOne ratAdd ratSub ratMul ratNat
    ratSign ratNeg ratInv ratDiv context p
  cases generic : Roots.roots Sturm.orderSign context p with
  | all =>
    have zero : realPoly p = 0 := all.mp generic
    have backend := (RealAlgebraicPoly.roots_all_iff (polynomial p)).mpr
      ((polynomial_real p).trans zero)
    simp only [roots, generic, output, backend]
  | finite entries =>
    cases backend : (polynomial p).roots with
    | all =>
      have zero : realPoly p = 0 := (polynomial_real p).symm.trans
        ((RealAlgebraicPoly.roots_all_iff (polynomial p)).mp backend)
      have impossible := all.mpr zero
      rw [generic] at impossible
      cases impossible
    | finite existing =>
      have backend_order := RealAlgebraicPoly.roots_sorted (polynomial p)
      simp only [backend, RealRootSet.toArray, RealRootSet.finite?, Option.getD_some] at backend_order
      have ordered := backend_order.imp (fun h => (RealAlgebraicNumber.lt_iff _ _).mp h)
      let relation := fun a b : RealRootCount => a.root.toReal < b.root.toReal
      letI : Std.Antisymm relation := ⟨fun _ _ less greater => False.elim ((lt_asymm less) greater)⟩
      letI : Std.Irrefl relation := ⟨fun _ => lt_irrefl _⟩
      have same : entries.map entry = existing.toList :=
        List.Pairwise.eq_of_mem_iff (r := relation) (entries_sorted p generic) ordered
          (fun s => (entries_spec p generic s).trans (backend_spec p backend s).symm)
      simp only [roots, generic, output, backend]
      rw [same, Array.toArray_toList]

end Hex.RealClosure.Trivial.Rational

/-- info: 'Hex.RealClosure.Trivial.Rational.compare_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Rational.compare_eq

/-- info: 'Hex.RealClosure.Trivial.Rational.roots_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Rational.roots_eq
