/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.NumberField
public import HexRealClosureTheory.RootTotal
public import HexRealAlgebraicTheory.FieldSign

public section

namespace Hex.RealClosure.NumberField

open HexPolyTheory.Interpret

variable (generator : RealAlgebraicNumber)

/-- Interpret coordinates at the generator's actual selected embedding.
The checked real generator makes this a real value, not a projection of a
nonreal number field. -/
noncomputable def value (a : QAdjoin generator.toAlgebraic) : ℝ :=
  (PolyQuot.toComplex a generator.toAlgebraic.rep generator.toAlgebraic.rep_mk).re

/-- The real interpretation retains the entire complex value. -/
theorem value_complex (a : QAdjoin generator.toAlgebraic) :
    (value generator a : ℂ) =
      PolyQuot.toComplex a generator.toAlgebraic.rep generator.toAlgebraic.rep_mk := by
  exact Complex.ext rfl (QAdjoin.value_real a generator.property).symm

theorem value_zero : value generator 0 = 0 := by
  simp [value, PolyQuot.map_zero]

theorem value_one : value generator 1 = 1 := by
  simp [value, PolyQuot.map_one]

theorem value_add (a b : QAdjoin generator.toAlgebraic) :
    value generator (a + b) = value generator a + value generator b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, value_complex, value_complex, value_complex, PolyQuot.map_add]

theorem value_sub (a b : QAdjoin generator.toAlgebraic) :
    value generator (a - b) = value generator a - value generator b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sub, value_complex, value_complex, value_complex, PolyQuot.map_sub]

theorem value_mul (a b : QAdjoin generator.toAlgebraic) :
    value generator (a * b) = value generator a * value generator b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, value_complex, value_complex, value_complex, PolyQuot.map_mul]

theorem value_div (a b : QAdjoin generator.toAlgebraic) :
    value generator (a / b) = value generator a / value generator b := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, value_complex, value_complex, value_complex, PolyQuot.map_div]

theorem value_neg (a : QAdjoin generator.toAlgebraic) :
    value generator (-a) = -value generator a := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, value_complex, value_complex, PolyQuot.map_neg]

theorem value_inv (a : QAdjoin generator.toAlgebraic) :
    value generator (a⁻¹) = (value generator a)⁻¹ := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_inv, value_complex, value_complex, PolyQuot.map_inv]

theorem value_nat (n : Nat) : value generator (n : QAdjoin generator.toAlgebraic) = n := by
  apply Complex.ofReal_injective
  rw [value_complex]
  change PolyQuot.toComplex ((n : Rat) • (1 : QAdjoin generator.toAlgebraic))
    generator.toAlgebraic.rep generator.toAlgebraic.rep_mk = _
  rw [PolyQuot.map_smul, PolyQuot.map_one, mul_one]
  norm_cast

/-- Reduced field coordinates reflect zero through the selected embedding. -/
theorem value_eq_zero (a : QAdjoin generator.toAlgebraic) :
    value generator a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply PolyQuot.toComplex_injective generator.toAlgebraic.rep generator.toAlgebraic.rep_mk
    dsimp only
    rw [← value_complex, h, Complex.ofReal_zero, PolyQuot.map_zero]
  · rintro rfl
    exact value_zero generator

/-- The native coefficient sign is the order of that same real embedding. -/
theorem sign_spec (a : QAdjoin generator.toAlgebraic) :
    generator.signField a = (SignType.sign (value generator a) : Int) :=
  generator.signField_spec a

/-- Coordinates gathered from different fields retain each original selected
complex value when the actual common generator passes the real check. -/
theorem common_value (inputs : Array AlgebraicNumber)
    (real : (QAdjoin.common inputs).generator.isReal = true)
    (i : Nat) (hi : i < inputs.size) :
    (value (RealAlgebraicNumber.ofAlgebraic (QAdjoin.common inputs).generator real)
      ((QAdjoin.common inputs).entries[i]'(by simpa using hi)) : ℂ) = inputs[i].toComplex := by
  exact (value_complex _ _).trans
    ((PolyQuot.toAlgebraicNumber_toComplex ((QAdjoin.common inputs).entries[i]'(by simpa using hi))
      (QAdjoin.common inputs).generator.rep (QAdjoin.common inputs).generator.rep_mk).symm.trans
      (congrArg AlgebraicNumber.toComplex (QAdjoin.common_get inputs i hi)))

/-- Interpretation of a returned entry, retaining its selected root. -/
noncomputable def rootValue {context : Nat}
    (entry : Roots.Entry generator.signField context) : ℝ :=
  entry.value (value generator) (value_eq_zero generator) (value_one generator)
    (value_add generator) (value_sub generator) (value_mul generator)
    (value_nat generator) (sign_spec generator)

/-- Interpret the original polynomial in the selected real embedding. -/
noncomputable def polynomial (p : DensePoly (QAdjoin generator.toAlgebraic)) : Polynomial ℝ :=
  interpret (value generator) (value_eq_zero generator) p

/-- Every interpreted coefficient retains its original selected real value. -/
theorem polynomial_coeff (p : DensePoly (QAdjoin generator.toAlgebraic)) (i : Nat) :
    (polynomial generator p).coeff i = value generator (p.coeff i) :=
  coeff_interpret (value generator) (value_eq_zero generator) p i

/-- The actual number-field producer succeeds on every polynomial, including
zero, without an accepted-output premise. -/
theorem roots_success (context : Nat) (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    ∃ output, roots? generator context p = .ok output ∧ roots generator context p = output :=
  Roots.roots_success (value generator) (value_eq_zero generator) (value_one generator)
    (value_add generator) (value_sub generator) (value_mul generator) (value_nat generator)
    (sign_spec generator) (value_neg generator) (value_inv generator) (value_div generator)
    context p

/-- All roots is returned exactly for a zero polynomial at the selected embedding. -/
theorem roots_all (context : Nat) (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    roots generator context p = .all ↔ polynomial generator p = 0 :=
  Roots.roots_all (value generator) (value_eq_zero generator) (value_one generator)
    (value_add generator) (value_sub generator) (value_mul generator) (value_nat generator)
    (sign_spec generator) (value_neg generator) (value_inv generator) (value_div generator)
    context p

/-- Every real root occurs once with its exact original multiplicity. -/
theorem roots_spec {context : Nat} (p : DensePoly (QAdjoin generator.toAlgebraic))
    {out : List (Roots.Entry generator.signField context)}
    (returned : roots generator context p = .finite out) (x : ℝ) (label : Nat) :
    (∃ entry ∈ out, rootValue generator entry = x ∧ entry.multiplicity = label) ↔
      (polynomial generator p).IsRoot x ∧ label = (polynomial generator p).rootMultiplicity x :=
  Roots.roots_spec (value generator) (value_eq_zero generator) (value_one generator)
    (value_add generator) (value_sub generator) (value_mul generator) (value_nat generator)
    (sign_spec generator) (value_neg generator) (value_inv generator) (value_div generator)
    p returned x label

/-- The ordinary number-field result is strictly ordered in its selected embedding. -/
theorem roots_sorted {context : Nat} (p : DensePoly (QAdjoin generator.toAlgebraic))
    {out : List (Roots.Entry generator.signField context)}
    (returned : roots generator context p = .finite out) :
    (out.map (rootValue generator)).Pairwise (· < ·) :=
  Roots.roots_sorted (value generator) (value_eq_zero generator) (value_one generator)
    (value_add generator) (value_sub generator) (value_mul generator) (value_nat generator)
    (sign_spec generator) (value_neg generator) (value_inv generator) (value_div generator)
    p returned

end Hex.RealClosure.NumberField

/-- info: 'Hex.RealClosure.NumberField.value_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_complex

/-- info: 'Hex.RealClosure.NumberField.value_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_eq_zero

/-- info: 'Hex.RealClosure.NumberField.sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.sign_spec

/-- info: 'Hex.RealClosure.NumberField.common_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.common_value

/-- info: 'Hex.RealClosure.NumberField.roots_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.roots_success

/-- info: 'Hex.RealClosure.NumberField.roots_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.roots_all

/-- info: 'Hex.RealClosure.NumberField.roots_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.roots_spec

/-- info: 'Hex.RealClosure.NumberField.roots_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.roots_sorted

/-- info: 'Hex.RealClosure.NumberField.value_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_zero

/-- info: 'Hex.RealClosure.NumberField.value_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_one

/-- info: 'Hex.RealClosure.NumberField.value_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_add

/-- info: 'Hex.RealClosure.NumberField.value_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_sub

/-- info: 'Hex.RealClosure.NumberField.value_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_mul

/-- info: 'Hex.RealClosure.NumberField.value_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_div

/-- info: 'Hex.RealClosure.NumberField.value_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_neg

/-- info: 'Hex.RealClosure.NumberField.value_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_inv

/-- info: 'Hex.RealClosure.NumberField.value_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.NumberField.value_nat
