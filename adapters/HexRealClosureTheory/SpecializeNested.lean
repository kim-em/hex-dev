/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Specialize
public import HexRealClosureTheory.SpecializeRegular

public section

namespace Hex.RealClosure.Specialize

open Polynomial Filter Topology

variable {F : Type} [Field F]

/-- Substitute a coefficient function preserving zero. This operation does
not require the function to preserve arithmetic outside these coefficients. -/
noncomputable def mapCoefficients (f : F → ℝ) (zero : f 0 = 0)
    (p : Polynomial F) : Polynomial ℝ :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange f zero))

/-- Each coefficient is the actual substituted source coefficient. -/
theorem mapCoefficients_coeff (f : F → ℝ) (zero : f 0 = 0)
    (p : Polynomial F) (i : Nat) :
    (mapCoefficients f zero p).coeff i = f (p.coeff i) := by
  simp [mapCoefficients, Polynomial.coeff]

/-- Reflecting zero on this polynomial's coefficients preserves its least
nonzero exponent and its corresponding coefficient. -/
theorem mapCoefficients_trailing (f : F → ℝ) (zero : f 0 = 0)
    (p : Polynomial F) (reflect : ∀ i, f (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (mapCoefficients f zero p).trailingCoeff = f p.trailingCoeff := by
  have support : (mapCoefficients f zero p).support = p.support := by
    ext i
    simp only [Polynomial.mem_support_iff, mapCoefficients_coeff]
    exact (reflect i).not
  have degree : (mapCoefficients f zero p).natTrailingDegree = p.natTrailingDegree := by
    simp only [Polynomial.natTrailingDegree, Polynomial.trailingDegree, support]
  simp only [Polynomial.trailingCoeff, degree, mapCoefficients_coeff]

section Successive

attribute [local instance 2000] Field.toGrindField
open scoped Hex.OrderedFn.Infinitesimal

/-- Every stored coefficient has a nonzero evaluation denominator and its
native infinitesimal sign at this first ordinary parameter. -/
def CoefficientData (p : Polynomial (Hex.RationalFn ℝ)) (t : ℝ) : Prop :=
  ∀ i : Nat, (HexPolyTheory.toPolynomial (p.coeff i).den).eval t ≠ 0 ∧
    (SignType.sign (evalFraction (p.coeff i) t) : Int) =
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (p.coeff i)

/-- The first-level data holds on one neighborhood, allowing it to be
intersected with other finite replay and root-count requirements. -/
theorem coefficients_near (polynomials : Finset (Polynomial (Hex.RationalFn ℝ))) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p ∈ polynomials, CoefficientData p t := by
  classical
  let fractions := insert (0 : Hex.RationalFn ℝ)
    (polynomials.biUnion fun p => p.support.image p.coeff)
  have stable : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ q ∈ fractions,
      (HexPolyTheory.toPolynomial q.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction q t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q :=
    (eventually_all_finset fractions).mpr fun q _ => fraction_sign q
  filter_upwards [stable] with t signs
  intro p hp i
  apply signs (p.coeff i)
  by_cases coefficient : p.coeff i = 0
  · simp only [coefficient, fractions, Finset.mem_insert, true_or]
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_image.mpr ⟨i, Polynomial.mem_support_iff.mpr coefficient, rfl⟩⟩)

/-- A single ordinary parameter preserves every stored coefficient sign and
its actual denominator guard in a finite polynomial family over one
infinitesimal level. The finite family includes zero coefficients too. -/
theorem exists_coefficients_parameter
    (polynomials : Finset (Polynomial (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ p ∈ polynomials, ∀ i : Nat,
      (HexPolyTheory.toPolynomial (p.coeff i).den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction (p.coeff i) t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (p.coeff i) := by
  classical
  let fractions := insert (0 : Hex.RationalFn ℝ)
    (polynomials.biUnion fun p => p.support.image p.coeff)
  obtain ⟨t, ht, below, signs⟩ := exists_fraction_parameter fractions cap positive
  refine ⟨t, ht, below, fun p hp i => signs (p.coeff i) ?_⟩
  by_cases coefficient : p.coeff i = 0
  · simp only [coefficient, fractions, Finset.mem_insert, true_or]
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_image.mpr ⟨i, Polynomial.mem_support_iff.mpr coefficient, rfl⟩⟩)

/-- Evaluating the stored zero fraction gives zero at every parameter. -/
theorem evalFraction_zero (t : ℝ) : evalFraction (0 : Hex.RationalFn ℝ) t = 0 := by
  simpa only [evalMapped, Polynomial.map_id, evalFraction] using
    evalMapped_zero (RingHom.id ℝ) t

private theorem cast_sign_zero (a : ℝ) : (SignType.sign a : Int) = 0 ↔ a = 0 := by
  rcases lt_trichotomy a 0 with negative | rfl | positive
  · simp [negative, negative.ne]
  · simp
  · simp [positive, positive.ne']

/-- First-level data reflects zero on each actual stored coefficient. -/
theorem CoefficientData.zero_iff {p : Polynomial (Hex.RationalFn ℝ)} {t : ℝ}
    (data : CoefficientData p t) (i : Nat) :
    evalFraction (p.coeff i) t = 0 ↔ p.coeff i = 0 := by
  rw [← cast_sign_zero, (data i).2, Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff]

private theorem inner_sign (q : Hex.RationalFn ℝ) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q = Hex.OrderedFn.orderSign q := by
  rw [Hex.OrderedFn.Infinitesimal.orderSign_eq]
  rcases lt_trichotomy q 0 with negative | rfl | positive
  · rw [Hex.OrderedFn.Infinitesimal.sign_of_neg negative]
    simp [negative]
  · simp
  · rw [Hex.OrderedFn.Infinitesimal.sign_of_pos positive]
    simp [positive]

/-- The actual successive-level native sign reflects canonical zero. -/
theorem nested_sign_zero_iff (fraction : Hex.RationalFn (Hex.RationalFn ℝ)) :
    Hex.OrderedFn.Infinitesimal.sign
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction = 0 ↔ fraction = 0 := by
  have signs : (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign : Hex.RationalFn ℝ → Int) =
      Hex.OrderedFn.orderSign := funext inner_sign
  rw [signs]
  exact Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff fraction

/-- Substitute the first ordinary parameter into the actual coefficients,
then evaluate the resulting polynomial at the second parameter. -/
noncomputable def evalNestedPolynomial (p : Polynomial (Hex.RationalFn ℝ))
    (first second : ℝ) : ℝ :=
  (mapCoefficients (fun q => evalFraction q first) (evalFraction_zero first) p).eval second

/-- On nested positive neighborhoods the first-level coefficient data and
second-level polynomial signs hold together. Both neighborhoods can be
intersected with additional replay or selected-root conditions. -/
theorem nested_polynomials_near (polynomials : Finset (Polynomial (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ),
      (∀ p ∈ polynomials, CoefficientData p first) ∧
      ∀ᶠ second in 𝓝[>] (0 : ℝ), ∀ p ∈ polynomials,
        (SignType.sign (evalNestedPolynomial p first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign p.trailingCoeff := by
  classical
  filter_upwards [coefficients_near polynomials] with first coefficients
  refine ⟨coefficients, ?_⟩
  let f := fun q => evalFraction q first
  let zero := evalFraction_zero first
  have stable : ∀ᶠ second in 𝓝[>] (0 : ℝ), ∀ p ∈ polynomials,
      SignType.sign ((mapCoefficients f zero p).eval second) =
        SignType.sign (mapCoefficients f zero p).trailingCoeff :=
    (eventually_all_finset polynomials).mpr fun p _ => polynomial_sign _
  filter_upwards [stable] with second signs
  intro p hp
  have reflect (i : Nat) : f (p.coeff i) = 0 ↔ p.coeff i = 0 := by
    rw [← cast_sign_zero, (coefficients p hp i).2,
      Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff]
  have integer := congrArg (fun s : SignType => (s : Int)) (signs p hp)
  rw [mapCoefficients_trailing f zero p reflect] at integer
  exact integer.trans (coefficients p hp p.natTrailingDegree).2

/-- The two parameters are chosen together from the actual finite coefficient
family. The second lies below the first, and every polynomial has its native
successive-infinitesimal sign. No sign-agreement hypothesis is supplied. -/
theorem exists_nested_parameters (polynomials : Finset (Polynomial (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ first : ℝ, 0 < first ∧ first < cap ∧
      ∃ second : ℝ, 0 < second ∧ second < first ∧ ∀ p ∈ polynomials,
        (SignType.sign (evalNestedPolynomial p first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign p.trailingCoeff := by
  classical
  obtain ⟨first, hfirst, below, coefficients⟩ :=
    exists_coefficients_parameter polynomials cap positive
  let f := fun q => evalFraction q first
  let zero := evalFraction_zero first
  let mapped := polynomials.image (mapCoefficients f zero)
  obtain ⟨second, hsecond, ordered, signs⟩ := exists_parameter mapped first hfirst
  refine ⟨first, hfirst, below, second, hsecond, ordered, fun p hp => ?_⟩
  have reflect (i : Nat) : f (p.coeff i) = 0 ↔ p.coeff i = 0 := by
    rw [← cast_sign_zero, (coefficients p hp i).2,
      Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff]
  have stable := signs (mapCoefficients f zero p)
    (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have integer := congrArg (fun s : SignType => (s : Int)) stable
  rw [mapCoefficients_trailing f zero p reflect] at integer
  exact integer.trans (coefficients p hp p.natTrailingDegree).2

/-- Evaluate the actual numerator and denominator of a successive-level
canonical fraction using the same two ordinary parameters. -/
noncomputable def evalNestedFraction (fraction : Hex.RationalFn (Hex.RationalFn ℝ))
    (first second : ℝ) : ℝ :=
  evalNestedPolynomial (HexPolyTheory.toPolynomial fraction.num) first second /
    evalNestedPolynomial (HexPolyTheory.toPolynomial fraction.den) first second

private theorem evalNestedPolynomial_zero (first second : ℝ) :
    evalNestedPolynomial 0 first second = 0 := by
  have mapped : mapCoefficients (fun q => evalFraction q first)
      (evalFraction_zero first) (0 : Polynomial (Hex.RationalFn ℝ)) = 0 := by
    ext i
    simp only [mapCoefficients_coeff, Polynomial.coeff_zero, evalFraction_zero]
  simp only [evalNestedPolynomial, mapped, Polynomial.eval_zero]

/-- Nested evaluation uses the existing guarded first-level polynomial
substitution on the actual native coefficient array. -/
theorem nested_polynomial_eq (p : Hex.DensePoly (Hex.RationalFn ℝ)) (first second : ℝ) :
    evalNestedPolynomial (HexPolyTheory.toPolynomial p) first second =
      (HexPolyTheory.toPolynomial (polynomial (RingHom.id ℝ) p first)).eval second := by
  unfold evalNestedPolynomial
  apply congrArg (fun p : Polynomial ℝ => p.eval second)
  ext i
  simp only [mapCoefficients_coeff, HexPolyTheory.coeff_toPolynomial, polynomial_coeff,
    evalFraction, evalMapped, Polynomial.map_id]

private theorem coefficient_regular {p : Hex.DensePoly (Hex.RationalFn ℝ)} {first : ℝ}
    (data : CoefficientData (HexPolyTheory.toPolynomial p) first) (i : Nat) :
    Regular (RingHom.id ℝ) first (p.coeff i) := by
  simpa only [Regular, Polynomial.map_id, HexPolyTheory.coeff_toPolynomial] using (data i).1

/-- Substitute the first ordinary parameter in the stored outer fraction,
retaining the second indeterminate as a native rational-function value. -/
noncomputable def mapFraction (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ) :
    Hex.RationalFn ℝ :=
  let numerator := polynomial (RingHom.id ℝ) f.num first
  let denominator := polynomial (RingHom.id ℝ) f.den first
  if zero : denominator = 0 then 0 else Hex.RationalFn.normalize numerator denominator zero

private theorem polynomial_reflects (p : Hex.DensePoly (Hex.RationalFn ℝ)) (first : ℝ)
    (data : CoefficientData (HexPolyTheory.toPolynomial p) first) :
    polynomial (RingHom.id ℝ) p first = 0 ↔ p = 0 := by
  apply polynomial_zero
  intro i _
  simpa only [evalFraction, evalMapped, Polynomial.map_id, HexPolyTheory.coeff_toPolynomial]
    using data.zero_iff i

/-- The canonical monic denominator stays nonzero as an outer polynomial
after substituting any first parameter, because its leading coefficient is one. -/
theorem polynomial_den_ne_zero (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ) :
    polynomial (RingHom.id ℝ) f.den first ≠ 0 := by
  have positive : 0 < f.den.size := Nat.pos_of_ne_zero
    (fun zero => f.den_ne_zero ((Hex.DensePoly.size_eq_zero_iff f.den).mp zero))
  have leading : f.den.coeff (f.den.size - 1) = 1 :=
    (Hex.DensePoly.leadingCoeff_eq_coeff_last f.den positive).symm.trans f.monic_den
  intro zero
  have coefficient := congrArg (fun p : Hex.DensePoly ℝ => p.coeff (f.den.size - 1)) zero
  rw [polynomial_coeff, leading, evalMapped_one, Hex.DensePoly.coeff_zero] at coefficient
  exact one_ne_zero coefficient

/-- First substitution represents the actual substituted stored numerator and
denominator. Monicity ensures the denominator remains an outer polynomial. -/
theorem mapFraction_represents (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ) :
    Hex.RationalFn.Represents (mapFraction f first)
      (polynomial (RingHom.id ℝ) f.num first) (polynomial (RingHom.id ℝ) f.den first) := by
  simp only [mapFraction, dite_eq_right (polynomial_den_ne_zero f first)]
  exact Hex.RationalFn.normalize_spec _ _ _

/-- Finite coefficient data provide the same actual stored presentation. -/
theorem mapFraction_spec (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (_denominator : CoefficientData (HexPolyTheory.toPolynomial f.den) first) :
    Hex.RationalFn.Represents (mapFraction f first)
      (polynomial (RingHom.id ℝ) f.num first) (polynomial (RingHom.id ℝ) f.den first) := by
  exact mapFraction_represents f first

private theorem polynomial_C (coefficient : Hex.RationalFn ℝ) (first : ℝ) :
    polynomial (RingHom.id ℝ) (Hex.DensePoly.C coefficient) first =
      Hex.DensePoly.C (evalFraction coefficient first) := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff, Hex.DensePoly.coeff_C, Hex.DensePoly.coeff_C]
  split_ifs
  · simp only [evalFraction, evalMapped, Polynomial.map_id]
  · exact evalMapped_zero (RingHom.id ℝ) first

private theorem polynomial_one (first : ℝ) :
    polynomial (RingHom.id ℝ) (1 : Hex.DensePoly (Hex.RationalFn ℝ)) first = 1 := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff]
  change evalMapped (RingHom.id ℝ) ((Hex.DensePoly.C 1).coeff i) first =
    (Hex.DensePoly.C 1).coeff i
  rw [Hex.DensePoly.coeff_C, Hex.DensePoly.coeff_C]
  split_ifs
  · exact evalMapped_one (RingHom.id ℝ) first
  · exact evalMapped_zero (RingHom.id ℝ) first

/-- First substitution fixes the outer indeterminate itself. -/
theorem mapFraction_X (first : ℝ) :
    mapFraction (Hex.RationalFn.X : Hex.RationalFn (Hex.RationalFn ℝ)) first =
      Hex.RationalFn.X := by
  apply (mapFraction_represents Hex.RationalFn.X first).eq _ (polynomial_den_ne_zero _ _)
  have indeterminate : polynomial (RingHom.id ℝ) (Hex.DensePoly.monomial 1 1) first =
      Hex.DensePoly.monomial 1 (1 : ℝ) := by
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [polynomial_coeff, Hex.DensePoly.coeff_monomial, Hex.DensePoly.coeff_monomial]
    split_ifs
    · exact evalMapped_one (RingHom.id ℝ) first
    · exact evalMapped_zero (RingHom.id ℝ) first
  change Hex.RationalFn.Represents Hex.RationalFn.X
    (polynomial (RingHom.id ℝ) (Hex.DensePoly.monomial 1 1) first)
    (polynomial (RingHom.id ℝ) 1 first)
  rw [indeterminate, polynomial_one]
  exact Hex.RationalFn.represents_self _

/-- Inner fractions substitute to constant outer fractions with their actual
ordinary value, including total division's value at a zero denominator. -/
theorem mapFraction_C (coefficient : Hex.RationalFn ℝ) (first : ℝ) :
    mapFraction (Hex.RationalFn.C coefficient) first =
      Hex.RationalFn.C (evalFraction coefficient first) := by
  apply (mapFraction_represents (Hex.RationalFn.C coefficient) first).eq _
    (polynomial_den_ne_zero _ _)
  change Hex.RationalFn.Represents (Hex.RationalFn.C (evalFraction coefficient first))
    (polynomial (RingHom.id ℝ) (Hex.DensePoly.C coefficient) first)
    (polynomial (RingHom.id ℝ) 1 first)
  rw [polynomial_C, polynomial_one]
  exact Hex.RationalFn.represents_self _

/-- First substitution preserves the unit of the outer native field. -/
theorem mapFraction_one (first : ℝ) :
    mapFraction (1 : Hex.RationalFn (Hex.RationalFn ℝ)) first = 1 := by
  apply (mapFraction_represents 1 first).eq _ (polynomial_den_ne_zero _ _)
  change Hex.RationalFn.Represents (1 : Hex.RationalFn ℝ)
    (polynomial (RingHom.id ℝ) 1 first) (polynomial (RingHom.id ℝ) 1 first)
  rw [polynomial_one]
  exact Hex.RationalFn.represents_self _

private theorem polynomial_trailing (p : Hex.DensePoly (Hex.RationalFn ℝ)) (first : ℝ)
    (data : CoefficientData (HexPolyTheory.toPolynomial p) first) :
    (HexPolyTheory.toPolynomial (polynomial (RingHom.id ℝ) p first)).trailingCoeff =
      evalFraction (HexPolyTheory.toPolynomial p).trailingCoeff first := by
  have mapped : HexPolyTheory.toPolynomial (polynomial (RingHom.id ℝ) p first) =
      mapCoefficients (fun q => evalFraction q first) (evalFraction_zero first)
        (HexPolyTheory.toPolynomial p) := by
    ext i
    simp only [HexPolyTheory.coeff_toPolynomial, polynomial_coeff, mapCoefficients_coeff,
      evalFraction, evalMapped, Polynomial.map_id]
  rw [mapped]
  exact mapCoefficients_trailing _ _ _ data.zero_iff

private theorem lowest_sign (p : Hex.DensePoly (Hex.RationalFn ℝ)) (first : ℝ)
    (data : CoefficientData (HexPolyTheory.toPolynomial p) first) :
    Hex.OrderedFn.orderSign (Hex.OrderedFn.Infinitesimal.lowestCoeff
      (polynomial (RingHom.id ℝ) p first)) =
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
      (Hex.OrderedFn.Infinitesimal.lowestCoeff p) := by
  simp only [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
  rw [polynomial_trailing p first data, Hex.OrderedFn.Infinitesimal.orderSign_eq]
  simpa only [Polynomial.trailingCoeff] using
    (data (HexPolyTheory.toPolynomial p).natTrailingDegree).2

/-- First substitution preserves the actual successive-infinitesimal sign
while retaining a native second-level fraction for later replay specialization. -/
theorem mapFraction_sign (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (numerator : CoefficientData (HexPolyTheory.toPolynomial f.num) first)
    (denominator : CoefficientData (HexPolyTheory.toPolynomial f.den) first) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (mapFraction f first) =
      Hex.OrderedFn.Infinitesimal.sign
        (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f := by
  have nonzero := (polynomial_reflects f.den first denominator).not.mpr f.den_ne_zero
  rw [Hex.OrderedFn.Infinitesimal.sign_fraction Hex.OrderedFn.orderSign
    Hex.OrderedFn.Infinitesimal.orderSign_eq (mapFraction_spec f first denominator) nonzero]
  rw [lowest_sign f.num first numerator, lowest_sign f.den first denominator]
  exact (Hex.OrderedFn.Infinitesimal.sign_fraction
    (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
    (fun q => (inner_sign q).trans (Hex.OrderedFn.Infinitesimal.orderSign_eq q))
    (Hex.RationalFn.represents_self f) f.den_ne_zero).symm

/-- The first substitution reflects zero for each fraction whose actual
stored numerator and denominator coefficient families were specialized. -/
theorem mapFraction_zero_iff (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (numerator : CoefficientData (HexPolyTheory.toPolynomial f.num) first)
    (denominator : CoefficientData (HexPolyTheory.toPolynomial f.den) first) :
    mapFraction f first = 0 ↔ f = 0 := by
  rw [← Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff, mapFraction_sign f first numerator denominator,
    nested_sign_zero_iff]

/-- One first-parameter neighborhood preserves all signs and zero tests of
recorded outer fractions before substituting their remaining indeterminate. -/
theorem mapFractions_near (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ), ∀ f ∈ fractions,
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (mapFraction f first) =
        Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
      (mapFraction f first = 0 ↔ f = 0) := by
  classical
  let polynomials := (fractions.image fun f => HexPolyTheory.toPolynomial f.num) ∪
    (fractions.image fun f => HexPolyTheory.toPolynomial f.den)
  filter_upwards [coefficients_near polynomials] with first data
  intro f present
  have numerator := data _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, present, rfl⟩))
  have denominator := data _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, present, rfl⟩))
  exact ⟨mapFraction_sign f first numerator denominator,
    mapFraction_zero_iff f first numerator denominator⟩

/-- Evaluating the remaining indeterminate after first substitution equals
actual simultaneous evaluation of the original stored fraction at that pair. -/
theorem mapFraction_eval (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (denominator : CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (guard : evalNestedPolynomial (HexPolyTheory.toPolynomial f.den) first second ≠ 0) :
    evalMapped (RingHom.id ℝ) (mapFraction f first) second =
      evalNestedFraction f first second := by
  have guard' : ((HexPolyTheory.toPolynomial (polynomial (RingHom.id ℝ) f.den first)).map
      (RingHom.id ℝ)).eval second ≠ 0 := by
    simpa only [Polynomial.map_id, nested_polynomial_eq] using guard
  rw [evalMapped_fraction (RingHom.id ℝ) second (mapFraction_spec f first denominator) guard']
  simp only [Polynomial.map_id, evalNestedFraction, nested_polynomial_eq]

/-- Actual native addition specializes using the first-level guards; closure
of the existing regular coefficient ring handles intermediate sums. -/
theorem nested_polynomial_add (p q : Hex.DensePoly (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial p) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial q) first) :
    evalNestedPolynomial (HexPolyTheory.toPolynomial (p + q)) first second =
      evalNestedPolynomial (HexPolyTheory.toPolynomial p) first second +
        evalNestedPolynomial (HexPolyTheory.toPolynomial q) first second := by
  rw [nested_polynomial_eq, polynomial_add (RingHom.id ℝ) first p q
    (fun i _ => coefficient_regular left i) (fun i _ => coefficient_regular right i),
    HexPolyTheory.toPolynomial_add, Polynomial.eval_add,
    ← nested_polynomial_eq, ← nested_polynomial_eq]

/-- Actual native multiplication specializes through the same guarded
coefficient ring, without a homomorphism on the whole infinitesimal field. -/
theorem nested_polynomial_mul (p q : Hex.DensePoly (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial p) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial q) first) :
    evalNestedPolynomial (HexPolyTheory.toPolynomial (p * q)) first second =
      evalNestedPolynomial (HexPolyTheory.toPolynomial p) first second *
        evalNestedPolynomial (HexPolyTheory.toPolynomial q) first second := by
  rw [nested_polynomial_eq, polynomial_mul (RingHom.id ℝ) first p q
    (fun i _ => coefficient_regular left i) (fun i _ => coefficient_regular right i),
    HexPolyTheory.toPolynomial_mul, Polynomial.eval_mul,
    ← nested_polynomial_eq, ← nested_polynomial_eq]

private theorem nested_lift_eval (p : Hex.DensePoly (Hex.RationalFn ℝ))
    (first second : ℝ) (P : Polynomial (regularRing (RingHom.id ℝ) first))
    (lift : P.map (regularRing (RingHom.id ℝ) first).subtype = HexPolyTheory.toPolynomial p) :
    evalNestedPolynomial (HexPolyTheory.toPolynomial p) first second =
      (P.map (evaluation (RingHom.id ℝ) first)).eval second := by
  rw [nested_polynomial_eq, polynomial_map (RingHom.id ℝ) first p P lift]

/-- Canonical outer fraction addition specializes at the same ordinary pair.
Only the actual stored coefficient guards and three outer denominator guards
are used; no interpretation of the whole infinitesimal field is assumed. -/
theorem nested_fraction_add (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial g.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first)
    (sum : CoefficientData (HexPolyTheory.toPolynomial (f + g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (f + g).den) first)
    (leftDen : evalNestedPolynomial (HexPolyTheory.toPolynomial f.den) first second ≠ 0)
    (rightDen : evalNestedPolynomial (HexPolyTheory.toPolynomial g.den) first second ≠ 0)
    (sumDen : evalNestedPolynomial (HexPolyTheory.toPolynomial (f + g).den) first second ≠ 0) :
    evalNestedFraction (f + g) first second =
      evalNestedFraction f first second + evalNestedFraction g first second := by
  classical
  obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
    (fun i _ => coefficient_regular left.1 i)
  obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
    (fun i _ => coefficient_regular left.2 i)
  obtain ⟨GN, hgn⟩ := polynomial_lift (RingHom.id ℝ) first g.num
    (fun i _ => coefficient_regular right.1 i)
  obtain ⟨GD, hgd⟩ := polynomial_lift (RingHom.id ℝ) first g.den
    (fun i _ => coefficient_regular right.2 i)
  obtain ⟨SN, hsn⟩ := polynomial_lift (RingHom.id ℝ) first (f + g).num
    (fun i _ => coefficient_regular sum.1 i)
  obtain ⟨SD, hsd⟩ := polynomial_lift (RingHom.id ℝ) first (f + g).den
    (fun i _ => coefficient_regular sum.2 i)
  have cross : SN * (FD * GD) = (FN * GD + GN * FD) * SD := by
    apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
      (regularRing (RingHom.id ℝ) first).subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_add, hfn, hfd, hgn, hgd, hsn, hsd]
    simpa only [HexPolyTheory.toPolynomial_mul, HexPolyTheory.toPolynomial_add] using
      congrArg HexPolyTheory.toPolynomial (Hex.RationalFn.add_spec f g)
  have specialized := congrArg
    (fun p => (p.map (evaluation (RingHom.id ℝ) first)).eval second) cross
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.eval_mul,
    Polynomial.eval_add, ← nested_lift_eval f.num first second FN hfn,
    ← nested_lift_eval f.den first second FD hfd, ← nested_lift_eval g.num first second GN hgn,
    ← nested_lift_eval g.den first second GD hgd, ← nested_lift_eval (f + g).num first second SN hsn,
    ← nested_lift_eval (f + g).den first second SD hsd] at specialized
  unfold evalNestedFraction
  rw [div_add_div _ _ leftDen rightDen]
  apply (div_eq_div_iff sumDen (mul_ne_zero leftDen rightDen)).mpr
  simpa only [mul_comm] using specialized

/-- Canonical outer fraction multiplication specializes at the same ordinary pair.
Only the actual stored coefficient guards and three outer denominator guards
are used; no interpretation of the whole infinitesimal field is assumed. -/
theorem nested_fraction_mul (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial g.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first)
    (product : CoefficientData (HexPolyTheory.toPolynomial (f * g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (f * g).den) first)
    (leftDen : evalNestedPolynomial (HexPolyTheory.toPolynomial f.den) first second ≠ 0)
    (rightDen : evalNestedPolynomial (HexPolyTheory.toPolynomial g.den) first second ≠ 0)
    (productDen : evalNestedPolynomial (HexPolyTheory.toPolynomial (f * g).den) first second ≠ 0) :
    evalNestedFraction (f * g) first second =
      evalNestedFraction f first second * evalNestedFraction g first second := by
  classical
  obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
    (fun i _ => coefficient_regular left.1 i)
  obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
    (fun i _ => coefficient_regular left.2 i)
  obtain ⟨GN, hgn⟩ := polynomial_lift (RingHom.id ℝ) first g.num
    (fun i _ => coefficient_regular right.1 i)
  obtain ⟨GD, hgd⟩ := polynomial_lift (RingHom.id ℝ) first g.den
    (fun i _ => coefficient_regular right.2 i)
  obtain ⟨SN, hsn⟩ := polynomial_lift (RingHom.id ℝ) first (f * g).num
    (fun i _ => coefficient_regular product.1 i)
  obtain ⟨SD, hsd⟩ := polynomial_lift (RingHom.id ℝ) first (f * g).den
    (fun i _ => coefficient_regular product.2 i)
  have cross : SN * (FD * GD) = (FN * GN) * SD := by
    apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
      (regularRing (RingHom.id ℝ) first).subtype_injective
    simp only [Polynomial.map_mul, hfn, hfd, hgn, hgd, hsn, hsd]
    simpa only [HexPolyTheory.toPolynomial_mul] using
      congrArg HexPolyTheory.toPolynomial (Hex.RationalFn.mul_spec f g)
  have specialized := congrArg
    (fun p => (p.map (evaluation (RingHom.id ℝ) first)).eval second) cross
  simp only [Polynomial.map_mul, Polynomial.eval_mul,
    ← nested_lift_eval f.num first second FN hfn,
    ← nested_lift_eval f.den first second FD hfd, ← nested_lift_eval g.num first second GN hgn,
    ← nested_lift_eval g.den first second GD hgd, ← nested_lift_eval (f * g).num first second SN hsn,
    ← nested_lift_eval (f * g).den first second SD hsd] at specialized
  unfold evalNestedFraction
  rw [div_mul_div_comm]
  apply (div_eq_div_iff productDen (mul_ne_zero leftDen rightDen)).mpr
  simpa only [mul_comm] using specialized

/-- Total canonical inversion preserves ordinary evaluation at the same pair
when the actual finite data reflects zero and the stored guards hold. -/
theorem nested_fraction_inv (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (input : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (inverse : CoefficientData (HexPolyTheory.toPolynomial f⁻¹.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f⁻¹.den) first)
    (inverseDen : evalNestedPolynomial (HexPolyTheory.toPolynomial f⁻¹.den) first second ≠ 0)
    (reflects : evalNestedFraction f first second = 0 ↔ f = 0) :
    evalNestedFraction f⁻¹ first second = (evalNestedFraction f first second)⁻¹ := by
  classical
  by_cases zero : f = 0
  · subst f
    have value : evalNestedFraction (0 : Hex.RationalFn (Hex.RationalFn ℝ)) first second = 0 := by
      change evalNestedPolynomial (HexPolyTheory.toPolynomial (0 : Hex.DensePoly (Hex.RationalFn ℝ)))
        first second / _ = 0
      rw [HexPolyTheory.toPolynomial_zero, evalNestedPolynomial_zero, zero_div]
    rw [inv_zero, value, inv_zero]
  · have numerator : evalNestedPolynomial (HexPolyTheory.toPolynomial f.num) first second ≠ 0 := by
      intro vanishes
      apply zero
      apply reflects.mp
      unfold evalNestedFraction
      rw [vanishes, zero_div]
    obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
      (fun i _ => coefficient_regular input.1 i)
    obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
      (fun i _ => coefficient_regular input.2 i)
    obtain ⟨IN, hin⟩ := polynomial_lift (RingHom.id ℝ) first f⁻¹.num
      (fun i _ => coefficient_regular inverse.1 i)
    obtain ⟨ID, hid⟩ := polynomial_lift (RingHom.id ℝ) first f⁻¹.den
      (fun i _ => coefficient_regular inverse.2 i)
    have cross : IN * FN = FD * ID := by
      apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
        (regularRing (RingHom.id ℝ) first).subtype_injective
      simp only [Polynomial.map_mul, hfn, hfd, hin, hid]
      simpa only [HexPolyTheory.toPolynomial_mul] using congrArg HexPolyTheory.toPolynomial
        (Hex.RationalFn.inv_spec f ((Hex.RationalFn.num_eq_zero f).not.mpr zero))
    have specialized := congrArg
      (fun p => (p.map (evaluation (RingHom.id ℝ) first)).eval second) cross
    simp only [Polynomial.map_mul, Polynomial.eval_mul,
      ← nested_lift_eval f.num first second FN hfn, ← nested_lift_eval f.den first second FD hfd,
      ← nested_lift_eval f⁻¹.num first second IN hin, ← nested_lift_eval f⁻¹.den first second ID hid]
      at specialized
    unfold evalNestedFraction
    rw [inv_div]
    exact (div_eq_div_iff inverseDen numerator).mpr specialized

/-- First-parameter coefficient substitution preserves canonical addition
on the finitely guarded stored operands and actual sum. -/
theorem mapFraction_add (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial g.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first)
    (sum : CoefficientData (HexPolyTheory.toPolynomial (f + g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (f + g).den) first) :
    mapFraction (f + g) first = mapFraction f first + mapFraction g first := by
  classical
  obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
    (fun i _ => coefficient_regular left.1 i)
  obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
    (fun i _ => coefficient_regular left.2 i)
  obtain ⟨GN, hgn⟩ := polynomial_lift (RingHom.id ℝ) first g.num
    (fun i _ => coefficient_regular right.1 i)
  obtain ⟨GD, hgd⟩ := polynomial_lift (RingHom.id ℝ) first g.den
    (fun i _ => coefficient_regular right.2 i)
  obtain ⟨SN, hsn⟩ := polynomial_lift (RingHom.id ℝ) first (f + g).num
    (fun i _ => coefficient_regular sum.1 i)
  obtain ⟨SD, hsd⟩ := polynomial_lift (RingHom.id ℝ) first (f + g).den
    (fun i _ => coefficient_regular sum.2 i)
  have cross : SN * (FD * GD) = (FN * GD + GN * FD) * SD := by
    apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
      (regularRing (RingHom.id ℝ) first).subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_add, hfn, hfd, hgn, hgd, hsn, hsd]
    simpa only [HexPolyTheory.toPolynomial_mul, HexPolyTheory.toPolynomial_add] using
      congrArg HexPolyTheory.toPolynomial (Hex.RationalFn.add_spec f g)
  have mapped := congrArg (fun p => p.map (evaluation (RingHom.id ℝ) first)) cross
  simp only [Polynomial.map_mul, Polynomial.map_add] at mapped
  have specialized :
      polynomial (RingHom.id ℝ) (f + g).num first *
        (polynomial (RingHom.id ℝ) f.den first * polynomial (RingHom.id ℝ) g.den first) =
      (polynomial (RingHom.id ℝ) f.num first * polynomial (RingHom.id ℝ) g.den first +
        polynomial (RingHom.id ℝ) g.num first * polynomial (RingHom.id ℝ) f.den first) *
        polynomial (RingHom.id ℝ) (f + g).den first := by
    apply (HexPolyTheory.equiv (R := ℝ)).injective
    change HexPolyTheory.toPolynomial _ = HexPolyTheory.toPolynomial _
    simp only [HexPolyTheory.toPolynomial_mul, HexPolyTheory.toPolynomial_add]
    rw [polynomial_map (RingHom.id ℝ) first f.num FN hfn,
      polynomial_map (RingHom.id ℝ) first f.den FD hfd,
      polynomial_map (RingHom.id ℝ) first g.num GN hgn,
      polynomial_map (RingHom.id ℝ) first g.den GD hgd,
      polynomial_map (RingHom.id ℝ) first (f + g).num SN hsn,
      polynomial_map (RingHom.id ℝ) first (f + g).den SD hsd]
    exact mapped
  have represented : Hex.RationalFn.Represents (mapFraction (f + g) first)
      (polynomial (RingHom.id ℝ) f.num first * polynomial (RingHom.id ℝ) g.den first +
        polynomial (RingHom.id ℝ) g.num first * polynomial (RingHom.id ℝ) f.den first)
      (polynomial (RingHom.id ℝ) f.den first * polynomial (RingHom.id ℝ) g.den first) := by
    have source := mapFraction_spec (f + g) first sum.2
    unfold Hex.RationalFn.Represents at *
    apply Hex.DensePoly.mul_right_cancel
      ((polynomial_reflects (f + g).den first sum.2).not.mpr (f + g).den_ne_zero)
    grind
  exact represented.eq ((mapFraction_spec f first left.2).add (mapFraction_spec g first right.2))
    (Hex.DensePoly.mul_ne_zero ((polynomial_reflects f.den first left.2).not.mpr f.den_ne_zero)
      ((polynomial_reflects g.den first right.2).not.mpr g.den_ne_zero))

/-- First-parameter coefficient substitution preserves canonical multiplication
on the finitely guarded stored operands and actual product. -/
theorem mapFraction_mul (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial g.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first)
    (product : CoefficientData (HexPolyTheory.toPolynomial (f * g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (f * g).den) first) :
    mapFraction (f * g) first = mapFraction f first * mapFraction g first := by
  classical
  obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
    (fun i _ => coefficient_regular left.1 i)
  obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
    (fun i _ => coefficient_regular left.2 i)
  obtain ⟨GN, hgn⟩ := polynomial_lift (RingHom.id ℝ) first g.num
    (fun i _ => coefficient_regular right.1 i)
  obtain ⟨GD, hgd⟩ := polynomial_lift (RingHom.id ℝ) first g.den
    (fun i _ => coefficient_regular right.2 i)
  obtain ⟨SN, hsn⟩ := polynomial_lift (RingHom.id ℝ) first (f * g).num
    (fun i _ => coefficient_regular product.1 i)
  obtain ⟨SD, hsd⟩ := polynomial_lift (RingHom.id ℝ) first (f * g).den
    (fun i _ => coefficient_regular product.2 i)
  have cross : SN * (FD * GD) = (FN * GN) * SD := by
    apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
      (regularRing (RingHom.id ℝ) first).subtype_injective
    simp only [Polynomial.map_mul, hfn, hfd, hgn, hgd, hsn, hsd]
    simpa only [HexPolyTheory.toPolynomial_mul] using
      congrArg HexPolyTheory.toPolynomial (Hex.RationalFn.mul_spec f g)
  have mapped := congrArg (fun p => p.map (evaluation (RingHom.id ℝ) first)) cross
  simp only [Polynomial.map_mul] at mapped
  have specialized :
      polynomial (RingHom.id ℝ) (f * g).num first *
        (polynomial (RingHom.id ℝ) f.den first * polynomial (RingHom.id ℝ) g.den first) =
      (polynomial (RingHom.id ℝ) f.num first * polynomial (RingHom.id ℝ) g.num first) *
        polynomial (RingHom.id ℝ) (f * g).den first := by
    apply (HexPolyTheory.equiv (R := ℝ)).injective
    change HexPolyTheory.toPolynomial _ = HexPolyTheory.toPolynomial _
    simp only [HexPolyTheory.toPolynomial_mul]
    rw [polynomial_map (RingHom.id ℝ) first f.num FN hfn,
      polynomial_map (RingHom.id ℝ) first f.den FD hfd,
      polynomial_map (RingHom.id ℝ) first g.num GN hgn,
      polynomial_map (RingHom.id ℝ) first g.den GD hgd,
      polynomial_map (RingHom.id ℝ) first (f * g).num SN hsn,
      polynomial_map (RingHom.id ℝ) first (f * g).den SD hsd]
    exact mapped
  have represented : Hex.RationalFn.Represents (mapFraction (f * g) first)
      (polynomial (RingHom.id ℝ) f.num first * polynomial (RingHom.id ℝ) g.num first)
      (polynomial (RingHom.id ℝ) f.den first * polynomial (RingHom.id ℝ) g.den first) := by
    have source := mapFraction_spec (f * g) first product.2
    unfold Hex.RationalFn.Represents at *
    apply Hex.DensePoly.mul_right_cancel
      ((polynomial_reflects (f * g).den first product.2).not.mpr (f * g).den_ne_zero)
    grind
  exact represented.eq ((mapFraction_spec f first left.2).mul (mapFraction_spec g first right.2))
    (Hex.DensePoly.mul_ne_zero ((polynomial_reflects f.den first left.2).not.mpr f.den_ne_zero)
      ((polynomial_reflects g.den first right.2).not.mpr g.den_ne_zero))

/-- First-parameter substitution preserves total inversion, including zero,
on the actual guarded input and stored inverse. -/
theorem mapFraction_inv (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (input : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (inverse : CoefficientData (HexPolyTheory.toPolynomial f⁻¹.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f⁻¹.den) first) :
    mapFraction f⁻¹ first = (mapFraction f first)⁻¹ := by
  classical
  by_cases zero : f = 0
  · have left := (mapFraction_zero_iff f⁻¹ first inverse.1 inverse.2).mpr
      (by rw [zero, inv_zero])
    have right := (mapFraction_zero_iff f first input.1 input.2).mpr zero
    rw [left, right, inv_zero]
  · obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
      (fun i _ => coefficient_regular input.1 i)
    obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
      (fun i _ => coefficient_regular input.2 i)
    obtain ⟨IN, hin⟩ := polynomial_lift (RingHom.id ℝ) first f⁻¹.num
      (fun i _ => coefficient_regular inverse.1 i)
    obtain ⟨ID, hid⟩ := polynomial_lift (RingHom.id ℝ) first f⁻¹.den
      (fun i _ => coefficient_regular inverse.2 i)
    have cross : IN * FN = FD * ID := by
      apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
        (regularRing (RingHom.id ℝ) first).subtype_injective
      simp only [Polynomial.map_mul, hfn, hfd, hin, hid]
      simpa only [HexPolyTheory.toPolynomial_mul] using congrArg HexPolyTheory.toPolynomial
        (Hex.RationalFn.inv_spec f ((Hex.RationalFn.num_eq_zero f).not.mpr zero))
    have mapped := congrArg (fun p => p.map (evaluation (RingHom.id ℝ) first)) cross
    simp only [Polynomial.map_mul] at mapped
    have specialized :
        polynomial (RingHom.id ℝ) f⁻¹.num first * polynomial (RingHom.id ℝ) f.num first =
        polynomial (RingHom.id ℝ) f.den first * polynomial (RingHom.id ℝ) f⁻¹.den first := by
      apply (HexPolyTheory.equiv (R := ℝ)).injective
      change HexPolyTheory.toPolynomial _ = HexPolyTheory.toPolynomial _
      simp only [HexPolyTheory.toPolynomial_mul]
      rw [polynomial_map (RingHom.id ℝ) first f.num FN hfn,
        polynomial_map (RingHom.id ℝ) first f.den FD hfd,
        polynomial_map (RingHom.id ℝ) first f⁻¹.num IN hin,
        polynomial_map (RingHom.id ℝ) first f⁻¹.den ID hid]
      exact mapped
    have represented := (mapFraction_spec f first input.2).mul
      (mapFraction_spec f⁻¹ first inverse.2)
    have one : Hex.RationalFn.Represents (1 : Hex.RationalFn ℝ)
        (polynomial (RingHom.id ℝ) f.num first * polynomial (RingHom.id ℝ) f⁻¹.num first)
        (polynomial (RingHom.id ℝ) f.den first * polynomial (RingHom.id ℝ) f⁻¹.den first) := by
      change 1 * _ = _ * 1
      grind
    exact eq_inv_of_mul_eq_one_right (represented.eq one
      (Hex.DensePoly.mul_ne_zero
        ((polynomial_reflects f.den first input.2).not.mpr f.den_ne_zero)
        ((polynomial_reflects f⁻¹.den first inverse.2).not.mpr f⁻¹.den_ne_zero)))

/-- First substitution preserves negation of every stored coefficient,
including coefficients whose numerator vanishes at the prescribed point. -/
private theorem polynomial_neg (p : Hex.DensePoly (Hex.RationalFn ℝ)) (first : ℝ) :
    polynomial (RingHom.id ℝ) (-p) first = -polynomial (RingHom.id ℝ) p first := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff, Hex.DensePoly.coeff_neg_ring, Hex.DensePoly.coeff_neg_ring,
    polynomial_coeff]
  simpa only [zero_sub] using evalMapped_neg (RingHom.id ℝ) (p.coeff i) first

/-- Canonical outer negation preserves the first substituted fraction. -/
theorem mapFraction_neg (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (denominator : CoefficientData (HexPolyTheory.toPolynomial f.den) first) :
    mapFraction (-f) first = -mapFraction f first := by
  apply (mapFraction_spec (-f) first denominator).eq _
    ((polynomial_reflects f.den first denominator).not.mpr f.den_ne_zero)
  change Hex.RationalFn.Represents (-mapFraction f first)
    (polynomial (RingHom.id ℝ) (-f.num) first) (polynomial (RingHom.id ℝ) f.den first)
  rw [polynomial_neg]
  exact (mapFraction_spec f first denominator).neg

private theorem evalNestedPolynomial_neg (p : Hex.DensePoly (Hex.RationalFn ℝ))
    (first second : ℝ) :
    evalNestedPolynomial (HexPolyTheory.toPolynomial (-p)) first second =
      -evalNestedPolynomial (HexPolyTheory.toPolynomial p) first second := by
  rw [nested_polynomial_eq, polynomial_neg, HexPolyTheory.toPolynomial_neg,
    Polynomial.eval_neg, nested_polynomial_eq]

/-- Total ordinary evaluation preserves canonical outer negation. -/
theorem nested_fraction_neg (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ) :
    evalNestedFraction (-f) first second = -evalNestedFraction f first second := by
  change evalNestedPolynomial (HexPolyTheory.toPolynomial (-f.num)) first second /
    evalNestedPolynomial (HexPolyTheory.toPolynomial f.den) first second =
    -(evalNestedPolynomial (HexPolyTheory.toPolynomial f.num) first second /
      evalNestedPolynomial (HexPolyTheory.toPolynomial f.den) first second)
  rw [evalNestedPolynomial_neg, neg_div]

/-- The finite coefficient guards and signs remain valid under negation. -/
theorem CoefficientData.neg {p : Polynomial (Hex.RationalFn ℝ)} {first : ℝ}
    (data : CoefficientData p first) : CoefficientData (-p) first := by
  intro i
  rw [Polynomial.coeff_neg]
  refine ⟨(data i).1, ?_⟩
  have mapped : evalFraction (-p.coeff i) first = -evalFraction (p.coeff i) first := by
    simpa only [evalFraction, evalMapped, Polynomial.map_id] using
      evalMapped_neg (RingHom.id ℝ) (p.coeff i) first
  rw [mapped, Left.sign_neg, SignType.coe_neg,
    Hex.OrderedFn.Infinitesimal.sign_neg, (data i).2]

/-- First substitution preserves the actual canonical difference using the
guarded operands and its stored result. -/
theorem mapFraction_sub (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial g.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first)
    (difference : CoefficientData (HexPolyTheory.toPolynomial (f - g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (f - g).den) first) :
    mapFraction (f - g) first = mapFraction f first - mapFraction g first := by
  have negative : CoefficientData (HexPolyTheory.toPolynomial (-g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (-g).den) first := by
    change CoefficientData (HexPolyTheory.toPolynomial (-g.num)) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first
    rw [HexPolyTheory.toPolynomial_neg]
    exact ⟨right.1.neg, right.2⟩
  simpa only [sub_eq_add_neg, mapFraction_neg g first right.2] using
    mapFraction_add f (-g) first left negative (by simpa only [sub_eq_add_neg] using difference)

/-- Ordinary evaluation preserves the actual stored difference at the same
parameter pair as the operands. -/
theorem nested_fraction_sub (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyTheory.toPolynomial f.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyTheory.toPolynomial g.num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first)
    (difference : CoefficientData (HexPolyTheory.toPolynomial (f - g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (f - g).den) first)
    (leftDen : evalNestedPolynomial (HexPolyTheory.toPolynomial f.den) first second ≠ 0)
    (rightDen : evalNestedPolynomial (HexPolyTheory.toPolynomial g.den) first second ≠ 0)
    (differenceDen : evalNestedPolynomial (HexPolyTheory.toPolynomial (f - g).den) first second ≠ 0) :
    evalNestedFraction (f - g) first second =
      evalNestedFraction f first second - evalNestedFraction g first second := by
  have negative : CoefficientData (HexPolyTheory.toPolynomial (-g).num) first ∧
      CoefficientData (HexPolyTheory.toPolynomial (-g).den) first := by
    change CoefficientData (HexPolyTheory.toPolynomial (-g.num)) first ∧
      CoefficientData (HexPolyTheory.toPolynomial g.den) first
    rw [HexPolyTheory.toPolynomial_neg]
    exact ⟨right.1.neg, right.2⟩
  simpa only [sub_eq_add_neg, nested_fraction_neg] using
    nested_fraction_add f (-g) first second left negative
      (by simpa only [sub_eq_add_neg] using difference) leftDen rightDen
      (by simpa only [sub_eq_add_neg] using differenceDen)

private theorem nested_fraction_sign
    (fraction : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (numerator : (SignType.sign (evalNestedPolynomial
      (HexPolyTheory.toPolynomial fraction.num) first second) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
          (HexPolyTheory.toPolynomial fraction.num).trailingCoeff)
    (denominator : (SignType.sign (evalNestedPolynomial
      (HexPolyTheory.toPolynomial fraction.den) first second) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
          (HexPolyTheory.toPolynomial fraction.den).trailingCoeff) :
    evalNestedPolynomial (HexPolyTheory.toPolynomial fraction.den) first second ≠ 0 ∧
      (SignType.sign (evalNestedFraction fraction first second) : Int) =
        Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction := by
  rw [← Hex.OrderedFn.Infinitesimal.lowestCoeff_eq] at numerator denominator
  have nonzero : HexPolyTheory.toPolynomial fraction.den ≠ 0 := by
    intro zero
    apply fraction.den_ne_zero
    apply Hex.DensePoly.ext_coeff
    intro i
    have equal := congrArg (fun p : Polynomial (Hex.RationalFn ℝ) => p.coeff i) zero
    simpa only [HexPolyTheory.coeff_toPolynomial, Polynomial.coeff_zero,
      Hex.DensePoly.coeff_zero] using equal
  have lowest : Hex.OrderedFn.Infinitesimal.lowestCoeff fraction.den ≠ 0 := by
    rw [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
    exact trailingCoeff_nonzero_iff_nonzero.mpr nonzero
  have guard : evalNestedPolynomial (HexPolyTheory.toPolynomial fraction.den) first second ≠ 0 := by
    intro zero
    have vanishes : Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
        (Hex.OrderedFn.Infinitesimal.lowestCoeff fraction.den) = 0 := by
      simpa only [zero, sign_zero, SignType.coe_zero] using denominator.symm
    exact lowest ((Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff _).mp vanishes)
  refine ⟨guard, ?_⟩
  by_cases zero : fraction.num = 0
  · rw [Hex.OrderedFn.Infinitesimal.sign, ite_eq_left zero]
    simp only [evalNestedFraction, zero, HexPolyTheory.toPolynomial_zero,
      evalNestedPolynomial_zero, zero_div, sign_zero, SignType.coe_zero]
  · have inverse (a : ℝ) : SignType.sign a⁻¹ = SignType.sign a := by
      simp only [sign_apply, inv_pos, inv_lt_zero]
    rw [Hex.OrderedFn.Infinitesimal.sign, ite_eq_right zero]
    simp only [evalNestedFraction, div_eq_mul_inv, sign_mul, inverse,
      SignType.coe_mul, numerator, denominator]


/-- All canonical fractions in the finite family share one ordinary pair.
Every actual denominator remains nonzero and every native successive-level
sign is preserved, including the zero numerator case. -/
theorem exists_nested_fraction_parameters
    (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ first : ℝ, 0 < first ∧ first < cap ∧
      ∃ second : ℝ, 0 < second ∧ second < first ∧ ∀ fraction ∈ fractions,
        evalNestedPolynomial (HexPolyTheory.toPolynomial fraction.den) first second ≠ 0 ∧
        (SignType.sign (evalNestedFraction fraction first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction := by
  classical
  let polynomials := (fractions.image fun q => HexPolyTheory.toPolynomial q.num) ∪
    (fractions.image fun q => HexPolyTheory.toPolynomial q.den)
  obtain ⟨first, hfirst, below, second, hsecond, ordered, signs⟩ :=
    exists_nested_parameters polynomials cap positive
  refine ⟨first, hfirst, below, second, hsecond, ordered, fun fraction present => ?_⟩
  have numerator := signs (HexPolyTheory.toPolynomial fraction.num)
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  have denominator := signs (HexPolyTheory.toPolynomial fraction.den)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  exact nested_fraction_sign fraction first second numerator denominator

/-- The actual numerator and denominator coefficient guards are retained on
the first neighborhood. On the second neighborhood all outer denominator
guards and signs hold together, so further finite requirements can compose. -/
theorem nested_fractions_near (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ),
      (∀ fraction ∈ fractions,
        CoefficientData (HexPolyTheory.toPolynomial fraction.num) first ∧
        CoefficientData (HexPolyTheory.toPolynomial fraction.den) first) ∧
      ∀ᶠ second in 𝓝[>] (0 : ℝ), ∀ fraction ∈ fractions,
        evalNestedPolynomial (HexPolyTheory.toPolynomial fraction.den) first second ≠ 0 ∧
        (SignType.sign (evalNestedFraction fraction first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction ∧
        (evalNestedFraction fraction first second = 0 ↔ fraction = 0) := by
  classical
  let polynomials := (fractions.image fun q => HexPolyTheory.toPolynomial q.num) ∪
    (fractions.image fun q => HexPolyTheory.toPolynomial q.den)
  filter_upwards [nested_polynomials_near polynomials] with first data
  refine ⟨fun fraction present => ⟨?_, ?_⟩, ?_⟩
  · exact data.1 _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  · exact data.1 _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  · filter_upwards [data.2] with second signs
    intro fraction present
    obtain ⟨guard, agreement⟩ := nested_fraction_sign fraction first second
      (signs _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩)))
      (signs _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩)))
    refine ⟨guard, agreement, ?_⟩
    rw [← cast_sign_zero, agreement, nested_sign_zero_iff]

/-- Before the second indeterminate is evaluated, one first-parameter
neighborhood preserves all recorded signs, zero tests and arithmetic steps.
Each operation uses its actual stored result from the finite inventory. -/
theorem mapArithmetic_near (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ),
      (∀ f ∈ fractions,
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (mapFraction f first) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
        (mapFraction f first = 0 ↔ f = 0)) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f + g ∈ fractions →
        mapFraction (f + g) first = mapFraction f first + mapFraction g first) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f * g ∈ fractions →
        mapFraction (f * g) first = mapFraction f first * mapFraction g first) ∧
      (∀ f ∈ fractions, f⁻¹ ∈ fractions →
        mapFraction f⁻¹ first = (mapFraction f first)⁻¹) ∧
      (∀ f ∈ fractions, mapFraction (-f) first = -mapFraction f first) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f - g ∈ fractions →
        mapFraction (f - g) first = mapFraction f first - mapFraction g first) := by
  filter_upwards [nested_fractions_near fractions] with first coefficients
  refine ⟨fun f hf => ⟨mapFraction_sign f first (coefficients.1 f hf).1
    (coefficients.1 f hf).2, mapFraction_zero_iff f first (coefficients.1 f hf).1
      (coefficients.1 f hf).2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf g hg hsum
    exact mapFraction_add f g first (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f + g) hsum)
  · intro f hf g hg hproduct
    exact mapFraction_mul f g first (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f * g) hproduct)
  · intro f hf hinverse
    exact mapFraction_inv f first (coefficients.1 f hf) (coefficients.1 f⁻¹ hinverse)

  · intro f hf
    exact mapFraction_neg f first (coefficients.1 f hf).2
  · intro f hf g hg hdifference
    exact mapFraction_sub f g first (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f - g) hdifference)

/-- At one ordinary parameter pair, every recorded sign and arithmetic step
in a finite family is preserved together. Membership requires recording each
actual result; it does not assume any coefficient interpretation laws. -/
theorem nested_arithmetic_near (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ), ∀ᶠ second in 𝓝[>] (0 : ℝ),
      (∀ f ∈ fractions,
        (SignType.sign (evalNestedFraction f first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
        (evalNestedFraction f first second = 0 ↔ f = 0)) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f + g ∈ fractions →
        evalNestedFraction (f + g) first second =
          evalNestedFraction f first second + evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f * g ∈ fractions →
        evalNestedFraction (f * g) first second =
          evalNestedFraction f first second * evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, f⁻¹ ∈ fractions →
        evalNestedFraction f⁻¹ first second = (evalNestedFraction f first second)⁻¹) ∧
      (∀ f ∈ fractions, evalNestedFraction (-f) first second = -evalNestedFraction f first second) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f - g ∈ fractions →
        evalNestedFraction (f - g) first second =
          evalNestedFraction f first second - evalNestedFraction g first second) := by
  filter_upwards [nested_fractions_near fractions] with first coefficients
  filter_upwards [coefficients.2] with second values
  refine ⟨fun f hf => (values f hf).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf g hg hsum
    exact nested_fraction_add f g first second (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f + g) hsum) (values f hf).1 (values g hg).1 (values (f + g) hsum).1
  · intro f hf g hg hproduct
    exact nested_fraction_mul f g first second (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f * g) hproduct) (values f hf).1 (values g hg).1
      (values (f * g) hproduct).1
  · intro f hf hinverse
    exact nested_fraction_inv f first second (coefficients.1 f hf) (coefficients.1 f⁻¹ hinverse)
      (values f⁻¹ hinverse).1 (values f hf).2.2
  · intro f _
    exact nested_fraction_neg f first second
  · intro f hf g hg hdifference
    exact nested_fraction_sub f g first second (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f - g) hdifference) (values f hf).1 (values g hg).1
      (values (f - g) hdifference).1

/-- One positive ordinary pair below the requested cap preserves the entire
recorded finite family, including successive-parameter order and arithmetic. -/
theorem exists_nested_arithmetic (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ first : ℝ, 0 < first ∧ first < cap ∧
      ∃ second : ℝ, 0 < second ∧ second < first ∧
      (∀ f ∈ fractions,
        (SignType.sign (evalNestedFraction f first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
        (evalNestedFraction f first second = 0 ↔ f = 0)) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f + g ∈ fractions →
        evalNestedFraction (f + g) first second =
          evalNestedFraction f first second + evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f * g ∈ fractions →
        evalNestedFraction (f * g) first second =
          evalNestedFraction f first second * evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, f⁻¹ ∈ fractions →
        evalNestedFraction f⁻¹ first second = (evalNestedFraction f first second)⁻¹) ∧
      (∀ f ∈ fractions, evalNestedFraction (-f) first second = -evalNestedFraction f first second) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f - g ∈ fractions →
        evalNestedFraction (f - g) first second =
          evalNestedFraction f first second - evalNestedFraction g first second) := by
  have firstSmall : ∀ᶠ first in 𝓝[>] (0 : ℝ), first < cap :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds positive)
  have firstPositive : ∀ᶠ first in 𝓝[>] (0 : ℝ), 0 < first := self_mem_nhdsWithin
  obtain ⟨first, ⟨data, belowCap⟩, hfirst⟩ :=
    (((nested_arithmetic_near fractions).and firstSmall).and firstPositive).exists
  have secondSmall : ∀ᶠ second in 𝓝[>] (0 : ℝ), second < first :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hfirst)
  have secondPositive : ∀ᶠ second in 𝓝[>] (0 : ℝ), 0 < second := self_mem_nhdsWithin
  obtain ⟨second, ⟨preserved, below⟩, hsecond⟩ := ((data.and secondSmall).and secondPositive).exists
  exact ⟨first, hfirst, belowCap, second, hsecond, below, preserved⟩

end Successive

/-- info: 'Hex.RealClosure.Specialize.mapCoefficients_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mapCoefficients_trailing

/-- info: 'Hex.RealClosure.Specialize.exists_nested_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_nested_parameters

/-- info: 'Hex.RealClosure.Specialize.exists_nested_fraction_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_nested_fraction_parameters

end Hex.RealClosure.Specialize

/-- info: 'Hex.RealClosure.Specialize.coefficients_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.coefficients_near

/-- info: 'Hex.RealClosure.Specialize.nested_polynomials_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_polynomials_near

/-- info: 'Hex.RealClosure.Specialize.nested_fractions_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fractions_near

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_add

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_mul

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_inv

/-- info: 'Hex.RealClosure.Specialize.nested_arithmetic_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_arithmetic_near

/-- info: 'Hex.RealClosure.Specialize.exists_nested_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_nested_arithmetic

/-- info: 'Hex.RealClosure.Specialize.mapFraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction

/-- info: 'Hex.RealClosure.Specialize.mapFraction_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_spec

/-- info: 'Hex.RealClosure.Specialize.mapFraction_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_sign

/-- info: 'Hex.RealClosure.Specialize.mapFraction_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_zero_iff

/-- info: 'Hex.RealClosure.Specialize.mapFractions_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFractions_near

/-- info: 'Hex.RealClosure.Specialize.mapFraction_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_eval

/-- info: 'Hex.RealClosure.Specialize.mapFraction_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_add

/-- info: 'Hex.RealClosure.Specialize.mapFraction_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_mul

/-- info: 'Hex.RealClosure.Specialize.mapFraction_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_inv

/-- info: 'Hex.RealClosure.Specialize.mapArithmetic_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapArithmetic_near

/-- info: 'Hex.RealClosure.Specialize.mapFraction_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_neg

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_neg

/-- info: 'Hex.RealClosure.Specialize.mapFraction_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_sub

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_sub

/-- info: 'Hex.RealClosure.Specialize.polynomial_den_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_den_ne_zero

/-- info: 'Hex.RealClosure.Specialize.mapFraction_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_represents

/-- info: 'Hex.RealClosure.Specialize.mapFraction_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_X

/-- info: 'Hex.RealClosure.Specialize.mapFraction_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_C

/-- info: 'Hex.RealClosure.Specialize.mapFraction_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_one

/-- The source dictionaries for two successive native rational-function
levels agree with the executable dictionaries used by the staged base. -/
example : Field.toGrindField (K := Hex.RationalFn ℝ) = Hex.RationalFn.instField :=
  HexRationalFnTheory.coreField_eq

example : Field.toGrindField (K := Hex.RationalFn (Hex.RationalFn ℝ)) = Hex.RationalFn.instField :=
  HexRationalFnTheory.coreField_eq
