/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.FactorGeneric.Product

public section

/-!
# Correctness of the executable Yun squarefree decomposition

Root-multiplicity analysis of `Factor.yunRaw` over the tower coefficient
field: the loop invariant at one complex root, soundness, completeness, and
monicity of the emitted components, and acceptance of the produced
decomposition by the executable certificate check `Factor.checkYun`.
-/

namespace Hex.NumberTower

section Yun

variable {levels : List Level}
variable (hvalid : LevelsValid levels)
variable (hinjective : LevelSemantics.DenoteInjective levels)
variable (hinv : ∀ a : Arithmetic.Coeff levels,
  LevelSemantics.coeffDenote levels a⁻¹ =
    (LevelSemantics.coeffDenote levels a)⁻¹)

include hvalid hinjective hinv

/-- Monic normalisation only rescales by a unit: the interpretation of
`Norm.monic f` over `ℂ` is associated to the interpretation of `f`. -/
theorem rawPolynomial_monic_associated
    (f : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0) :
    Associated (Norm.rawPolynomial levels (Norm.monic f))
      (Norm.rawPolynomial levels f) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let ι := LevelSemantics.coeffHom levels hvalid hinjective hinv
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (HexPolyMathlib.toPolynomial f).map ι = 0
    rw [hzero, Polynomial.map_zero]
  have hsource := toPolynomial_monic_associated levels hvalid hinjective
    hinv f (by
      intro hzero
      apply hfSource
      rw [hzero, HexPolyMathlib.toPolynomial_zero])
  have hmapped := Polynomial.associated_map_map ι hsource
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
    ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change Associated
    ((HexPolyMathlib.toPolynomial (Norm.monic f)).map ι)
    ((HexPolyMathlib.toPolynomial f).map ι)
  exact hmapped

omit hvalid hinjective hinv in
/-- Associated complex polynomials have the same root multiplicity at every
point. -/
theorem rootMultiplicity_associated_complex
    {f g : Polynomial ℂ} (h : Associated f g) (z : ℂ) :
    f.rootMultiplicity z = g.rootMultiplicity z := by
  rw [← Polynomial.count_roots, ← Polynomial.count_roots, h.roots_eq]

omit hvalid hinjective hinv in
/-- Over `ℂ` the root multiplicity of a gcd at each point is the minimum of
the root multiplicities of its arguments. -/
theorem rootMultiplicity_gcd_complex
    (f g : Polynomial ℂ) (hf : f ≠ 0) (hg : g ≠ 0) (z : ℂ) :
    (EuclideanDomain.gcd f g).rootMultiplicity z =
      min (f.rootMultiplicity z) (g.rootMultiplicity z) := by
  have hgcd : EuclideanDomain.gcd f g ≠ 0 := by
    intro h
    exact hf (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  apply le_antisymm
  · exact le_min
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hf
        (EuclideanDomain.gcd_dvd_left f g) z)
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hg
        (EuclideanDomain.gcd_dvd_right f g) z)
  · rw [Polynomial.le_rootMultiplicity_iff hgcd]
    apply EuclideanDomain.dvd_gcd
    · rw [← Polynomial.le_rootMultiplicity_iff hf]
      exact min_le_left _ _
    · rw [← Polynomial.le_rootMultiplicity_iff hg]
      exact min_le_right _ _

/-- The monic normalisation of the executable gcd `DensePoly.gcd f g` divides
both `f` and `g` in the executable polynomial ring. -/
theorem monicGcd_dvd
    (f g : DensePoly (Arithmetic.Coeff levels))
    (hf : f ≠ 0) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Norm.monic (DensePoly.gcd f g) ∣ f ∧
      Norm.monic (DensePoly.gcd f g) ∣ g := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let raw := HexPolyMathlib.toPolynomial (DensePoly.gcd f g)
  let normalized := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  have hfPoly : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff levels)).injective
    simpa using hzero
  have hrawNormalized : Associated raw normalized :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hnormalized : normalized ≠ 0 := by
    intro hzero
    exact hfPoly (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hraw : raw ≠ 0 := fun hzero =>
    hnormalized (hrawNormalized.eq_zero_iff.mp hzero)
  have hmonicRaw : Associated
      (HexPolyMathlib.toPolynomial (Norm.monic (DensePoly.gcd f g))) raw :=
    toPolynomial_monic_associated levels hvalid hinjective hinv
      (DensePoly.gcd f g) (by
        intro hzero
        apply hraw
        simp [raw, hzero])
  have hmonicNormalized := hmonicRaw.trans hrawNormalized
  constructor <;> rw [← HexPolyMathlib.toPolynomial_dvd_iff]
  · exact hmonicNormalized.dvd.trans
      (EuclideanDomain.gcd_dvd_left _ _)
  · exact hmonicNormalized.dvd.trans
      (EuclideanDomain.gcd_dvd_right _ _)

/-- The monic executable gcd interprets to a nonzero complex polynomial
whenever its first argument does. -/
theorem rawPolynomial_monicGcd_ne_zero
    (f g : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0) :
    Norm.rawPolynomial levels (Norm.monic (DensePoly.gcd f g)) ≠ 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (HexPolyMathlib.toPolynomial f).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) = 0
    rw [hzero, Polynomial.map_zero]
  let sourceGcd := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  have hsourceGcd : sourceGcd ≠ 0 := by
    intro hzero
    exact hfSource (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hrawSource : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd f g)) sourceGcd :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hraw : DensePoly.gcd f g ≠ 0 := by
    intro hzero
    apply hsourceGcd
    apply hrawSource.eq_zero_iff.mp
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hsourceNe := toPolynomial_monic_associated levels hvalid hinjective
    hinv (DensePoly.gcd f g) hraw |>.ne_zero_iff.mpr (by
      intro hzero
      apply hsourceGcd
      exact hrawSource.eq_zero_iff.mp hzero)
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change (HexPolyMathlib.toPolynomial
    (Norm.monic (DensePoly.gcd f g))).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) ≠ 0
  exact (Polynomial.map_ne_zero_iff
    (LevelSemantics.coeffHom levels hvalid hinjective hinv).injective).mpr
      hsourceNe

/-- The executable monic gcd tracks complex root multiplicities: at every
`z`, the interpretation of `Norm.monic (DensePoly.gcd f g)` has root
multiplicity the minimum of those of `f` and `g`. -/
theorem rootMultiplicity_monicGcd
    (f g : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0)
    (hg : Norm.rawPolynomial levels g ≠ 0) (z : ℂ) :
    (Norm.rawPolynomial levels
      (Norm.monic (DensePoly.gcd f g))).rootMultiplicity z =
      min ((Norm.rawPolynomial levels f).rootMultiplicity z)
        ((Norm.rawPolynomial levels g).rootMultiplicity z) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let sourceGcd := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  let targetGcd := EuclideanDomain.gcd
    (Norm.rawPolynomial levels f) (Norm.rawPolynomial levels g)
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    apply hf
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (HexPolyMathlib.toPolynomial f).map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) = 0
    rw [hzero, Polynomial.map_zero]
  have hsourceGcd : sourceGcd ≠ 0 := by
    intro hzero
    exact hfSource (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hrawSource : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd f g)) sourceGcd :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hraw : DensePoly.gcd f g ≠ 0 := by
    intro hzero
    apply hsourceGcd
    apply hrawSource.eq_zero_iff.mp
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hmonicSource : Associated
      (HexPolyMathlib.toPolynomial (Norm.monic (DensePoly.gcd f g)))
      sourceGcd :=
    (toPolynomial_monic_associated levels hvalid hinjective hinv
      (DensePoly.gcd f g) hraw).trans hrawSource
  let ι := LevelSemantics.coeffHom levels hvalid hinjective hinv
  have hmapped : Associated
      (Norm.rawPolynomial levels (Norm.monic (DensePoly.gcd f g)))
      (sourceGcd.map ι) := by
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change Associated
      ((HexPolyMathlib.toPolynomial
        (Norm.monic (DensePoly.gcd f g))).map ι)
      (sourceGcd.map ι)
    exact Polynomial.associated_map_map ι hmonicSource
  have hmapGcd : sourceGcd.map ι = targetGcd := by
    change (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial f)
      (HexPolyMathlib.toPolynomial g)).map ι =
      EuclideanDomain.gcd (Norm.rawPolynomial levels f)
        (Norm.rawPolynomial levels g)
    rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
      ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
    change (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial f)
      (HexPolyMathlib.toPolynomial g)).map ι =
      EuclideanDomain.gcd
        ((HexPolyMathlib.toPolynomial f).map ι)
        ((HexPolyMathlib.toPolynomial g).map ι)
    exact (Polynomial.gcd_map (p := HexPolyMathlib.toPolynomial f)
      (q := HexPolyMathlib.toPolynomial g) ι).symm
  calc
    (Norm.rawPolynomial levels
        (Norm.monic (DensePoly.gcd f g))).rootMultiplicity z =
        (sourceGcd.map ι).rootMultiplicity z :=
      rootMultiplicity_associated_complex hmapped z
    _ = targetGcd.rootMultiplicity z := by rw [hmapGcd]
    _ = min ((Norm.rawPolynomial levels f).rootMultiplicity z)
        ((Norm.rawPolynomial levels g).rootMultiplicity z) :=
      rootMultiplicity_gcd_complex _ _ hf hg z

/-- For an exact executable division the interpretations reconstruct the
dividend: interpreting `dividend / divisor` and multiplying by the
interpreted divisor recovers the interpreted dividend. -/
theorem rawPolynomial_div_mul
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend) :
    Norm.rawPolynomial levels (dividend / divisor) *
        Norm.rawPolynomial levels divisor =
      Norm.rawPolynomial levels dividend := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hmod : dividend % divisor = 0 :=
    DensePoly.mod_eq_zero_of_dvd dividend divisor hdivisor
  have hreconstruct := DensePoly.div_mul_add_mod dividend divisor
  rw [hmod] at hreconstruct
  have hsource := congrArg HexPolyMathlib.toPolynomial hreconstruct
  simp only [HexPolyMathlib.toPolynomial_add,
    HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_zero,
    add_zero] at hsource
  let ι := LevelSemantics.coeffHom levels hvalid hinjective hinv
  have hmapped := congrArg (Polynomial.map ι) hsource
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
    ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv,
    ← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change (HexPolyMathlib.toPolynomial (dividend / divisor)).map ι *
      (HexPolyMathlib.toPolynomial divisor).map ι =
    (HexPolyMathlib.toPolynomial dividend).map ι
  simpa only [Polynomial.map_mul] using hmapped

/-- An exact executable quotient of a semantically nonzero dividend is
semantically nonzero. -/
theorem rawPolynomial_div_ne_zero
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend)
    (hdividend : Norm.rawPolynomial levels dividend ≠ 0) :
    Norm.rawPolynomial levels (dividend / divisor) ≠ 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  intro hquotient
  have hreconstruct := rawPolynomial_div_mul hvalid hinjective hinv
    dividend divisor hdivisor
  rw [hquotient, zero_mul] at hreconstruct
  exact hdividend hreconstruct.symm

/-- Root multiplicities subtract across the monic exact quotient: at every
`z`, the multiplicity of `Norm.monic (dividend / divisor)` is the dividend's
multiplicity minus the divisor's. -/
theorem rootMultiplicity_monicDiv
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend)
    (hdividend : Norm.rawPolynomial levels dividend ≠ 0) (z : ℂ) :
    (Norm.rawPolynomial levels
      (Norm.monic (dividend / divisor))).rootMultiplicity z =
      (Norm.rawPolynomial levels dividend).rootMultiplicity z -
        (Norm.rawPolynomial levels divisor).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hquotient := rawPolynomial_div_ne_zero hvalid hinjective hinv
    dividend divisor hdivisor hdividend
  have hmonic := rawPolynomial_monic_associated hvalid hinjective hinv
    (dividend / divisor) hquotient
  rw [rootMultiplicity_associated_complex hmonic z]
  have hreconstruct := rawPolynomial_div_mul hvalid hinjective hinv
    dividend divisor hdivisor
  have hproduct : Norm.rawPolynomial levels (dividend / divisor) *
      Norm.rawPolynomial levels divisor ≠ 0 := by simpa [hreconstruct]
  have hmultiplicity := Polynomial.rootMultiplicity_mul (x := z) hproduct
  rw [hreconstruct] at hmultiplicity
  omega

/-- The monic normalisation of an exact quotient of a semantically nonzero
dividend is semantically nonzero. -/
theorem rawPolynomial_monicDiv_ne_zero
    (dividend divisor : DensePoly (Arithmetic.Coeff levels))
    (hdivisor : divisor ∣ dividend)
    (hdividend : Norm.rawPolynomial levels dividend ≠ 0) :
    Norm.rawPolynomial levels (Norm.monic (dividend / divisor)) ≠ 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hquotient := rawPolynomial_div_ne_zero hvalid hinjective hinv
    dividend divisor hdivisor hdividend
  exact (rawPolynomial_monic_associated hvalid hinjective hinv
    (dividend / divisor) hquotient).ne_zero_iff.mpr hquotient

/-- Loop invariant of Yun's algorithm tracked at one complex root `z` of
multiplicity `r` in the original input. Before emitting the component of
multiplicity `k`, the working polynomial `w` carries `z` simply exactly when
`k ≤ r`, and the repeated part carries the remaining multiplicity `r - k`. -/
structure YunInvariant (z : ℂ) (r k : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) : Prop where
  w_ne : Norm.rawPolynomial levels w ≠ 0
  repeated_ne : Norm.rawPolynomial levels repeated ≠ 0
  w_multiplicity : (Norm.rawPolynomial levels w).rootMultiplicity z =
    if k ≤ r then 1 else 0
  repeated_multiplicity :
    (Norm.rawPolynomial levels repeated).rootMultiplicity z = r - k

/-- One Yun iteration preserves the invariant: replacing `w` by the monic
gcd with the repeated part and dividing that gcd out of the repeated part
advances the multiplicity counter from `k` to `k + 1`. -/
theorem YunInvariant.step (z : ℂ) (r k : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (invariant : YunInvariant z r k w repeated) :
    let shared := Norm.monic (DensePoly.gcd w repeated)
    let nextRepeated := Norm.monic (repeated / shared)
    YunInvariant z r (k + 1) shared nextRepeated := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let shared := Norm.monic (DensePoly.gcd w repeated)
  let nextRepeated := Norm.monic (repeated / shared)
  have hwDense : w ≠ 0 := by
    intro hzero
    apply invariant.w_ne
    rw [hzero, Norm.rawPolynomial_zero]
  have hdivisors := monicGcd_dvd hvalid hinjective hinv w repeated hwDense
  have hsharedNe : Norm.rawPolynomial levels shared ≠ 0 :=
    rawPolynomial_monicGcd_ne_zero hvalid hinjective hinv
      w repeated invariant.w_ne
  have hnextNe : Norm.rawPolynomial levels nextRepeated ≠ 0 :=
    rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv
      repeated shared hdivisors.2 invariant.repeated_ne
  have hsharedMultiplicity :
      (Norm.rawPolynomial levels shared).rootMultiplicity z =
        min ((Norm.rawPolynomial levels w).rootMultiplicity z)
          ((Norm.rawPolynomial levels repeated).rootMultiplicity z) :=
    rootMultiplicity_monicGcd hvalid hinjective hinv w repeated
      invariant.w_ne invariant.repeated_ne z
  have hnextMultiplicity :
      (Norm.rawPolynomial levels nextRepeated).rootMultiplicity z =
        (Norm.rawPolynomial levels repeated).rootMultiplicity z -
          (Norm.rawPolynomial levels shared).rootMultiplicity z :=
    rootMultiplicity_monicDiv hvalid hinjective hinv repeated shared
      hdivisors.2 invariant.repeated_ne z
  refine ⟨hsharedNe, hnextNe, ?_, ?_⟩
  · rw [hsharedMultiplicity, invariant.w_multiplicity,
      invariant.repeated_multiplicity]
    by_cases hk : k ≤ r <;> by_cases hnext : k + 1 ≤ r <;>
      simp [hk, hnext] <;> omega
  · rw [hnextMultiplicity, invariant.repeated_multiplicity,
      hsharedMultiplicity, invariant.w_multiplicity,
      invariant.repeated_multiplicity]
    by_cases hk : k ≤ r <;> simp [hk] <;> omega

/-- The component emitted at counter `k` carries `z` as a simple root exactly
when `k` is the multiplicity of `z` in the original input, and avoids `z`
otherwise. -/
theorem YunInvariant.component (z : ℂ) (r k : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (invariant : YunInvariant z r k w repeated) :
    let shared := Norm.monic (DensePoly.gcd w repeated)
    let component := Norm.monic (w / shared)
    (Norm.rawPolynomial levels component).rootMultiplicity z =
      if k = r then 1 else 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let shared := Norm.monic (DensePoly.gcd w repeated)
  let component := Norm.monic (w / shared)
  have hwDense : w ≠ 0 := by
    intro hzero
    apply invariant.w_ne
    rw [hzero, Norm.rawPolynomial_zero]
  have hdivisors := monicGcd_dvd hvalid hinjective hinv w repeated hwDense
  change (Norm.rawPolynomial levels component).rootMultiplicity z =
    if k = r then 1 else 0
  rw [rootMultiplicity_monicDiv hvalid hinjective hinv w shared
      hdivisors.1 invariant.w_ne z,
    rootMultiplicity_monicGcd hvalid hinjective hinv w repeated
      invariant.w_ne invariant.repeated_ne z,
    invariant.w_multiplicity, invariant.repeated_multiplicity]
  by_cases hk : k ≤ r
  · by_cases heq : k = r
    · simp [heq]
    · simp [hk, heq]
      omega
  · have heq : k ≠ r := by omega
    simp [hk, heq]

/-- The Yun setup establishes the invariant at counter `1`: over a
characteristic-zero coefficient field, dividing the monic input by its gcd
with the derivative leaves each root exactly once, and the gcd retains the
remaining multiplicity. -/
theorem YunInvariant.init
    (f : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0)
    (hdegree : (Norm.rawPolynomial levels f).natDegree ≠ 0) (z : ℂ) :
    let normalized := Norm.monic f
    let repeated := Norm.monic
      (DensePoly.gcd normalized (Norm.derivative levels normalized))
    let distinct := Norm.monic (normalized / repeated)
    YunInvariant z
      ((Norm.rawPolynomial levels f).rootMultiplicity z) 1
      distinct repeated := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let normalized := Norm.monic f
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have hnormalizedAssoc := rawPolynomial_monic_associated hvalid
    hinjective hinv f hf
  have hnormalizedNe : Norm.rawPolynomial levels normalized ≠ 0 :=
    hnormalizedAssoc.ne_zero_iff.mpr hf
  have hnormalizedMultiplicity :
      (Norm.rawPolynomial levels normalized).rootMultiplicity z =
        (Norm.rawPolynomial levels f).rootMultiplicity z :=
    rootMultiplicity_associated_complex hnormalizedAssoc z
  have hnormalizedDegree :
      (Norm.rawPolynomial levels normalized).natDegree ≠ 0 := by
    have hdegreeEq := Polynomial.degree_eq_degree_of_associated
      hnormalizedAssoc
    have hnatDegreeEq := Polynomial.natDegree_eq_of_degree_eq hdegreeEq
    intro hzero
    apply hdegree
    rw [← hnatDegreeEq, hzero]
  have hderivativeNe : Norm.rawPolynomial levels
      (Norm.derivative levels normalized) ≠ 0 := by
    rw [Norm.rawPolynomial_derivative]
    exact Polynomial.derivative_ne_zero.mpr hnormalizedDegree
  have hrepeatedNe : Norm.rawPolynomial levels repeated ≠ 0 :=
    rawPolynomial_monicGcd_ne_zero hvalid hinjective hinv normalized
      (Norm.derivative levels normalized) hnormalizedNe
  have hnormalizedDense : normalized ≠ 0 := by
    intro hzero
    apply hnormalizedNe
    rw [hzero, Norm.rawPolynomial_zero]
  have hdivisor : repeated ∣ normalized :=
    (monicGcd_dvd hvalid hinjective hinv normalized
      (Norm.derivative levels normalized) hnormalizedDense).1
  have hdistinctNe : Norm.rawPolynomial levels distinct ≠ 0 :=
    rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv normalized
      repeated hdivisor hnormalizedNe
  have hrepeatedMultiplicity :
      (Norm.rawPolynomial levels repeated).rootMultiplicity z =
        (Norm.rawPolynomial levels f).rootMultiplicity z - 1 := by
    rw [rootMultiplicity_monicGcd hvalid hinjective hinv normalized
        (Norm.derivative levels normalized) hnormalizedNe hderivativeNe z,
      Norm.rawPolynomial_derivative, hnormalizedMultiplicity]
    by_cases hroot :
        (Norm.rawPolynomial levels f).rootMultiplicity z = 0
    · simp [hroot]
    · have hpositive : 0 <
          (Norm.rawPolynomial levels normalized).rootMultiplicity z := by
        omega
      have hisRoot : (Norm.rawPolynomial levels normalized).IsRoot z :=
        (Polynomial.rootMultiplicity_pos hnormalizedNe).mp hpositive
      rw [Polynomial.derivative_rootMultiplicity_of_root hisRoot,
        hnormalizedMultiplicity]
      omega
  refine ⟨hdistinctNe, hrepeatedNe, ?_, hrepeatedMultiplicity⟩
  rw [rootMultiplicity_monicDiv hvalid hinjective hinv normalized repeated
      hdivisor hnormalizedNe z,
    hnormalizedMultiplicity, hrepeatedMultiplicity]
  by_cases hpositive : 1 ≤
      (Norm.rawPolynomial levels f).rootMultiplicity z <;>
    simp [hpositive] <;> omega

/-- A nonzero interpreted polynomial with a root has positive executable
degree. Keeping this transport separate prevents the recursive Yun proof from
re-elaborating the coefficient-field construction at every induction step. -/
theorem natDegree_rawPolynomial
    (f : DensePoly (Arithmetic.Coeff levels)) :
    (Norm.rawPolynomial levels f).natDegree = f.degree?.getD 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  change ((HexPolyMathlib.toPolynomial f).map
    (LevelSemantics.coeffHom levels hvalid hinjective hinv)).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective
      (LevelSemantics.coeffHom levels hvalid hinjective hinv).injective,
    HexPolyMathlib.natDegree_toPolynomial]

/-- The raw complex interpretation is coefficientwise mapping through the
coefficient denotation homomorphism. -/
theorem rawPolynomial_eq_map
    (f : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Norm.rawPolynomial levels f =
      (HexPolyMathlib.toPolynomial f).map
        (LevelSemantics.coeffHom levels hvalid hinjective hinv) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  rw [← Norm.rawPolynomialHom_apply levels hvalid hinjective hinv]
  rfl

/-- A semantically nonzero executable polynomial with a complex root has
positive executable degree. -/
theorem degree_pos_of_rawPolynomial_root
    (f : DensePoly (Arithmetic.Coeff levels))
    (hf : Norm.rawPolynomial levels f ≠ 0) {z : ℂ}
    (hroot : (Norm.rawPolynomial levels f).IsRoot z) :
    0 < f.degree?.getD 0 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hdegree := Polynomial.degree_pos_of_root hf hroot
  have hnatDegree : 0 < (Norm.rawPolynomial levels f).natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr hdegree
  rw [natDegree_rawPolynomial hvalid hinjective hinv] at hnatDegree
  exact hnatDegree

/-- Entries already accumulated survive the rest of the Yun loop: the
accumulator only grows. -/
theorem mem_yunAux_of_mem
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat)) {entry}
    (hentry : entry ∈ out.toList) :
    entry ∈ (Factor.yunAux levels w repeated k fuel out).toList := by
  induction fuel generalizing w repeated k out with
  | zero => simpa [Factor.yunAux] using hentry
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hentry
      · dsimp only
        split
        · apply ih
          rw [Array.toList_push, List.mem_append]
          exact Or.inl hentry
        · exact ih _ _ _ _ hentry

/-- Soundness of the Yun loop at one root: assuming the invariant, every
emitted component that vanishes at `z` is labelled with exactly the
multiplicity `r` of `z` in the original input. -/
theorem yunAux_sound (z : ℂ) (r : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat))
    (invariant : YunInvariant z r k w repeated)
    (hOut : ∀ entry ∈ out.toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z → entry.2 = r) :
    ∀ entry ∈ (Factor.yunAux levels w repeated k fuel out).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z → entry.2 = r := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated k out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        let shared := Norm.monic (DensePoly.gcd w repeated)
        let component := Norm.monic (w / shared)
        let nextRepeated := Norm.monic (repeated / shared)
        have hwDense : w ≠ 0 := by
          intro hzero
          apply invariant.w_ne
          rw [hzero, Norm.rawPolynomial_zero]
        have hdivisors := monicGcd_dvd hvalid hinjective hinv
          w repeated hwDense
        have hcomponentNe : Norm.rawPolynomial levels component ≠ 0 :=
          rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv
            w shared hdivisors.1 invariant.w_ne
        have hcomponentMultiplicity :
            (Norm.rawPolynomial levels component).rootMultiplicity z =
              if k = r then 1 else 0 :=
          invariant.component hvalid hinjective hinv z r k w repeated
        have hcomponentSound :
            (Norm.rawPolynomial levels component).IsRoot z → k = r := by
          intro hroot
          have hpositive :=
            (Polynomial.rootMultiplicity_pos hcomponentNe).mpr hroot
          rw [hcomponentMultiplicity] at hpositive
          by_cases heq : k = r
          · exact heq
          · simp [heq] at hpositive
        have hnextInvariant : YunInvariant z r (k + 1)
            shared nextRepeated :=
          invariant.step hvalid hinjective hinv z r k w repeated
        split
        · apply ih shared nextRepeated (k + 1) _ hnextInvariant
          intro entry hentry
          rw [Array.toList_push, List.mem_append,
            List.mem_singleton] at hentry
          rcases hentry with hentry | rfl
          · exact hOut entry hentry
          · rw [rawPoly_polyCoords]
            intro hroot
            exact hcomponentSound hroot
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant hOut

/-- Squarefreeness of the emitted components: assuming the invariant, every
component produced by the Yun loop carries `z` with multiplicity at most
one. -/
theorem yunAux_rootMultiplicity_le_one (z : ℂ) (r : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat))
    (invariant : YunInvariant z r k w repeated)
    (hOut : ∀ entry ∈ out.toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).rootMultiplicity z ≤ 1) :
    ∀ entry ∈ (Factor.yunAux levels w repeated k fuel out).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).rootMultiplicity z ≤ 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated k out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        let shared := Norm.monic (DensePoly.gcd w repeated)
        let component := Norm.monic (w / shared)
        let nextRepeated := Norm.monic (repeated / shared)
        have hcomponentMultiplicity :
            (Norm.rawPolynomial levels component).rootMultiplicity z =
              if k = r then 1 else 0 :=
          invariant.component hvalid hinjective hinv z r k w repeated
        have hnextInvariant : YunInvariant z r (k + 1)
            shared nextRepeated :=
          invariant.step hvalid hinjective hinv z r k w repeated
        split
        · apply ih shared nextRepeated (k + 1) _ hnextInvariant
          intro entry hentry
          rw [Array.toList_push, List.mem_append,
            List.mem_singleton] at hentry
          rcases hentry with hentry | rfl
          · exact hOut entry hentry
          · rw [rawPoly_polyCoords, hcomponentMultiplicity]
            split <;> omega
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant hOut

set_option maxHeartbeats 1200000 in
/-- Completeness of the Yun loop at one root: with enough fuel, some emitted
component vanishes at `z` and is labelled with its multiplicity `r`. -/
theorem yunAux_complete (z : ℂ) (r : Nat)
    (w repeated : DensePoly (Arithmetic.Coeff levels)) (k fuel : Nat)
    (out : Array (Array (Array Rat) × Nat))
    (invariant : YunInvariant z r k w repeated)
    (hindex : k ≤ r) (hfuel : r < k + fuel) :
    ∃ entry ∈ (Factor.yunAux levels w repeated k fuel out).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z ∧ entry.2 = r := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated k out with
  | zero => omega
  | succ fuel ih =>
      have hnotOne : w ≠ 1 := by
        intro hone
        have hmultiplicity := invariant.w_multiplicity
        rw [hone, Norm.rawPolynomial_one levels hvalid hinjective hinv,
          ite_eq_left hindex] at hmultiplicity
        have honeMultiplicity :
            Polynomial.rootMultiplicity z (1 : Polynomial ℂ) = 0 := by
          simpa only [Polynomial.C_1] using
            Polynomial.rootMultiplicity_C (1 : ℂ) z
        omega
      rw [Factor.yunAux, ite_eq_right hnotOne]
      dsimp only
      let shared := Norm.monic (DensePoly.gcd w repeated)
      let component := Norm.monic (w / shared)
      let nextRepeated := Norm.monic (repeated / shared)
      have hwDense : w ≠ 0 := by
        intro hzero
        apply invariant.w_ne
        rw [hzero, Norm.rawPolynomial_zero]
      have hdivisors := monicGcd_dvd hvalid hinjective hinv
        w repeated hwDense
      have hcomponentNe : Norm.rawPolynomial levels component ≠ 0 :=
        rawPolynomial_monicDiv_ne_zero hvalid hinjective hinv
          w shared hdivisors.1 invariant.w_ne
      have hcomponentMultiplicity :
          (Norm.rawPolynomial levels component).rootMultiplicity z =
            if k = r then 1 else 0 :=
        invariant.component hvalid hinjective hinv z r k w repeated
      by_cases heq : k = r
      · have hpositive : 0 <
            (Norm.rawPolynomial levels component).rootMultiplicity z := by
          rw [hcomponentMultiplicity]
          simp [heq]
        have hroot : (Norm.rawPolynomial levels component).IsRoot z :=
          (Polynomial.rootMultiplicity_pos hcomponentNe).mp hpositive
        have hdegree : 0 < component.degree?.getD 0 :=
          degree_pos_of_rawPolynomial_root hvalid hinjective hinv component
            hcomponentNe hroot
        rw [ite_eq_left hdegree]
        refine ⟨(Factor.polyCoords component, k), ?_, ?_, heq⟩
        · apply mem_yunAux_of_mem hvalid hinjective hinv
          simp [component, shared]
        · rw [rawPoly_polyCoords]
          exact hroot
      · have hnextInvariant : YunInvariant z r (k + 1)
            shared nextRepeated :=
          invariant.step hvalid hinjective hinv z r k w repeated
        have hnextIndex : k + 1 ≤ r := by omega
        have hnextFuel : r < k + 1 + fuel := by omega
        split
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant
            hnextIndex hnextFuel
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant
            hnextIndex hnextFuel

/-- The Yun loop only emits nonconstant components with positive
multiplicity labels. -/
theorem yunAux_positive
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (multiplicity fuel : Nat) (out : Array (Array (Array Rat) × Nat))
    (hMultiplicity : 0 < multiplicity)
    (hOut : ∀ component ∈ out.toList,
      0 < (Factor.rawPoly levels component.1).degree?.getD 0 ∧
        0 < component.2) :
    ∀ component ∈
      (Factor.yunAux levels w repeated multiplicity fuel out).toList,
      0 < (Factor.rawPoly levels component.1).degree?.getD 0 ∧
        0 < component.2 := by
  induction fuel generalizing w repeated multiplicity out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        split
        · apply ih
          · omega
          · intro component hcomponent
            rw [Array.toList_push, List.mem_append,
              List.mem_singleton] at hcomponent
            rcases hcomponent with hcomponent | rfl
            · exact hOut component hcomponent
            · rw [rawPoly_polyCoords]
              exact ⟨by assumption, hMultiplicity⟩
        · apply ih
          · omega
          · exact hOut

omit hvalid hinjective hinv in
/-- Multiplicity labels emitted by the Yun loop are strictly increasing and
bounded by the starting counter plus the remaining fuel. -/
theorem yunAux_multiplicities
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (multiplicity fuel : Nat) (out : Array (Array (Array Rat) × Nat))
    (hpairwise : out.toList.Pairwise fun a b => a.2 < b.2)
    (hOut : ∀ entry ∈ out.toList, entry.2 < multiplicity) :
    ((Factor.yunAux levels w repeated multiplicity fuel out).toList.Pairwise
        fun a b => a.2 < b.2) ∧
      ∀ entry ∈
        (Factor.yunAux levels w repeated multiplicity fuel out).toList,
        entry.2 < multiplicity + fuel := by
  induction fuel generalizing w repeated multiplicity out with
  | zero =>
      refine ⟨by simpa [Factor.yunAux] using hpairwise, ?_⟩
      simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact ⟨hpairwise, fun entry hentry => by
          have := hOut entry hentry
          omega⟩
      · dsimp only
        split
        · have hresult := ih
            (Norm.monic (DensePoly.gcd w repeated))
            (Norm.monic (repeated /
              Norm.monic (DensePoly.gcd w repeated)))
            (multiplicity + 1)
            (out.push (Factor.polyCoords
              (Norm.monic (w / Norm.monic (DensePoly.gcd w repeated))),
              multiplicity)) (by
            rw [Array.toList_push, List.pairwise_append]
            refine ⟨hpairwise, by simp, ?_⟩
            intro a ha b hb
            have hb' : b = (Factor.polyCoords
                (Norm.monic (w / Norm.monic (DensePoly.gcd w repeated))),
                multiplicity) := by
              simpa only [List.mem_singleton] using hb
            rw [hb']
            exact hOut a ha) (by
            intro entry hentry
            rw [Array.toList_push, List.mem_append,
              List.mem_singleton] at hentry
            rcases hentry with hentry | rfl
            · have := hOut entry hentry
              omega
            · omega)
          refine ⟨hresult.1, ?_⟩
          intro entry hentry
          have := hresult.2 entry hentry
          omega
        · have hresult := ih
            (Norm.monic (DensePoly.gcd w repeated))
            (Norm.monic (repeated /
              Norm.monic (DensePoly.gcd w repeated)))
            (multiplicity + 1) out hpairwise (by
            intro entry hentry
            have := hOut entry hentry
            omega)
          refine ⟨hresult.1, ?_⟩
          intro entry hentry
          have := hresult.2 entry hentry
          omega

/-- Every component emitted by the Yun loop is monic in the executable
sense: its raw leading coefficient is `1`. -/
theorem yunAux_monic
    (w repeated : DensePoly (Arithmetic.Coeff levels))
    (multiplicity fuel : Nat) (out : Array (Array (Array Rat) × Nat))
    (hOut : ∀ entry ∈ out.toList,
      (Factor.rawPoly levels entry.1).leadingCoeff = 1) :
    ∀ entry ∈
      (Factor.yunAux levels w repeated multiplicity fuel out).toList,
      (Factor.rawPoly levels entry.1).leadingCoeff = 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction fuel generalizing w repeated multiplicity out with
  | zero => simpa [Factor.yunAux] using hOut
  | succ fuel ih =>
      rw [Factor.yunAux]
      split
      · exact hOut
      · dsimp only
        let shared := Norm.monic (DensePoly.gcd w repeated)
        let component := Norm.monic (w / shared)
        split
        · rename_i hdegree
          apply ih
          intro entry hentry
          rw [Array.toList_push, List.mem_append,
            List.mem_singleton] at hentry
          rcases hentry with hentry | rfl
          · exact hOut entry hentry
          · rw [rawPoly_polyCoords]
            have hcomponentNe : component ≠ 0 := by
              intro hzero
              have hdegreeZero : component.degree?.getD 0 = 0 := by
                rw [hzero]
                simp
              have hdegreeComponent : 0 < component.degree?.getD 0 := by
                simpa [component, shared] using hdegree
              omega
            have hquotientNe : w / shared ≠ 0 := by
              intro hzero
              apply hcomponentNe
              simp [component, hzero, Norm.monic]
            rw [← HexPolyMathlib.leadingCoeff_toPolynomial]
            exact (toPolynomial_monic_monic levels hvalid hinjective hinv
              (w / shared) hquotientNe).leadingCoeff
        · exact ih _ _ _ _ hOut

omit hvalid hinjective hinv in
/-- The multiplicity of any single root of a nonzero complex polynomial is
bounded by its degree. -/
theorem rootMultiplicity_le_natDegree_complex
    (f : Polynomial ℂ) (hf : f ≠ 0) (z : ℂ) :
    f.rootMultiplicity z ≤ f.natDegree := by
  have hdegree := Polynomial.natDegree_le_of_dvd
    (Polynomial.pow_rootMultiplicity_dvd f z) hf
  simpa using hdegree

/-- Every root of an emitted tower Yun component is a root of the input with
the component's stored multiplicity. -/
theorem yun_sound
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (z : ℂ) (entry : Array (Array Rat) × Nat)
    (hentry : entry ∈ (Factor.yunRaw levels f).toList)
    (hroot : (Norm.rawPolynomial levels
      (Factor.rawPoly levels entry.1)).IsRoot z) :
    entry.2 = (Norm.rawPolynomial levels
      (Factor.rawPoly levels f)).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hnatDegree : (Norm.rawPolynomial levels p).natDegree ≠ 0 := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    omega
  have hpNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hnatDegree
    exact hnatDegree rfl
  let normalized := Norm.monic p
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have invariant : YunInvariant z
      ((Norm.rawPolynomial levels p).rootMultiplicity z) 1
      distinct repeated :=
    YunInvariant.init hvalid hinjective hinv p hpNe hnatDegree z
  unfold Factor.yunRaw at hentry
  rw [ite_eq_right (by omega : p.degree?.getD 0 ≠ 0)] at hentry
  exact yunAux_sound hvalid hinjective hinv z
    ((Norm.rawPolynomial levels p).rootMultiplicity z)
    distinct repeated 1 (p.size + 1) #[] invariant (by simp)
    entry hentry hroot

/-- Every root of a positive-degree tower polynomial occurs in an emitted Yun
component at its exact multiplicity. -/
theorem yun_complete
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (z : ℂ)
    (hroot : (Norm.rawPolynomial levels
      (Factor.rawPoly levels f)).IsRoot z) :
    ∃ entry ∈ (Factor.yunRaw levels f).toList,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).IsRoot z ∧
      entry.2 = (Norm.rawPolynomial levels
        (Factor.rawPoly levels f)).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hnatDegree : (Norm.rawPolynomial levels p).natDegree ≠ 0 := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    omega
  have hpNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hnatDegree
    exact hnatDegree rfl
  let r := (Norm.rawPolynomial levels p).rootMultiplicity z
  have hindex : 1 ≤ r :=
    (Polynomial.rootMultiplicity_pos hpNe).mpr hroot
  have hmultiplicityDegree : r ≤
      (Norm.rawPolynomial levels p).natDegree :=
    rootMultiplicity_le_natDegree_complex _ hpNe z
  have hsize : 0 < p.size := by
    by_contra hzero
    have hsizeZero : p.size = 0 := by omega
    have hpZero : p = 0 := (DensePoly.size_eq_zero_iff p).mp hsizeZero
    rw [hpZero] at hdegreeP
    simp at hdegreeP
  have hdenseDegree : p.degree?.getD 0 = p.size - 1 := by
    rw [DensePoly.degree?_eq_some_of_pos_size p hsize]
    rfl
  have hdegreeEq : (Norm.rawPolynomial levels p).natDegree =
      p.degree?.getD 0 :=
    natDegree_rawPolynomial hvalid hinjective hinv p
  have hfuel : r < 1 + (p.size + 1) := by omega
  let normalized := Norm.monic p
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have invariant : YunInvariant z r 1 distinct repeated :=
    YunInvariant.init hvalid hinjective hinv p hpNe hnatDegree z
  have hcomplete := yunAux_complete hvalid hinjective hinv z r
    distinct repeated 1 (p.size + 1) #[] invariant hindex hfuel
  unfold Factor.yunRaw
  rw [ite_eq_right (by omega : p.degree?.getD 0 ≠ 0)]
  exact hcomplete

/-- Every emitted Yun component has only simple roots over `ℂ`. -/
theorem yun_rootMultiplicity_le_one
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (entry : Array (Array Rat) × Nat)
    (hentry : entry ∈ (Factor.yunRaw levels f).toList) (z : ℂ) :
    (Norm.rawPolynomial levels
      (Factor.rawPoly levels entry.1)).rootMultiplicity z ≤ 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hnatDegree : (Norm.rawPolynomial levels p).natDegree ≠ 0 := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    omega
  have hpNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hnatDegree
    exact hnatDegree rfl
  let r := (Norm.rawPolynomial levels p).rootMultiplicity z
  let normalized := Norm.monic p
  let repeated := Norm.monic
    (DensePoly.gcd normalized (Norm.derivative levels normalized))
  let distinct := Norm.monic (normalized / repeated)
  have invariant : YunInvariant z r 1 distinct repeated :=
    YunInvariant.init hvalid hinjective hinv p hpNe hnatDegree z
  unfold Factor.yunRaw at hentry
  rw [ite_eq_right (by omega : p.degree?.getD 0 ≠ 0)] at hentry
  exact yunAux_rootMultiplicity_le_one hvalid hinjective hinv z r
    distinct repeated 1 (p.size + 1) #[] invariant (by simp)
    entry hentry

/-- Every emitted tower Yun component has positive degree and positive stored
multiplicity. -/
theorem yun_positive
    (f : Array (Array Rat)) (component : Array (Array Rat) × Nat)
    (hcomponent : component ∈ (Factor.yunRaw levels f).toList) :
    0 < (Factor.rawPoly levels component.1).degree?.getD 0 ∧
      0 < component.2 := by
  simp only [Factor.yunRaw] at hcomponent
  split at hcomponent
  · simp at hcomponent
  · exact yunAux_positive hvalid hinjective hinv _ _ 1
      ((Factor.rawPoly levels f).size + 1) #[] Nat.one_pos
      (by simp) component hcomponent

/-- Yun emits components in strictly increasing multiplicity order. -/
theorem yun_multiplicities
    (f : Array (Array Rat)) :
    (Factor.yunRaw levels f).toList.Pairwise fun a b => a.2 < b.2 := by
  simp only [Factor.yunRaw]
  split
  · simp
  · exact (yunAux_multiplicities
      (levels := levels) _ _ 1 ((Factor.rawPoly levels f).size + 1) #[]
      (by simp) (by simp)).1

/-- Every tower Yun component is monic in executable coordinates. -/
theorem yun_monic
    (f : Array (Array Rat)) (component : Array (Array Rat) × Nat)
    (hcomponent : component ∈ (Factor.yunRaw levels f).toList) :
    (Factor.rawPoly levels component.1).leadingCoeff = 1 := by
  simp only [Factor.yunRaw] at hcomponent
  split at hcomponent
  · simp at hcomponent
  · exact yunAux_monic hvalid hinjective hinv _ _ 1
      ((Factor.rawPoly levels f).size + 1) #[] (by simp)
      component hcomponent

/-- Every tower Yun component passes the executable squarefreeness test. -/
theorem yun_squarefree
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (component : Array (Array Rat) × Nat)
    (hcomponent : component ∈ (Factor.yunRaw levels f).toList) :
    Norm.isSquarefree levels component.1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let P := Norm.rawPolynomial levels
    (Factor.rawPoly levels component.1)
  have hcomponentDegree :=
    (yun_positive hvalid hinjective hinv f component hcomponent).1
  have hPNe : P ≠ 0 := by
    intro hzero
    have hnatDegree : P.natDegree = 0 := by simp [hzero]
    have htransport := natDegree_rawPolynomial hvalid hinjective hinv
      (Factor.rawPoly levels component.1)
    rw [← htransport] at hcomponentDegree
    exact (Nat.ne_of_gt hcomponentDegree) hnatDegree
  have hnodup : P.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [Polynomial.count_roots]
    exact yun_rootMultiplicity_le_one hvalid hinjective hinv f hdegree
      component hcomponent z
  have hseparable : P.Separable :=
    (Polynomial.nodup_roots_iff_of_splits hPNe
      (IsAlgClosed.splits P)).mp hnodup
  exact (Norm.isSquarefree_iff levels hvalid hinjective hinv
    component.1).mpr hseparable.squarefree

/-- Distinct tower Yun components pass the executable coprimality test. -/
theorem yun_coprime
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0)
    (a b : Array (Array Rat) × Nat)
    (ha : a ∈ (Factor.yunRaw levels f).toList)
    (hb : b ∈ (Factor.yunRaw levels f).toList)
    (hmultiplicity : a.2 < b.2) :
    (DensePoly.gcd (Factor.rawPoly levels a.1)
      (Factor.rawPoly levels b.1)).size ≤ 1 := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let pa := Factor.rawPoly levels a.1
  let pb := Factor.rawPoly levels b.1
  let g := DensePoly.gcd pa pb
  by_contra hsize
  have hsizeG : ¬g.size ≤ 1 := hsize
  have hsize' : 1 < g.size := by omega
  have hgSize : 0 < g.size := by omega
  have hgDegree : 0 < g.degree?.getD 0 := by
    rw [DensePoly.degree?_eq_some_of_pos_size g hgSize]
    simp only [Option.getD_some]
    omega
  have htargetDegree : 0 < (Norm.rawPolynomial levels g).natDegree := by
    rw [natDegree_rawPolynomial hvalid hinjective hinv]
    exact hgDegree
  have hdegreeComplex : 0 < (Norm.rawPolynomial levels g).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp htargetDegree
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Norm.rawPolynomial levels g) (ne_of_gt hdegreeComplex)
  have hgAssociated : Associated (HexPolyMathlib.toPolynomial g)
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial pa)
        (HexPolyMathlib.toPolynomial pb)) :=
    HexPolyMathlib.toPolynomial_gcd_associated pa pb
  have hgDvdA : HexPolyMathlib.toPolynomial g ∣
      HexPolyMathlib.toPolynomial pa :=
    hgAssociated.dvd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hgDvdB : HexPolyMathlib.toPolynomial g ∣
      HexPolyMathlib.toPolynomial pb :=
    hgAssociated.dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have htargetDvdA : Norm.rawPolynomial levels g ∣
      Norm.rawPolynomial levels pa := by
    rw [rawPolynomial_eq_map hvalid hinjective hinv,
      rawPolynomial_eq_map hvalid hinjective hinv]
    exact Polynomial.map_dvd
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) hgDvdA
  have htargetDvdB : Norm.rawPolynomial levels g ∣
      Norm.rawPolynomial levels pb := by
    rw [rawPolynomial_eq_map hvalid hinjective hinv,
      rawPolynomial_eq_map hvalid hinjective hinv]
    exact Polynomial.map_dvd
      (LevelSemantics.coeffHom levels hvalid hinjective hinv) hgDvdB
  have hrootA : (Norm.rawPolynomial levels pa).IsRoot z :=
    hz.dvd htargetDvdA
  have hrootB : (Norm.rawPolynomial levels pb).IsRoot z :=
    hz.dvd htargetDvdB
  have haMultiplicity := yun_sound hvalid hinjective hinv f hdegree
    z a ha hrootA
  have hbMultiplicity := yun_sound hvalid hinjective hinv f hdegree
    z b hb hrootB
  omega

omit hvalid hinjective hinv in
/-- Root multiplicities scale linearly under powers of a nonzero complex
polynomial. -/
theorem rootMultiplicity_pow_complex
    (P : Polynomial ℂ) (hP : P ≠ 0) (n : Nat) (z : ℂ) :
    (P ^ n).rootMultiplicity z = n * P.rootMultiplicity z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (_root_.pow_ne_zero n hP) hP), ih]
      simp [Nat.succ_mul]

omit hvalid hinjective hinv in
/-- Root multiplicities add across a product of nonzero complex
polynomials. -/
theorem rootMultiplicity_list_prod_complex
    (polys : List (Polynomial ℂ))
    (hnonzero : ∀ P ∈ polys, P ≠ 0) (z : ℂ) :
    polys.prod.rootMultiplicity z =
      (polys.map fun P => P.rootMultiplicity z).sum := by
  induction polys with
  | nil => simp
  | cons P polys ih =>
      have hP : P ≠ 0 := hnonzero P (by simp)
      have htail : ∀ Q ∈ polys, Q ≠ 0 := by
        intro Q hQ
        exact hnonzero Q (by simp [hQ])
      have htailProd : polys.prod ≠ 0 :=
        List.prod_ne_zero (by
          intro hzeroMem
          exact htail 0 hzeroMem rfl)
      rw [List.prod_cons, Polynomial.rootMultiplicity_mul
        (mul_ne_zero hP htailProd), ih htail]
      simp

/-- Semantic interpretation turns the executable power `Factor.polyPow` into
the complex polynomial power. -/
theorem rawPolynomial_polyPow
    (f : DensePoly (Arithmetic.Coeff levels)) (n : Nat) :
    Norm.rawPolynomial levels (Factor.polyPow f n) =
      Norm.rawPolynomial levels f ^ n := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Factor.polyPow, Norm.rawPolynomial_one levels hvalid
          hinjective hinv]
      · rw [Factor.polyPow, ite_eq_right hn]
        have hhalf : n / 2 < n :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        dsimp only
        by_cases heven : n % 2 = 0
        · rw [ite_eq_left heven,
            Norm.rawPolynomial_mul levels hvalid hinjective hinv,
            ih (n / 2) hhalf]
          rw [← pow_add]
          congr 1
          omega
        · rw [ite_eq_right heven,
            Norm.rawPolynomial_mul levels hvalid hinjective hinv,
            Norm.rawPolynomial_mul levels hvalid hinjective hinv,
            ih (n / 2) hhalf]
          rw [← pow_add, ← pow_succ]
          congr 1
          omega

/-- The executable fold multiplying labelled component powers interprets to
the product of interpreted component powers times the accumulator. -/
theorem rawPolynomial_yunFold
    (components : List (Array (Array Rat) × Nat))
    (acc : DensePoly (Arithmetic.Coeff levels)) :
    Norm.rawPolynomial levels
        (components.foldl (fun product component =>
          product * Factor.polyPow
            (Factor.rawPoly levels component.1) component.2) acc) =
      (components.map fun component =>
        Norm.rawPolynomial levels
          (Factor.rawPoly levels component.1) ^ component.2).prod *
        Norm.rawPolynomial levels acc := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction components generalizing acc with
  | nil => simp
  | cons component components ih =>
      rw [List.foldl_cons, ih,
        Norm.rawPolynomial_mul levels hvalid hinjective hinv,
        rawPolynomial_polyPow hvalid hinjective hinv]
      simp only [List.map_cons, List.prod_cons]
      ring

/-- Multiplicity bookkeeping for the weighted Yun product: at every root `z`
of the input, the labels of the (squarefree, strictly ordered, jointly
complete) components weighted by their own multiplicities at `z` sum to the
input's multiplicity at `z`. -/
theorem yunMultiplicity_sum
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0) (z : ℂ)
    (components : List (Array (Array Rat) × Nat))
    (hcomponents : ∀ entry ∈ components,
      entry ∈ (Factor.yunRaw levels f).toList)
    (hpairwise : components.Pairwise fun a b => a.2 < b.2)
    (hcomplete :
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels f)).IsRoot z →
      ∃ entry ∈ components,
        (Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1)).IsRoot z) :
    (components.map fun entry => entry.2 *
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).rootMultiplicity z).sum =
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels f)).rootMultiplicity z := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let input := Norm.rawPolynomial levels (Factor.rawPoly levels f)
  have hinputNe : input ≠ 0 := by
    intro hzero
    have hnat : input.natDegree = 0 := by simp [hzero]
    have htransport := natDegree_rawPolynomial hvalid hinjective hinv
      (Factor.rawPoly levels f)
    rw [← htransport] at hdegree
    exact (Nat.ne_of_gt hdegree) hnat
  induction components with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      by_contra hr
      have hr' : input.rootMultiplicity z ≠ 0 := by
        intro hzero
        apply hr
        change 0 = input.rootMultiplicity z
        exact hzero.symm
      have hrPositive : 0 < input.rootMultiplicity z :=
        Nat.pos_of_ne_zero hr'
      have hroot : input.IsRoot z :=
        (Polynomial.rootMultiplicity_pos hinputNe).mp hrPositive
      rcases hcomplete hroot with ⟨entry, hentry, _⟩
      simp at hentry
  | cons entry components ih =>
      have hentryMem : entry ∈ (Factor.yunRaw levels f).toList :=
        hcomponents entry (by simp)
      have htailMem : ∀ tail ∈ components,
          tail ∈ (Factor.yunRaw levels f).toList := by
        intro tail htail
        exact hcomponents tail (by simp [htail])
      have hentryDegree :=
        (yun_positive hvalid hinjective hinv f entry hentryMem).1
      have hentryNe : Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1) ≠ 0 := by
        intro hzero
        have hnat : (Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1)).natDegree = 0 := by simp [hzero]
        rw [← natDegree_rawPolynomial hvalid hinjective hinv] at hentryDegree
        exact (Nat.ne_of_gt hentryDegree) hnat
      have hsimple := yun_rootMultiplicity_le_one hvalid hinjective hinv
        f hdegree entry hentryMem z
      rw [List.pairwise_cons] at hpairwise
      by_cases hzero : (Norm.rawPolynomial levels
          (Factor.rawPoly levels entry.1)).rootMultiplicity z = 0
      · simp only [List.map_cons, hzero, mul_zero, List.sum_cons, zero_add]
        apply ih htailMem hpairwise.2
        intro hroot
        rcases hcomplete hroot with ⟨witness, hwitness, hwitnessRoot⟩
        rw [List.mem_cons] at hwitness
        rcases hwitness with rfl | hwitness
        · have hpositive :=
            (Polynomial.rootMultiplicity_pos hentryNe).mpr hwitnessRoot
          omega
        · exact ⟨witness, hwitness, hwitnessRoot⟩
      · have hpositive : 0 < (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).rootMultiplicity z :=
          Nat.pos_of_ne_zero hzero
        have hroot : (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).IsRoot z :=
          (Polynomial.rootMultiplicity_pos hentryNe).mp hpositive
        have hlabel := yun_sound hvalid hinjective hinv f hdegree z
          entry hentryMem hroot
        have hmultiplicity : (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).rootMultiplicity z = 1 := by
          omega
        have htailZero : (components.map fun tail => tail.2 *
            (Norm.rawPolynomial levels
              (Factor.rawPoly levels tail.1)).rootMultiplicity z).sum = 0 := by
          rw [List.sum_eq_zero_iff_forall_eq_nat]
          intro value hvalue
          simp only [List.mem_map] at hvalue
          obtain ⟨tail, htail, rfl⟩ := hvalue
          by_cases htailZero : (Norm.rawPolynomial levels
              (Factor.rawPoly levels tail.1)).rootMultiplicity z = 0
          · simp [htailZero]
          · have htailEntry := htailMem tail htail
            have htailDegree :=
              (yun_positive hvalid hinjective hinv f tail htailEntry).1
            have htailNe : Norm.rawPolynomial levels
                (Factor.rawPoly levels tail.1) ≠ 0 := by
              intro hzeroPoly
              have hnat : (Norm.rawPolynomial levels
                (Factor.rawPoly levels tail.1)).natDegree = 0 := by
                simp [hzeroPoly]
              rw [← natDegree_rawPolynomial hvalid hinjective hinv]
                at htailDegree
              exact (Nat.ne_of_gt htailDegree) hnat
            have htailRoot : (Norm.rawPolynomial levels
                (Factor.rawPoly levels tail.1)).IsRoot z :=
              (Polynomial.rootMultiplicity_pos htailNe).mp
                (Nat.pos_of_ne_zero htailZero)
            have htailLabel := yun_sound hvalid hinjective hinv f hdegree z
              tail htailEntry htailRoot
            have hlt := hpairwise.1 tail htail
            omega
        simp only [List.map_cons, List.sum_cons, hmultiplicity, mul_one,
          htailZero, add_zero, hlabel]

/-- Every component emitted by `Factor.yunRaw` interprets to a monic complex
polynomial. -/
theorem yun_rawPolynomial_monic
    (f : Array (Array Rat))
    (entry : Array (Array Rat) × Nat)
    (hentry : entry ∈ (Factor.yunRaw levels f).toList) :
    (Norm.rawPolynomial levels
      (Factor.rawPoly levels entry.1)).Monic := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  have hsource : (HexPolyMathlib.toPolynomial
      (Factor.rawPoly levels entry.1)).Monic := by
    rw [Polynomial.Monic.def, HexPolyMathlib.leadingCoeff_toPolynomial,
      yun_monic hvalid hinjective hinv f entry hentry]
  rw [rawPolynomial_eq_map hvalid hinjective hinv]
  exact hsource.map
    (LevelSemantics.coeffHom levels hvalid hinjective hinv)

/-- The powered product of all tower Yun components reconstructs the monic
input exactly. -/
theorem yun_product
    (f : Array (Array Rat))
    (hdegree : 0 < (Factor.rawPoly levels f).degree?.getD 0) :
    Factor.yunProduct levels (Factor.yunRaw levels f) =
      Factor.polyCoords (Norm.monic (Factor.rawPoly levels f)) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  let components := (Factor.yunRaw levels f).toList
  let polys := components.map fun entry =>
    Norm.rawPolynomial levels (Factor.rawPoly levels entry.1) ^ entry.2
  let product := polys.prod
  let normalized := Norm.rawPolynomial levels (Norm.monic p)
  have hdegreeP : 0 < p.degree?.getD 0 := hdegree
  have hpNe : p ≠ 0 := by
    intro hzero
    rw [hzero] at hdegreeP
    simp at hdegreeP
  have hinputNe : Norm.rawPolynomial levels p ≠ 0 := by
    intro hzero
    have hnat : (Norm.rawPolynomial levels p).natDegree = 0 := by
      simp [hzero]
    rw [natDegree_rawPolynomial hvalid hinjective hinv] at hnat
    omega
  have hcomponentMonic : ∀ entry ∈ components,
      (Norm.rawPolynomial levels
        (Factor.rawPoly levels entry.1)).Monic := by
    intro entry hentry
    exact yun_rawPolynomial_monic hvalid hinjective hinv f entry hentry
  have hcomponentNe : ∀ entry ∈ components,
      Norm.rawPolynomial levels (Factor.rawPoly levels entry.1) ≠ 0 := by
    intro entry hentry
    exact (hcomponentMonic entry hentry).ne_zero
  have hpolysMonic : ∀ P ∈ polys, P.Monic := by
    intro P hP
    simp only [polys, List.mem_map] at hP
    obtain ⟨entry, hentry, rfl⟩ := hP
    exact (hcomponentMonic entry hentry).pow entry.2
  have hproductMonic : product.Monic := by
    change polys.prod.Monic
    have listProductMonic : ∀ (items : List (Polynomial ℂ)),
        (∀ P ∈ items, P.Monic) → items.prod.Monic := by
      intro items hitems
      induction items with
      | nil => simp
      | cons P items ih =>
          rw [List.prod_cons]
          exact (hitems P (by simp)).mul
            (ih (fun Q hQ => hitems Q (by simp [hQ])))
    exact listProductMonic polys hpolysMonic
  have hnormalizedMonic : normalized.Monic := by
    have hsourceMonic := toPolynomial_monic_monic levels hvalid hinjective
      hinv p hpNe
    change (Norm.rawPolynomial levels (Norm.monic p)).Monic
    rw [rawPolynomial_eq_map hvalid hinjective hinv]
    exact hsourceMonic.map
      (LevelSemantics.coeffHom levels hvalid hinjective hinv)
  have hpolysNe : ∀ P ∈ polys, P ≠ 0 := by
    intro P hP
    exact (hpolysMonic P hP).ne_zero
  have hmultiplicity (z : ℂ) : product.rootMultiplicity z =
      normalized.rootMultiplicity z := by
    have hsum := yunMultiplicity_sum hvalid hinjective hinv f hdegree z
      components (by intro entry hentry; exact hentry)
      (yun_multiplicities hvalid hinjective hinv f) (by
        intro hroot
        obtain ⟨entry, hentry, hentryRoot, _⟩ :=
          yun_complete hvalid hinjective hinv f hdegree z hroot
        exact ⟨entry, hentry, hentryRoot⟩)
    calc
      product.rootMultiplicity z =
          (polys.map fun P => P.rootMultiplicity z).sum :=
        rootMultiplicity_list_prod_complex polys hpolysNe z
      _ = (components.map fun entry => entry.2 *
          (Norm.rawPolynomial levels
            (Factor.rawPoly levels entry.1)).rootMultiplicity z).sum := by
        congr 1
        simp only [polys, List.map_map, Function.comp_apply]
        apply List.map_congr_left
        intro entry hentry
        exact rootMultiplicity_pow_complex _
          (hcomponentNe entry hentry) entry.2 z
      _ = (Norm.rawPolynomial levels p).rootMultiplicity z := hsum
      _ = normalized.rootMultiplicity z :=
        (rootMultiplicity_associated_complex
          (rawPolynomial_monic_associated hvalid hinjective hinv p hinputNe)
          z).symm
  have hroots : product.roots = normalized.roots := by
    apply Multiset.ext.mpr
    intro z
    rw [Polynomial.count_roots, Polynomial.count_roots]
    exact hmultiplicity z
  have hsemantic : product = normalized := by
    rw [(IsAlgClosed.splits product).eq_prod_roots_of_monic hproductMonic,
      (IsAlgClosed.splits normalized).eq_prod_roots_of_monic
        hnormalizedMonic, hroots]
  let fold := components.foldl (fun result entry =>
    result * Factor.polyPow (Factor.rawPoly levels entry.1) entry.2) 1
  have hfoldSemantic : Norm.rawPolynomial levels fold = product := by
    dsimp only [fold]
    rw [rawPolynomial_yunFold hvalid hinjective hinv,
      Norm.rawPolynomial_one levels hvalid hinjective hinv, mul_one]
  have hfold : fold = Norm.monic p := by
    apply Norm.rawPolynomial_injective levels hvalid hinjective hinv
    rw [hfoldSemantic]
    exact hsemantic
  unfold Factor.yunProduct
  rw [← Array.foldl_toList]
  change Factor.polyCoords fold = Factor.polyCoords (Norm.monic p)
  rw [hfold]

/-- The executable Yun decomposition always passes its full internal
certificate check. -/
theorem checkYun_yunRaw
    (f : Array (Array Rat)) :
    Factor.checkYun levels f (Factor.yunRaw levels f) := by
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  by_cases hdegreeZero : p.degree?.getD 0 = 0
  · simp [Factor.checkYun, Factor.yunRaw, p, hdegreeZero]
  · have hdegree : 0 < p.degree?.getD 0 :=
      Nat.pos_of_ne_zero hdegreeZero
    let components := Factor.yunRaw levels f
    have hmultiplicities :
        Factor.yunMultiplicitiesIncrease components := by
      simp only [Factor.yunMultiplicitiesIncrease, decide_eq_true_eq]
      exact yun_multiplicities hvalid hinjective hinv f
    have hpositiveMonic : components.all (fun component =>
        0 < component.2 &&
          let factor := Factor.rawPoly levels component.1
          0 < factor.degree?.getD 0 && factor.leadingCoeff = 1) := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro component hcomponent
      have hcomponent' : component ∈
          (Factor.yunRaw levels f).toList := by
        apply Array.mem_toList_iff.mpr
        simpa only [components] using hcomponent
      have hpositive := yun_positive hvalid hinjective hinv f component
        hcomponent'
      have hmonic := yun_monic hvalid hinjective hinv f component hcomponent'
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hpositive.2, hpositive.1, hmonic⟩
    have hcoprime : Factor.yunPairwiseCoprime levels components := by
      simp only [Factor.yunPairwiseCoprime, decide_eq_true_eq]
      have pairwiseCoprime : ∀
          (items : List (Array (Array Rat) × Nat)),
          (∀ entry ∈ items, entry ∈ components.toList) →
          (items.Pairwise fun a b => a.2 < b.2) →
          items.Pairwise fun a b =>
            (DensePoly.gcd (Factor.rawPoly levels a.1)
              (Factor.rawPoly levels b.1)).size ≤ 1 := by
        intro items hitems hpairwise
        induction items with
        | nil => simp
        | cons entry items ih =>
            rw [List.pairwise_cons] at hpairwise ⊢
            constructor
            · intro other hother
              exact yun_coprime hvalid hinjective hinv f hdegree entry other
                (hitems entry (by simp))
                (hitems other (by simp [hother]))
                (hpairwise.1 other hother)
            · exact ih (fun other hother =>
                hitems other (by simp [hother])) hpairwise.2
      exact pairwiseCoprime components.toList (by
        intro entry hentry
        exact hentry) (yun_multiplicities hvalid hinjective hinv f)
    have hsquarefree : components.all (fun component =>
        Norm.isSquarefree levels component.1) := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro component hcomponent
      have hcomponent' : component ∈
          (Factor.yunRaw levels f).toList := by
        apply Array.mem_toList_iff.mpr
        simpa only [components] using hcomponent
      exact yun_squarefree hvalid hinjective hinv f hdegree component
        hcomponent'
    have hproduct : Factor.yunProduct levels components =
        Factor.polyCoords (Norm.monic p) :=
      yun_product hvalid hinjective hinv f hdegree
    simp only [Factor.checkYun, p, hdegreeZero, ite_false,
      Bool.and_eq_true]
    exact ⟨⟨⟨⟨hmultiplicities, hpositiveMonic⟩, hcoprime⟩,
      hsquarefree⟩, decide_eq_true hproduct⟩

end Yun

end Hex.NumberTower
