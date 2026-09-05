/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.FactorGeneric.Trager

public section

/-!
# Reconstruction products for Trager factorization

Product identities assembling one squarefree component from its recovered
factors: fold/product correspondences for factor arrays, gcd-distribution
over squarefree products, and the reconstruction theorems for one Trager
recovery step and for the rational base case.
-/

namespace Hex.NumberTower

/-- Mapping a ring homomorphism across a list of polynomials commutes with
taking the product. -/
theorem polynomial_map_list_prod {R S : Type*}
    [Semiring R] [Semiring S] (f : R →+* S)
    (ps : List (Polynomial R)) :
    ps.prod.map f = (ps.map fun p => p.map f).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

/-- Over the empty tower the raw coordinate polynomial vanishes exactly when
its rational reading does: `Factor.rawPoly []` and `Factor.toRatPoly` present
the same polynomial through the coefficient identification with `ℚ`. -/
theorem rawPoly_nil_eq_zero_iff (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    Factor.rawPoly [] f = 0 ↔ Factor.toRatPoly f = 0 := by
  let : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  constructor
  · intro h
    have hmap := LevelSemantics.map_rawPoly_nil f
    rw [h, HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero] at hmap
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    simpa using hmap.symm
  · intro h
    apply (HexPolyMathlib.equiv (R := Arithmetic.Coeff [])).injective
    change HexPolyMathlib.toPolynomial (Factor.rawPoly [] f) = 0
    apply Polynomial.map_injective LevelSemantics.coeffRatEquiv.toRingHom
      LevelSemantics.coeffRatEquiv.injective
    rw [LevelSemantics.map_rawPoly_nil, h,
      HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero]

/-- Over the empty tower, monic normalisation commutes with the coefficient
identification with `ℚ`: normalising `Factor.rawPoly [] f` and then reading
coefficients rationally gives the leading-coefficient rescaling of
`Factor.toRatPoly f`. -/
theorem map_monic_rawPoly_nil (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    (HexPolyMathlib.toPolynomial
      (Norm.monic (Factor.rawPoly [] f))).map
        LevelSemantics.coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial
        (let p := Factor.toRatPoly f
         if p.isZero then 0 else DensePoly.scale p.leadingCoeff⁻¹ p) := by
  let : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  let raw := Factor.rawPoly [] f
  let p := Factor.toRatPoly f
  have hmap : (HexPolyMathlib.toPolynomial raw).map
      LevelSemantics.coeffRatEquiv.toRingHom =
        HexPolyMathlib.toPolynomial p := by
    exact LevelSemantics.map_rawPoly_nil f
  have hzero : raw = 0 ↔ p = 0 := by
    constructor
    · intro h
      have := hmap
      rw [h, HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero] at this
      apply (HexPolyMathlib.equiv (R := Rat)).injective
      simpa using this.symm
    · intro h
      apply (HexPolyMathlib.equiv (R := Arithmetic.Coeff [])).injective
      change HexPolyMathlib.toPolynomial raw = 0
      apply Polynomial.map_injective LevelSemantics.coeffRatEquiv.toRingHom
        LevelSemantics.coeffRatEquiv.injective
      rw [hmap, h, HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero]
  have hlc : LevelSemantics.coeffRatEquiv raw.leadingCoeff =
      p.leadingCoeff := by
    change LevelSemantics.coeffRatEquiv.toRingHom raw.leadingCoeff = _
    rw [← HexPolyMathlib.leadingCoeff_toPolynomial raw,
      ← Polynomial.leadingCoeff_map_of_injective
        LevelSemantics.coeffRatEquiv.injective, hmap,
      HexPolyMathlib.leadingCoeff_toPolynomial p]
  simp only [Norm.monic]
  split
  · rename_i hrawZero
    change raw.isZero = true at hrawZero
    have hpZero : p.isZero = true := by
      rw [DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff,
        ← hzero, ← DensePoly.size_eq_zero_iff,
        ← DensePoly.isZero_eq_true_iff]
      exact hrawZero
    rw [hpZero]
    simp only [ite_true]
    have hraw : raw = 0 :=
      (DensePoly.size_eq_zero_iff raw).mp
        ((DensePoly.isZero_eq_true_iff raw).mp hrawZero)
    simp
  · rename_i hrawZero
    change ¬ raw.isZero = true at hrawZero
    have hpZero : p.isZero = false := by
      rw [DensePoly.isZero_eq_false_iff]
      exact Nat.pos_of_ne_zero fun hpSize => by
        apply hrawZero
        rw [DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff,
          hzero, ← DensePoly.size_eq_zero_iff]
        exact hpSize
    rw [hpZero]
    simp only [Bool.false_eq_true, ite_false]
    change (HexPolyMathlib.toPolynomial
        (DensePoly.scale raw.leadingCoeff⁻¹ raw)).map
          LevelSemantics.coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial (DensePoly.scale p.leadingCoeff⁻¹ p)
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyMathlib.toPolynomial_scale, Polynomial.map_mul,
      Polynomial.map_C, map_inv₀]
    have hlc' : LevelSemantics.coeffRatEquiv.toRingHom raw.leadingCoeff =
        p.leadingCoeff := hlc
    rw [hlc', hmap]

/-- The executable left fold multiplying raw tower factors interprets to the
initial value times the product of the interpreted factors. -/
theorem rawFactorFoldl (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (hinv : ∀ a : Arithmetic.Coeff levels,
      LevelSemantics.coeffDenote levels a⁻¹ =
        (LevelSemantics.coeffDenote levels a)⁻¹)
    (factors : List (Array (Array Rat)))
    (init : DensePoly (Arithmetic.Coeff levels)) :
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor =>
          product * Factor.rawPoly levels factor) init) =
      HexPolyMathlib.toPolynomial init *
        (factors.map fun factor => HexPolyMathlib.toPolynomial
          (R := Arithmetic.Coeff levels)
          (Factor.rawPoly levels factor)).prod := by
  let : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction factors generalizing init with
  | nil => simp
  | cons factor factors ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.prod_cons,
        HexPolyMathlib.toPolynomial_mul]
      ring

/-- Rational analogue of {name}`rawFactorFoldl`: the executable left fold
multiplying rational readings of factors interprets to the initial value
times the product of the interpreted factors. -/
theorem ratFactorFoldl (factors : List (Array (Array Rat)))
    (init : DensePoly Rat) :
    HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor =>
          product * Factor.toRatPoly factor) init) =
      HexPolyMathlib.toPolynomial init *
        (factors.map fun factor => HexPolyMathlib.toPolynomial
          (Factor.toRatPoly factor)).prod := by
  induction factors generalizing init with
  | nil => simp
  | cons factor factors ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.prod_cons,
        HexPolyMathlib.toPolynomial_mul]
      ring

/-- Reconstruction for one squarefree component: the factors returned by
`Factor.factorSquarefree?` multiply to the monic normalisation of the input,
after interpretation over the tower coefficient field. -/
theorem factorSquarefree_product (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) {factors : Array (Array (Array Rat))}
    (hf : Factor.rawPoly levels f ≠ 0)
    (hresult : Factor.factorSquarefree? levels f = some factors) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    (factors.toList.map fun factor => HexPolyMathlib.toPolynomial
      (Factor.rawPoly levels factor)).prod =
        HexPolyMathlib.toPolynomial
          (Norm.monic (Factor.rawPoly levels f)) := by
  cases levels with
  | nil =>
      let : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil
      dsimp only
      have hinputNe : Factor.toRatPoly f ≠ 0 :=
        mt (rawPoly_nil_eq_zero_iff f).mpr hf
      have hinputZero : (Factor.toRatPoly f).isZero = false := by
        rw [DensePoly.isZero_eq_false_iff]
        exact Nat.pos_of_ne_zero fun hsize =>
          hinputNe ((DensePoly.size_eq_zero_iff _).mp hsize)
      let p := DensePoly.scale (Factor.toRatPoly f).leadingCoeff⁻¹
        (Factor.toRatPoly f)
      have hpNe : p ≠ 0 := by
        intro hzero
        have hpoly := congrArg HexPolyMathlib.toPolynomial hzero
        rw [HexPolyMathlib.toPolynomial_scale,
          HexPolyMathlib.toPolynomial_zero] at hpoly
        have hleadingNe : (Factor.toRatPoly f).leadingCoeff ≠ 0 :=
          DensePoly.leadingCoeff_ne_zero_of_pos_size _
            ((DensePoly.isZero_eq_false_iff _).mp hinputZero)
        have hinputPoly : HexPolyMathlib.toPolynomial
            (Factor.toRatPoly f) = 0 :=
          (mul_eq_zero.mp hpoly).resolve_left
            (Polynomial.C_ne_zero.mpr (inv_ne_zero hleadingNe))
        apply hinputNe
        apply (HexPolyMathlib.equiv (R := Rat)).injective
        simpa using hinputPoly
      simp only [Factor.factorSquarefree?] at hresult
      simp only [Factor.factorRat?] at hresult
      split at hresult
      · cases hresult
        exfalso
        apply hf
        have hp : Factor.toRatPoly f = 0 :=
          (DensePoly.size_eq_zero_iff _).mp
            ((DensePoly.isZero_eq_true_iff _).mp ‹_›)
        exact (rawPoly_nil_eq_zero_iff f).mpr hp
      · split at hresult
        · cases hresult
          exfalso
          apply hf
          have hpZero : p = 0 := by
            apply (DensePoly.size_eq_zero_iff _).mp
            exact (DensePoly.isZero_eq_true_iff _).mp ‹_›
          exact (hpNe hpZero).elim
        · split at hresult
          · split at hresult
            · rename_i hinputZero hpZero hgcd hproduct
              cases hresult
              have hmappedList (xs : List (Array (Array Rat))) :
                  (xs.map fun factor => HexPolyMathlib.toPolynomial
                    (Factor.rawPoly [] factor)).map
                      (fun q => q.map
                        LevelSemantics.coeffRatEquiv.toRingHom) =
                    xs.map fun factor => HexPolyMathlib.toPolynomial
                      (Factor.toRatPoly factor) := by
                rw [List.map_map]
                apply List.map_congr_left
                intro factor hfactor
                exact LevelSemantics.map_rawPoly_nil factor
              apply Polynomial.map_injective
                LevelSemantics.coeffRatEquiv.toRingHom
                LevelSemantics.coeffRatEquiv.injective
              rw [polynomial_map_list_prod, hmappedList,
                map_monic_rawPoly_nil, ite_eq_right hinputZero]
              have hpoly := congrArg HexPolyMathlib.toPolynomial hproduct
              rw [← Array.foldl_toList,
                ratFactorFoldl] at hpoly
              simpa using hpoly
            · cases hresult
          · cases hresult
  | cons level lower =>
      let hinv := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
        hinjective
      let : Field (Arithmetic.Coeff (level :: lower)) :=
        Norm.coeffFieldPoly (level :: lower) hvalid hinjective hinv
      dsimp only
      simp only [Factor.factorSquarefree?] at hresult
      split at hresult
      · obtain ⟨pair, hfind, hresult⟩ := Option.bind_eq_some_iff.mp hresult
        obtain ⟨lowerFactors, hlower, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        split at hresult
        · rename_i hcheck
          cases hresult
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
          have hproduct := hcheck.2
          rw [← Array.foldl_toList] at hproduct
          have hpoly := congrArg HexPolyMathlib.toPolynomial hproduct
          rw [rawFactorFoldl (level :: lower) hvalid hinjective hinv] at hpoly
          simpa using hpoly
        · contradiction
      · contradiction

/-- The gcd of `P` with a squarefree product is associated to the product of
the gcds with the individual factors: pairwise coprimality of the squarefree
factors lets the gcd distribute over the product. -/
theorem gcd_prod_associated {K : Type*} [Field K] [DecidableEq K]
    (P : Polynomial K) : ∀ qs : List (Polynomial K),
    Squarefree qs.prod →
    Associated (gcd P qs.prod)
      ((qs.map fun q => gcd P q).prod) := by
  intro qs
  induction qs with
  | nil =>
      intro hsquarefree
      simp
  | cons q qs ih =>
      intro hsquarefree
      have hparts := squarefree_mul_iff.mp hsquarefree
      have htail := ih hparts.2.2
      let gq := gcd P q
      let gt := gcd P qs.prod
      have hrel : IsRelPrime gq gt :=
        (hparts.1.of_dvd_left (gcd_dvd_right P q)).of_dvd_right
          (gcd_dvd_right P qs.prod)
      have hcop : IsCoprime gq gt := hrel.isCoprime
      have hforward : gcd P (q * qs.prod) ∣ gq * gt := by
        exact gcd_mul_dvd_mul_gcd P q qs.prod
      have hback : gq * gt ∣ gcd P (q * qs.prod) := by
        apply dvd_gcd
        · exact hcop.mul_dvd (gcd_dvd_left P q)
            (gcd_dvd_left P qs.prod)
        · exact mul_dvd_mul (gcd_dvd_right P q)
            (gcd_dvd_right P qs.prod)
      have hstep : Associated (gcd P (q * qs.prod))
          (gq * gt) := associated_of_dvd_dvd hforward hback
      simpa [gq, gt] using hstep.trans
        ((Associated.refl (gcd P q)).mul_mul htail)

/-- Trager's gcd recovery is complete: if `P` divides a squarefree product,
the product of the gcds of `P` with the factors recovers `P` up to a unit. -/
theorem prod_gcd_associated {K : Type*} [Field K] [DecidableEq K]
    (P : Polynomial K) (qs : List (Polynomial K))
    (hsquarefree : Squarefree qs.prod) (hdiv : P ∣ qs.prod) :
    Associated ((qs.map fun q => gcd P q).prod) P := by
  have h := (gcd_prod_associated P qs hsquarefree).symm
  have hgcd : gcd P qs.prod = normalize P :=
    gcd_eq_normalize (gcd_dvd_left P qs.prod) (dvd_gcd dvd_rfl hdiv)
  rw [hgcd] at h
  exact h.trans (associated_normalize P).symm

/-- The Euclidean-algorithm gcd and the normalised `GCDMonoid` gcd of two
polynomials agree up to a unit. -/
theorem euclidean_gcd_associated_gcd {K : Type*} [Field K]
    [DecidableEq K]
    (a b : Polynomial K) :
    Associated (EuclideanDomain.gcd a b) (gcd a b) := by
  apply associated_of_dvd_dvd
  · apply dvd_gcd
    · exact EuclideanDomain.gcd_dvd_left a b
    · exact EuclideanDomain.gcd_dvd_right a b
  · apply EuclideanDomain.dvd_gcd
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b

set_option maxHeartbeats 800000 in
/-- Shifting the product of the factors recovered by `Factor.recover` back by
the shift delta gives, up to a unit, the product of the gcds of the shifted
component with the lifted lower-tower factors. Lower factors whose gcd is
constant contribute a unit and are exactly the ones the recovery loop
discards. -/
theorem recover_product_associated (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component : Array (Array Rat)) (shift : Int)
    (lowerFactors : Array (Array (Array Rat)))
    (hcomponentNe : Factor.rawPoly (level :: lower) component ≠ 0) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let delta := Arithmetic.Coeff.ofData (level :: lower) #[(shift : Rat)] *
      Factor.topGenerator level lower
    let shifted := Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower component shift)
    let lifted (lowerFactor : Array (Array Rat)) :=
      Factor.rawPoly (level :: lower)
        (Factor.embedLower level lower lowerFactor)
    Associated
      (Polynomial.taylor (-delta)
        ((Factor.recover level lower shift component lowerFactors).toList.map
          fun factor => HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) factor)).prod)
      ((lowerFactors.toList.map fun lowerFactor =>
        EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
          (HexPolyMathlib.toPolynomial (lifted lowerFactor))).prod) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(shift : Rat)] *
    Factor.topGenerator level lower
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower component shift)
  let lifted (lowerFactor : Array (Array Rat)) :=
    Factor.rawPoly (level :: lower)
      (Factor.embedLower level lower lowerFactor)
  let g (lowerFactor : Array (Array Rat)) :=
    DensePoly.gcd shifted (lifted lowerFactor)
  let common (lowerFactor : Array (Array Rat)) := Norm.monic (g lowerFactor)
  let pass (lowerFactor : Array (Array Rat)) :=
    0 < (common lowerFactor).degree?.getD 0
  let unshifted (lowerFactor : Array (Array Rat)) :=
    Factor.rawPoly (level :: lower)
      (Factor.shiftTop level lower (Factor.polyCoords (common lowerFactor))
        (-shift))
  let result (lowerFactor : Array (Array Rat)) :=
    Norm.monic (unshifted lowerFactor)
  let recovered (lowerFactor : Array (Array Rat)) :=
    Factor.polyCoords (result lowerFactor)
  dsimp only
  have hcomponentPolyNe : HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower) component) ≠ 0 := by
    intro hzero
    apply hcomponentNe
    apply (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff (level :: lower))).injective
    simpa using hzero
  have hshiftedPolyNe : HexPolyMathlib.toPolynomial shifted ≠ 0 := by
    change HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower component shift)) ≠ 0
    rw [toPolynomial_shiftTop level lower hvalid hinjectiveTop]
    intro hzero
    have hback := congrArg (Polynomial.taylor delta) hzero
    apply hcomponentPolyNe
    simpa [delta, Polynomial.taylor_taylor] using hback
  have hgNe (lowerFactor : Array (Array Rat)) : g lowerFactor ≠ 0 := by
    have hassociated := HexPolyMathlib.toPolynomial_gcd_associated
      shifted (lifted lowerFactor)
    have hgcdNe : EuclideanDomain.gcd
        (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor)) ≠ 0 := by
      intro hzero
      exact hshiftedPolyNe
        (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
    have hpolyNe : HexPolyMathlib.toPolynomial (g lowerFactor) ≠ 0 :=
      hassociated.ne_zero_iff.mpr hgcdNe
    intro hzero
    apply hpolyNe
    simp [g, hzero]
  have hcommonPolyNe (lowerFactor : Array (Array Rat)) :
      HexPolyMathlib.toPolynomial (common lowerFactor) ≠ 0 :=
    (toPolynomial_monic_monic (level :: lower) hvalid hinjectiveTop hinvTop
      (g lowerFactor) (hgNe lowerFactor)).ne_zero
  have hcommonAssoc (lowerFactor : Array (Array Rat)) : Associated
      (HexPolyMathlib.toPolynomial (common lowerFactor))
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor))) :=
    (toPolynomial_monic_associated (level :: lower) hvalid
      hinjectiveTop hinvTop (g lowerFactor) (hgNe lowerFactor)).trans
        (HexPolyMathlib.toPolynomial_gcd_associated shifted
          (lifted lowerFactor))
  have hunshiftedPoly (lowerFactor : Array (Array Rat)) :
      HexPolyMathlib.toPolynomial (unshifted lowerFactor) =
        Polynomial.taylor delta
          (HexPolyMathlib.toPolynomial (common lowerFactor)) := by
    change HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower (Factor.polyCoords (common lowerFactor))
          (-shift))) = _
    rw [toPolynomial_shiftTop level lower hvalid hinjectiveTop,
      rawPoly_polyCoords]
    have hdelta := shiftDelta_neg level lower hvalid hinjectiveTop shift
    simpa only [Int.cast_neg] using congrArg
      (fun c => Polynomial.taylor c
        (HexPolyMathlib.toPolynomial (common lowerFactor))) hdelta
  have hunshiftedNe (lowerFactor : Array (Array Rat)) :
      unshifted lowerFactor ≠ 0 := by
    intro hzero
    have hpolyZero : Polynomial.taylor delta
        (HexPolyMathlib.toPolynomial (common lowerFactor)) = 0 := by
      rw [← hunshiftedPoly lowerFactor, hzero]
      exact HexPolyMathlib.toPolynomial_zero
    have hback := congrArg (Polynomial.taylor (-delta)) hpolyZero
    apply hcommonPolyNe lowerFactor
    simpa [Polynomial.taylor_taylor] using hback
  have hpass (lowerFactor : Array (Array Rat))
      (_hpass : pass lowerFactor) : Associated
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial (result lowerFactor)))
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor))) := by
    have hnormalized := toPolynomial_monic_associated (level :: lower)
      hvalid hinjectiveTop hinvTop (unshifted lowerFactor)
        (hunshiftedNe lowerFactor)
    have hmapped := hnormalized.map
      (Polynomial.taylorEquiv (-delta)).toMonoidHom
    change Associated
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial (Norm.monic (unshifted lowerFactor))))
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial (unshifted lowerFactor))) at hmapped
    have htaylor : Associated
        (Polynomial.taylor (-delta)
          (HexPolyMathlib.toPolynomial (result lowerFactor)))
        (HexPolyMathlib.toPolynomial (common lowerFactor)) := by
      change Associated
        (Polynomial.taylor (-delta)
          (HexPolyMathlib.toPolynomial (Norm.monic (unshifted lowerFactor))))
        (HexPolyMathlib.toPolynomial (common lowerFactor))
      rw [hunshiftedPoly lowerFactor] at hmapped
      simpa [Polynomial.taylor_taylor] using hmapped
    exact htaylor.trans (hcommonAssoc lowerFactor)
  have hskip (lowerFactor : Array (Array Rat))
      (hskip : ¬ pass lowerFactor) : IsUnit
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
        (HexPolyMathlib.toPolynomial (lifted lowerFactor))) := by
    apply (hcommonAssoc lowerFactor).isUnit_iff.mp
    apply Polynomial.isUnit_iff_degree_eq_zero.mpr
    rw [Polynomial.degree_eq_natDegree (hcommonPolyNe lowerFactor),
      HexPolyMathlib.natDegree_toPolynomial]
    have hdegree : (common lowerFactor).degree?.getD 0 = 0 :=
      Nat.eq_zero_of_not_pos hskip
    rw [hdegree]
    rfl
  have hfiltered := filterMap_prod_associated pass
    (fun lowerFactor => Polynomial.taylor (-delta)
      (HexPolyMathlib.toPolynomial (result lowerFactor)))
    (fun lowerFactor => EuclideanDomain.gcd
      (HexPolyMathlib.toPolynomial shifted)
      (HexPolyMathlib.toPolynomial (lifted lowerFactor)))
    hpass hskip lowerFactors.toList
  have hrecoverList :
      (Factor.recover level lower shift component lowerFactors).toList =
        lowerFactors.toList.filterMap (fun lowerFactor =>
          if pass lowerFactor then some (recovered lowerFactor) else none) := by
    have hfold := foldl_push_if_toList pass recovered
      lowerFactors.toList (#[] : Array (Array (Array Rat)))
    simpa only [Factor.recover, Array.foldl_toList, List.nil_append,
      shifted, lifted, g, common, pass, unshifted, result, recovered] using hfold
  rw [taylor_list_prod, hrecoverList]
  simpa [List.map_filterMap, Function.comp_def, recovered,
    rawPoly_polyCoords, delta, shifted, lifted] using hfiltered

/-- When every recovered factor interprets to an irreducible polynomial, the
product of the interpreted recovered factors is monic: each factor is a monic
normalisation by construction. -/
theorem recover_product_monic (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component : Array (Array Rat)) (shift : Int)
    (lowerFactors : Array (Array (Array Rat))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    (∀ factor ∈ Factor.recover level lower shift component lowerFactors,
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor))) →
    ((Factor.recover level lower shift component lowerFactors).toList.map
      fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod.Monic := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  dsimp only
  intro hsound
  let allFactors :=
    (Factor.recover level lower shift component lowerFactors).toList
  have go : ∀ factors : List (Array (Array Rat)),
      (∀ factor ∈ factors, factor ∈ allFactors) →
      (factors.map fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod.Monic := by
    intro factors hmem
    induction factors with
    | nil => simp
    | cons factor factors ih =>
      rw [List.map_cons, List.prod_cons]
      have hfactorMem : factor ∈
          Factor.recover level lower shift component lowerFactors := by
        exact Array.mem_toList_iff.mp (hmem factor (by simp))
      obtain ⟨lowerFactor, hlowerFactor, hdegree, hrecovered⟩ :=
        recover_mem level lower shift component lowerFactors hfactorMem
      let shifted := Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower component shift)
      let lifted := Factor.rawPoly (level :: lower)
        (Factor.embedLower level lower lowerFactor)
      let common := Norm.monic (DensePoly.gcd shifted lifted)
      let unshifted := Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower (Factor.polyCoords common) (-shift))
      have hirreducible := hsound factor hfactorMem
      have hunshiftedNe : unshifted ≠ 0 := by
        intro hzero
        apply hirreducible.ne_zero
        rw [← hrecovered, rawPoly_polyCoords]
        change HexPolyMathlib.toPolynomial (Norm.monic unshifted) = 0
        rw [hzero]
        simp [Norm.monic]
      have hfactorMonic : (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) factor)).Monic := by
        rw [← hrecovered, rawPoly_polyCoords]
        change (HexPolyMathlib.toPolynomial (Norm.monic unshifted)).Monic
        exact toPolynomial_monic_monic (level :: lower) hvalid
          hinjectiveTop hinvTop unshifted hunshiftedNe
      exact hfactorMonic.mul (ih (fun candidate hc =>
        hmem candidate (by simp [hc])))
  exact go allFactors (fun factor hfactor => hfactor)

set_option maxHeartbeats 800000 in
/-- Reconstruction across one Trager recovery step: given a squarefree
one-level norm at the accepted shift and lower-tower factors that multiply to
its monic normalisation, the recovered top-level factors multiply to the
monic normalisation of the squarefree component itself. -/
theorem recover_product (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (component norm : Array (Array Rat)) (shift : Int)
    (lowerFactors : Array (Array (Array Rat))) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Factor.rawPoly (level :: lower) component ≠ 0 →
    Squarefree (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)) →
    norm = Norm.oneLevel level lower component shift →
    (∀ lowerFactor ∈ lowerFactors,
      Factor.polyCoords (Factor.rawPoly lower lowerFactor) = lowerFactor) →
    ((lowerFactors.toList.map fun lowerFactor =>
      HexPolyMathlib.toPolynomial
        (Factor.rawPoly lower lowerFactor)).prod =
      HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm))) →
    (∀ factor ∈ Factor.recover level lower shift component lowerFactors,
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor))) →
    ((Factor.recover level lower shift component lowerFactors).toList.map
      fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod =
      HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly (level :: lower) component)) := by
  classical
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  dsimp only
  intro hcomponentNe hnormSquarefree hnormEq hlowerCoords hlowerProduct
    hrecoverSound
  let φ := Norm.lowerHom level lower hvalid hinjectiveTop
  let lowerPolys := lowerFactors.toList.map fun lowerFactor =>
    HexPolyMathlib.toPolynomial (Factor.rawPoly lower lowerFactor)
  let shifted := Factor.rawPoly (level :: lower)
    (Factor.shiftTop level lower component shift)
  let lifted (lowerFactor : Array (Array Rat)) :=
    Factor.rawPoly (level :: lower)
      (Factor.embedLower level lower lowerFactor)
  let qs := lowerFactors.toList.map fun lowerFactor =>
    HexPolyMathlib.toPolynomial (lifted lowerFactor)
  let recoveredProduct :=
    ((Factor.recover level lower shift component lowerFactors).toList.map
      fun factor => HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) factor)).prod
  let delta := Arithmetic.Coeff.ofData (level :: lower) #[(shift : Rat)] *
    Factor.topGenerator level lower
  let ιLower := LevelSemantics.coeffHom lower hvalid.2.2
    hinjectiveLower hinvLower
  let ιTop := LevelSemantics.coeffHom (level :: lower) hvalid
    hinjectiveTop hinvTop
  let : CharZero (Arithmetic.Coeff lower) :=
    { cast_injective := by
        intro m n hmn
        apply Nat.cast_injective (R := ℂ)
        have hmapped := congrArg ιLower hmn
        simpa only [map_natCast] using hmapped }
  let : CharZero (Arithmetic.Coeff (level :: lower)) :=
    { cast_injective := by
        intro m n hmn
        apply Nat.cast_injective (R := ℂ)
        have hmapped := congrArg ιTop hmn
        simpa only [map_natCast] using hmapped }
  have hnormNe : Factor.rawPoly lower norm ≠ 0 := by
    intro hzero
    apply hnormSquarefree.ne_zero
    rw [hzero]
    exact HexPolyMathlib.toPolynomial_zero
  have hnormAssoc : Associated
      (HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm)))
      (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)) :=
    toPolynomial_monic_associated lower hvalid.2.2 hinjectiveLower
      hinvLower (Factor.rawPoly lower norm) hnormNe
  have hnormMonicSquarefree : Squarefree
      (HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm))) :=
    hnormAssoc.squarefree_iff.mpr hnormSquarefree
  have hlifted (lowerFactor : Array (Array Rat))
      (hlowerFactor : lowerFactor ∈ lowerFactors) :
      HexPolyMathlib.toPolynomial (lifted lowerFactor) =
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly lower lowerFactor)).map φ := by
    let q := Factor.rawPoly lower lowerFactor
    have hcoords : Factor.polyCoords q = lowerFactor :=
      hlowerCoords lowerFactor hlowerFactor
    calc
      HexPolyMathlib.toPolynomial (lifted lowerFactor) =
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower)
              (Factor.embedLower level lower (Factor.polyCoords q))) := by
        rw [hcoords]
      _ = (HexPolyMathlib.toPolynomial q).map
          (Norm.lowerHom level lower hvalid hinjectiveTop) := by
        rw [rawPoly_embedLower_polyCoords level lower hvalid hinjectiveTop,
          HexPolyMathlib.toPolynomial_ofPolynomial]
      _ = (HexPolyMathlib.toPolynomial
          (Factor.rawPoly lower lowerFactor)).map φ := rfl
  have hqs : qs.prod =
      (HexPolyMathlib.toPolynomial
        (Norm.monic (Factor.rawPoly lower norm))).map φ := by
    have hlist : qs = lowerPolys.map fun p => p.map φ := by
      dsimp only [qs, lowerPolys]
      rw [List.map_map]
      apply List.map_congr_left
      intro lowerFactor hlowerFactor
      exact hlifted lowerFactor (Array.mem_toList_iff.mp hlowerFactor)
    calc
      qs.prod = (lowerPolys.map fun p => p.map φ).prod :=
        congrArg List.prod hlist
      _ = lowerPolys.prod.map φ :=
        (polynomial_map_list_prod φ lowerPolys).symm
      _ = (HexPolyMathlib.toPolynomial
          (Norm.monic (Factor.rawPoly lower norm))).map φ := by
        rw [show lowerPolys.prod = HexPolyMathlib.toPolynomial
          (Norm.monic (Factor.rawPoly lower norm)) by
            exact hlowerProduct]
  have hqsSquarefree : Squarefree qs.prod := by
    rw [hqs]
    exact polynomial_squarefree_map φ hnormMonicSquarefree
  have hshiftedDvd : HexPolyMathlib.toPolynomial shifted ∣ qs.prod := by
    have hdiv := Norm.shifted_dvd_norm level lower hvalid hinjectiveTop
      component shift
    rw [← hnormEq] at hdiv
    have hnormDvdMonic :
        (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)).map φ ∣
          (HexPolyMathlib.toPolynomial
            (Norm.monic (Factor.rawPoly lower norm))).map φ := by
      obtain ⟨u, hu⟩ := hnormAssoc.symm.dvd
      refine ⟨u.map φ, ?_⟩
      rw [hu, Polynomial.map_mul]
    rw [hqs]
    exact hdiv.trans hnormDvdMonic
  have hgcdProduct := prod_gcd_associated
    (HexPolyMathlib.toPolynomial shifted) qs hqsSquarefree hshiftedDvd
  have hgcdBridge : Associated
      ((lowerFactors.toList.map fun lowerFactor =>
        EuclideanDomain.gcd (HexPolyMathlib.toPolynomial shifted)
          (HexPolyMathlib.toPolynomial (lifted lowerFactor))).prod)
      ((qs.map fun q => gcd (HexPolyMathlib.toPolynomial shifted) q).prod) := by
    have go : ∀ items : List
        (Polynomial (Arithmetic.Coeff (level :: lower))),
        Associated
          ((items.map fun q => EuclideanDomain.gcd
            (HexPolyMathlib.toPolynomial shifted) q).prod)
          ((items.map fun q => gcd
            (HexPolyMathlib.toPolynomial shifted) q).prod) := by
      intro items
      induction items with
      | nil => simp
      | cons q items ih =>
          simp only [List.map_cons, List.prod_cons]
          exact (euclidean_gcd_associated_gcd
            (HexPolyMathlib.toPolynomial shifted) q).mul_mul ih
    simpa [qs, List.map_map, Function.comp_def] using go qs
  have hrecoverAssoc := recover_product_associated level lower hvalid
    hinjectiveTop component shift lowerFactors hcomponentNe
  have hshiftedAssoc : Associated
      (Polynomial.taylor (-delta) recoveredProduct)
      (HexPolyMathlib.toPolynomial shifted) := by
    exact hrecoverAssoc.trans (hgcdBridge.trans hgcdProduct)
  have hshiftedEq : HexPolyMathlib.toPolynomial shifted =
      Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) component)) := by
    exact toPolynomial_shiftTop level lower hvalid hinjectiveTop
      component shift
  rw [hshiftedEq] at hshiftedAssoc
  have hback := hshiftedAssoc.map
    (Polynomial.taylorEquiv delta).toMonoidHom
  change Associated
    (Polynomial.taylor delta
      (Polynomial.taylor (-delta) recoveredProduct))
    (Polynomial.taylor delta
      (Polynomial.taylor (-delta)
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly (level :: lower) component)))) at hback
  have hrecoveredAssoc : Associated recoveredProduct
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower) component)) := by
    simpa [Polynomial.taylor_taylor] using hback
  have hrecoveredMonic : recoveredProduct.Monic :=
    recover_product_monic level lower hvalid hinjectiveTop component shift
      lowerFactors hrecoverSound
  have hcomponentMonic := toPolynomial_monic_monic (level :: lower)
    hvalid hinjectiveTop hinvTop (Factor.rawPoly (level :: lower) component)
      hcomponentNe
  have hcomponentAssoc := toPolynomial_monic_associated (level :: lower)
    hvalid hinjectiveTop hinvTop (Factor.rawPoly (level :: lower) component)
      hcomponentNe
  exact Polynomial.eq_of_monic_of_associated hrecoveredMonic hcomponentMonic
    (hrecoveredAssoc.trans hcomponentAssoc.symm)

/-- The executable left fold multiplying monically rescaled rational readings
of integer factors interprets to the initial value times the product of the
corresponding {name}`normalizedRatFactor`s. -/
theorem normalizedRatFactorFoldl (factors : List ZPoly)
    (init : DensePoly Rat) :
    HexPolyMathlib.toPolynomial
        (factors.foldl (fun product factor => product *
          DensePoly.scale factor.toRatPoly.leadingCoeff⁻¹
            factor.toRatPoly) init) =
      HexPolyMathlib.toPolynomial init *
        (factors.map normalizedRatFactor).prod := by
  induction factors generalizing init with
  | nil => simp
  | cons factor factors ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.prod_cons, normalizedRatFactor,
        HexPolyMathlib.toPolynomial_mul]
      ring

/-- Rational base case of reconstruction: the monically rescaled
Berlekamp-Zassenhaus factors of the primitive part of a monic rational
polynomial multiply back to the polynomial itself. -/
theorem factorRat_product (p : DensePoly Rat) (hp : p ≠ 0)
    (hpMonic : (HexPolyMathlib.toPolynomial p).Monic) :
    let integer := ZPoly.ratPolyPrimitivePart p
    let rawFactors := (ZPoly.factorize integer).factors.flatMap fun entry =>
      Array.replicate entry.2 entry.1
    let factors := rawFactors.map fun factor =>
      let q := ZPoly.toRatPoly factor
      let q := DensePoly.scale q.leadingCoeff⁻¹ q
      Factor.ofRatPoly q
    factors.foldl
      (fun product factor => product * Factor.toRatPoly factor) 1 = p := by
  let integer := ZPoly.ratPolyPrimitivePart p
  have hintegerNe : integer ≠ 0 := by
    intro hzero
    obtain ⟨unit, hunit⟩ :=
      ZPoly.ratPolyPrimitivePart_rational_associate p
    apply hp
    rw [hunit]
    have hprimitiveZero :
        (ZPoly.ratPolyPrimitivePart p).toRatPoly = 0 := by
      rw [← show integer = ZPoly.ratPolyPrimitivePart p from rfl, hzero]
      exact ZPoly.toRatPoly_zero
    rw [hprimitiveZero]
    simp
  let rawFactors := (ZPoly.factorize integer).factors.flatMap fun entry =>
    Array.replicate entry.2 entry.1
  let normalized (factor : ZPoly) :=
    DensePoly.scale factor.toRatPoly.leadingCoeff⁻¹ factor.toRatPoly
  let factors := rawFactors.map fun factor => Factor.ofRatPoly (normalized factor)
  have hfold : HexPolyMathlib.toPolynomial
      (factors.foldl
        (fun product factor => product * Factor.toRatPoly factor) 1) =
      (rawFactors.toList.map normalizedRatFactor).prod := by
    rw [← Array.foldl_toList]
    simp only [factors, Array.toList_map]
    have hnormalized :
        ∀ init : DensePoly Rat,
        (List.map (fun factor => Factor.ofRatPoly (normalized factor))
          rawFactors.toList).foldl
            (fun product factor => product * Factor.toRatPoly factor) init =
          rawFactors.toList.foldl
            (fun product factor => product * normalized factor) init := by
      intro init
      induction rawFactors.toList generalizing init with
      | nil => rfl
      | cons factor tail ih =>
          rw [List.map_cons, List.foldl_cons, toRatPoly_ofRatPoly]
          exact ih _
    rw [hnormalized 1, normalizedRatFactorFoldl rawFactors.toList]
    simp
  obtain ⟨hnormalizedMonic, hnormalizedAssociated⟩ :=
    factorize_normalized_product integer hintegerNe
  have hrawList : rawFactors.toList =
      (ZPoly.factorize integer).factors.toList.flatMap
        (fun entry => List.replicate entry.2 entry.1) := by
    simp [rawFactors]
  rw [← hrawList] at hnormalizedMonic hnormalizedAssociated
  obtain ⟨unit, hunit⟩ :=
    ZPoly.ratPolyPrimitivePart_rational_associate p
  have hunitNe : unit ≠ 0 := by
    intro hzero
    apply hp
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    rw [hunit, hzero]
    simp
  have hpAssociated : Associated (HexPolyMathlib.toPolynomial p)
      (HexPolyZMathlib.toPolyℚ integer) := by
    have hunitPoly := congrArg HexPolyMathlib.toPolynomial hunit
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly] at hunitPoly
    rw [hunitPoly]
    exact associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr hunitNe.isUnit)
  change factors.foldl
    (fun product factor => product * Factor.toRatPoly factor) 1 = p
  apply (HexPolyMathlib.equiv (R := Rat)).injective
  change HexPolyMathlib.toPolynomial
      (factors.foldl
        (fun product factor => product * Factor.toRatPoly factor) 1) =
    HexPolyMathlib.toPolynomial p
  rw [hfold]
  exact Polynomial.eq_of_monic_of_associated hnormalizedMonic hpMonic
    (hnormalizedAssociated.trans hpAssociated.symm)

/-- For a separable input the executable gcd with the derivative is constant,
so the squarefreeness guard in the rational factorizer passes. -/
theorem gcd_derivative_size_le_one_of_separable
    (p : DensePoly Rat)
    (hseparable : (HexPolyMathlib.toPolynomial p).Separable) :
    (DensePoly.gcd p (DensePoly.derivative p)).size ≤ 1 := by
  let g := DensePoly.gcd p (DensePoly.derivative p)
  let G := EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
    (HexPolyMathlib.toPolynomial p).derivative
  have hassociated : Associated (HexPolyMathlib.toPolynomial g) G := by
    simpa only [g, G, HexPolyMathlib.toPolynomial_derivative] using
      HexPolyMathlib.toPolynomial_gcd_associated p (DensePoly.derivative p)
  have hGunit : IsUnit G := by
    change IsUnit (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
      (HexPolyMathlib.toPolynomial p).derivative)
    rw [EuclideanDomain.gcd_isUnit_iff]
    exact hseparable
  have hgunit : IsUnit (HexPolyMathlib.toPolynomial g) :=
    hassociated.isUnit_iff.mpr hGunit
  rw [HexPolyZMathlib.size_le_one_iff_natDegree_eq_zero]
  exact Polynomial.natDegree_eq_zero_of_isUnit hgunit

/-- The rational base factorizer is total on the separable inputs supplied by
Yun decomposition. -/
theorem factorRat_isSome (input : DensePoly Rat)
    (hseparable : (HexPolyMathlib.toPolynomial input).Separable) :
    (Factor.factorRat? input).isSome := by
  have hinputNe : input ≠ 0 := by
    intro hzero
    apply hseparable.ne_zero
    rw [hzero, HexPolyMathlib.toPolynomial_zero]
  have hinputZero : input.isZero = false := by
    rw [DensePoly.isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero fun hsize =>
      hinputNe ((DensePoly.size_eq_zero_iff input).mp hsize)
  let p := DensePoly.scale input.leadingCoeff⁻¹ input
  have hpNe : p ≠ 0 := by
    intro hzero
    have hpoly := congrArg HexPolyMathlib.toPolynomial hzero
    change HexPolyMathlib.toPolynomial
        (DensePoly.scale input.leadingCoeff⁻¹ input) =
      HexPolyMathlib.toPolynomial 0 at hpoly
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyMathlib.toPolynomial_zero] at hpoly
    have hleadingNe : input.leadingCoeff ≠ 0 :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size input
        ((DensePoly.isZero_eq_false_iff input).mp hinputZero)
    have hinputPoly : HexPolyMathlib.toPolynomial input = 0 :=
      (mul_eq_zero.mp hpoly).resolve_left
        (Polynomial.C_ne_zero.mpr (inv_ne_zero hleadingNe))
    apply hinputNe
    apply (HexPolyMathlib.equiv (R := Rat)).injective
    change HexPolyMathlib.toPolynomial input =
      HexPolyMathlib.toPolynomial (0 : DensePoly Rat)
    rw [HexPolyMathlib.toPolynomial_zero]
    exact hinputPoly
  have hpZero : p.isZero = false := by
    rw [DensePoly.isZero_eq_false_iff]
    exact Nat.pos_of_ne_zero fun hsize =>
      hpNe ((DensePoly.size_eq_zero_iff p).mp hsize)
  have hpMonic : (HexPolyMathlib.toPolynomial p).Monic := by
    exact toPolynomial_scale_inv_monic input hinputNe
  have hpSeparable : (HexPolyMathlib.toPolynomial p).Separable := by
    exact (scale_inv_associated input hinputNe).symm.separable hseparable
  have hgcd := gcd_derivative_size_le_one_of_separable p hpSeparable
  have hproduct := factorRat_product p hpNe hpMonic
  dsimp only at hproduct
  simp only [Factor.factorRat?, hinputZero, Bool.false_eq_true, ite_false]
  rw [show DensePoly.scale input.leadingCoeff⁻¹ input = p from rfl]
  simp only [hpZero, hgcd, ite_eq_left]
  rw [hproduct]
  simp

end Hex.NumberTower
