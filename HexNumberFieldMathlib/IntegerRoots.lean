/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Exact

public section

/-!
# Roots of integer polynomials

`ZPoly.algebraicRoots` always succeeds, and its output is exactly the set of
complex roots of the polynomial, each once. The reality test `isReal` is
exact at the stored separation precision, and `approx` returns a ball around
the represented value.
-/

namespace Hex

open HexRootsMathlib

namespace ZPoly

/-- The squarefree primitive part of a polynomial of positive degree has
positive degree. -/
private theorem squareFreeCore_degree_pos (p : ZPoly)
    (h0 : ¬ p.degree?.getD 0 = 0) :
    0 < (ZPoly.squareFreeCore p).degree?.getD 0 := by
  have hpne : p ≠ 0 := by
    intro hp
    apply h0
    simp [hp]
  have hcne : ZPoly.squareFreeCore p ≠ 0 := ZPoly.squareFreeCore_ne_zero p hpne
  have hdeg : 0 < (toPolyℂ p).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, natDegree_toPolyℂ]
    exact Nat.pos_of_ne_zero h0
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hcore : (toPolyℂ (ZPoly.squareFreeCore p)).IsRoot z :=
    HexPolyZMathlib.isRoot_squareFreeCore hpne hz
  by_contra hn
  have hsize : (ZPoly.squareFreeCore p).size ≠ 0 := by
    intro hsize
    exact hcne ((DensePoly.size_eq_zero_iff _).mp hsize)
  exact not_isRoot_of_degree_not_pos (ZPoly.squareFreeCore p) hsize hn z hcore

/-- The positive-degree branch of `algebraicRoots?`, with its certificate
hypotheses named. -/
private theorem algebraicRoots?_eq_of_pos (p : ZPoly)
    (h0 : ¬ p.degree?.getD 0 = 0)
    (hprim : ZPoly.content (ZPoly.squareFreeCore p) = 1)
    (hpos : 0 < (ZPoly.squareFreeCore p).leadingCoeff)
    (hdeg : 0 < (ZPoly.squareFreeCore p).degree?.getD 0)
    (hsimple : HasOnlySimpleRoots (ZPoly.squareFreeCore p)) :
    ZPoly.algebraicRoots? p =
      (isolate (ZPoly.squareFreeCore p) hsimple
          (separationDepth (ZPoly.squareFreeCore p) : Int)).bind fun isolations =>
        (isolations.mapM DyadicRootIsolation.toRefined?).bind fun refined =>
          (refined.mapM fun rep =>
              (AlgebraicRoot.ofRefined (ZPoly.squareFreeCore p) hprim hpos hdeg
                hsimple rep).exact?).bind fun roots =>
            some (roots.toList.mergeSort AlgebraicNumber.rootLe).toArray := by
  unfold ZPoly.algebraicRoots?
  rw [ite_eq_right h0]
  dsimp only
  rw [dite_eq_left hprim, dite_eq_left hpos, dite_eq_left hdeg, dite_eq_left hsimple]
  rfl

/-- The certificate hypotheses of the positive-degree branch all hold. -/
private theorem squareFreeCore_hypotheses (p : ZPoly)
    (h0 : ¬ p.degree?.getD 0 = 0) :
    ZPoly.content (ZPoly.squareFreeCore p) = 1 ∧
      0 < (ZPoly.squareFreeCore p).leadingCoeff ∧
      0 < (ZPoly.squareFreeCore p).degree?.getD 0 ∧
      HasOnlySimpleRoots (ZPoly.squareFreeCore p) := by
  have hpne : p ≠ 0 := by
    intro hp
    apply h0
    simp [hp]
  refine ⟨?_, ZPoly.leadingCoeff_squareFreeCore_pos p hpne,
    squareFreeCore_degree_pos p h0, ?_⟩
  · simpa [ZPoly.Primitive] using ZPoly.squareFreeCore_primitive p hpne
  · simpa [HasOnlySimpleRoots] using ZPoly.squareFreeRat_squareFreeCore p hpne

/-- The root-set computation always produces a certificate. -/
theorem algebraicRoots?_isSome (p : ZPoly) : (ZPoly.algebraicRoots? p).isSome := by
  by_cases h0 : p.degree?.getD 0 = 0
  · unfold ZPoly.algebraicRoots?
    rw [ite_eq_left h0]
    rfl
  · obtain ⟨hprim, hpos, hdeg, hsimple⟩ := squareFreeCore_hypotheses p h0
    have hpne : p ≠ 0 := by
      intro hp
      apply h0
      simp [hp]
    have hcne : ZPoly.squareFreeCore p ≠ 0 := ZPoly.squareFreeCore_ne_zero p hpne
    rw [algebraicRoots?_eq_of_pos p h0 hprim hpos hdeg hsimple]
    have hisolateSome := isolate_isSome (ZPoly.squareFreeCore p) hsimple hcne
      (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet
    obtain ⟨isolations, hisolate⟩ := Option.isSome_iff_exists.mp hisolateSome
    rw [hisolate, Option.bind_some]
    have hmapSome := array_mapM_isSome (xs := isolations)
      (f := DyadicRootIsolation.toRefined?) (fun iso hiso => by
        unfold DyadicRootIsolation.toRefined?
        rw [dite_eq_left (isolate_refined (ZPoly.squareFreeCore p) hsimple
          (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet hisolate
          iso hiso)]
        rfl)
    obtain ⟨refined, hmap⟩ := Option.isSome_iff_exists.mp hmapSome
    rw [hmap, Option.bind_some]
    have hexactSome := array_mapM_isSome (xs := refined)
      (f := fun rep => (AlgebraicRoot.ofRefined (ZPoly.squareFreeCore p) hprim hpos
        hdeg hsimple rep).exact?)
      (fun rep _ => AlgebraicRoot.exact?_isSome _)
    obtain ⟨roots, hroots⟩ := Option.isSome_iff_exists.mp hexactSome
    rw [hroots, Option.bind_some]
    rfl

/-- The total wrapper is the checked computation. -/
theorem algebraicRoots?_eq (p : ZPoly) :
    ZPoly.algebraicRoots? p = some (ZPoly.algebraicRoots p) := by
  obtain ⟨roots, hroots⟩ := Option.isSome_iff_exists.mp (algebraicRoots?_isSome p)
  rw [ZPoly.algebraicRoots, hroots]
  rfl

/-- A root of the squarefree primitive part of a nonzero polynomial is a root
of the polynomial. -/
private theorem isRoot_of_isRoot_squareFreeCore {p : ZPoly} (hp : p ≠ 0) {z : ℂ}
    (hz : (toPolyℂ (ZPoly.squareFreeCore p)).IsRoot z) :
    (toPolyℂ p).IsRoot z := by
  obtain ⟨ε, _, hre⟩ := ZPoly.primitiveSquareFreeDecomposition_reassembly_signed p hp
  have hcore : (ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore =
      ZPoly.squareFreeCore p := rfl
  have hfull := HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart p
  have hprim : HexPolyZMathlib.toPolynomial (ZPoly.primitivePart p) =
      Polynomial.C ε *
        (HexPolyZMathlib.toPolynomial (ZPoly.squareFreeCore p) *
          HexPolyZMathlib.toPolynomial
            (ZPoly.primitiveSquareFreeDecomposition p).repeatedPart) := by
    rw [← hre, ← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_C, HexPolyZMathlib.toPolynomial_mul, hcore]
  simp only [Polynomial.IsRoot.def, toPolyℂ, Polynomial.eval_map] at hz ⊢
  rw [hfull, hprim]
  simp only [Polynomial.eval₂_mul, hz, mul_zero, zero_mul]

/-- The output lists exactly the roots of a nonzero polynomial. -/
theorem mem_algebraicRoots_iff (p : ZPoly) (hp : p ≠ 0) (z : ℂ) :
    (∃ a ∈ (ZPoly.algebraicRoots p).toList, a.toComplex = z) ↔
      (toPolyℂ p).IsRoot z := by
  by_cases h0 : p.degree?.getD 0 = 0
  · have hroots : ZPoly.algebraicRoots p = #[] := by
      have h := algebraicRoots?_eq p
      unfold ZPoly.algebraicRoots? at h
      rw [ite_eq_left h0] at h
      exact (Option.some.inj h).symm
    have hsize : p.size ≠ 0 := by
      intro hsize
      exact hp ((DensePoly.size_eq_zero_iff _).mp hsize)
    constructor
    · rintro ⟨a, ha, _⟩
      simp [hroots] at ha
    · intro hz
      exact absurd hz (not_isRoot_of_degree_not_pos p hsize (by omega) z)
  · obtain ⟨hprim, hpos, hdeg, hsimple⟩ := squareFreeCore_hypotheses p h0
    have hcne : ZPoly.squareFreeCore p ≠ 0 := ZPoly.squareFreeCore_ne_zero p hp
    have heq := algebraicRoots?_eq p
    rw [algebraicRoots?_eq_of_pos p h0 hprim hpos hdeg hsimple] at heq
    have hisolateSome := isolate_isSome (ZPoly.squareFreeCore p) hsimple hcne
      (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet
    obtain ⟨isolations, hisolate⟩ := Option.isSome_iff_exists.mp hisolateSome
    rw [hisolate, Option.bind_some] at heq
    have hmapSome := array_mapM_isSome (xs := isolations)
      (f := DyadicRootIsolation.toRefined?) (fun iso hiso => by
        unfold DyadicRootIsolation.toRefined?
        rw [dite_eq_left (isolate_refined (ZPoly.squareFreeCore p) hsimple
          (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet hisolate
          iso hiso)]
        rfl)
    obtain ⟨refined, hmap⟩ := Option.isSome_iff_exists.mp hmapSome
    rw [hmap, Option.bind_some] at heq
    have hexactSome := array_mapM_isSome (xs := refined)
      (f := fun rep => (AlgebraicRoot.ofRefined (ZPoly.squareFreeCore p) hprim hpos
        hdeg hsimple rep).exact?)
      (fun rep _ => AlgebraicRoot.exact?_isSome _)
    obtain ⟨roots, hroots⟩ := Option.isSome_iff_exists.mp hexactSome
    rw [hroots, Option.bind_some] at heq
    have hout : ZPoly.algebraicRoots p =
        (roots.toList.mergeSort AlgebraicNumber.rootLe).toArray :=
      (Option.some.inj heq).symm
    obtain ⟨hsizeIso, hgetIso⟩ := array_mapM_some_get hmap
    obtain ⟨hsizeRoots, hgetRoots⟩ := array_mapM_some_get hroots
    -- Each refined isolation keeps its atom.
    have hraw : ∀ (i : Nat) (hi : i < isolations.size) (hj : i < refined.size),
        refined[i].1 = isolations[i] := by
      intro i hi hj
      have hto := hgetIso i hi hj
      rw [DyadicRootIsolation.toRefined?] at hto
      split at hto
      · exact (congrArg Subtype.val (Option.some.inj hto)).symm
      · exact absurd hto (by simp)
    -- Each output value is the root of its atom.
    have hvalue : ∀ (i : Nat) (hi : i < refined.size) (hj : i < roots.size),
        roots[i].toComplex = RefinedIsolation.root refined[i] := by
      intro i hi hj
      have h := hgetRoots i hi hj
      exact AlgebraicRoot.exact?_sound
        (AlgebraicRoot.ofRefined (ZPoly.squareFreeCore p) hprim hpos hdeg hsimple
          refined[i]) h
    rw [hout]
    simp only [List.mem_mergeSort]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨i, hi, hai⟩ := List.mem_iff_getElem.mp ha
      rw [Array.getElem_toList] at hai
      have hi' : i < roots.size := by simpa using hi
      have hi'' : i < refined.size := by omega
      rw [← hai, hvalue i hi'' hi']
      exact isRoot_of_isRoot_squareFreeCore hp (RefinedIsolation.isRoot refined[i])
    · intro hz
      have hcoreRoot : (toPolyℂ (ZPoly.squareFreeCore p)).IsRoot z :=
        HexPolyZMathlib.isRoot_squareFreeCore hp hz
      obtain ⟨iso, hiso, hisoRoot⟩ := isolate_root_mem_of_pos (ZPoly.squareFreeCore p)
        hsimple (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet hdeg
        hisolate hcoreRoot
      obtain ⟨i, hi, hidx⟩ := List.mem_iff_getElem.mp hiso
      rw [Array.getElem_toList] at hidx
      have hi' : i < isolations.size := by simpa using hi
      have hj : i < refined.size := by omega
      have hk : i < roots.size := by omega
      refine ⟨roots[i], ?_, ?_⟩
      · exact List.mem_iff_getElem.mpr ⟨i, by simpa using hk, by simp⟩
      · rw [hvalue i hj hk, ← hisoRoot, ← hidx]
        show (DyadicRootIsolation.sound refined[i].1).choose =
          (DyadicRootIsolation.sound isolations[i]).choose
        rw [hraw i hi' hj]

/-- The output has no repeated value. -/
theorem algebraicRoots_nodup (p : ZPoly) :
    (ZPoly.algebraicRoots p).toList.Nodup := by
  by_cases h0 : p.degree?.getD 0 = 0
  · have hroots : ZPoly.algebraicRoots p = #[] := by
      have h := algebraicRoots?_eq p
      unfold ZPoly.algebraicRoots? at h
      rw [ite_eq_left h0] at h
      exact (Option.some.inj h).symm
    simp [hroots]
  · obtain ⟨hprim, hpos, hdeg, hsimple⟩ := squareFreeCore_hypotheses p h0
    have hpne : p ≠ 0 := by
      intro hp
      apply h0
      simp [hp]
    have hcne : ZPoly.squareFreeCore p ≠ 0 := ZPoly.squareFreeCore_ne_zero p hpne
    have heq := algebraicRoots?_eq p
    rw [algebraicRoots?_eq_of_pos p h0 hprim hpos hdeg hsimple] at heq
    have hisolateSome := isolate_isSome (ZPoly.squareFreeCore p) hsimple hcne
      (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet
    obtain ⟨isolations, hisolate⟩ := Option.isSome_iff_exists.mp hisolateSome
    rw [hisolate, Option.bind_some] at heq
    have hmapSome := array_mapM_isSome (xs := isolations)
      (f := DyadicRootIsolation.toRefined?) (fun iso hiso => by
        unfold DyadicRootIsolation.toRefined?
        rw [dite_eq_left (isolate_refined (ZPoly.squareFreeCore p) hsimple
          (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet hisolate
          iso hiso)]
        rfl)
    obtain ⟨refined, hmap⟩ := Option.isSome_iff_exists.mp hmapSome
    rw [hmap, Option.bind_some] at heq
    have hexactSome := array_mapM_isSome (xs := refined)
      (f := fun rep => (AlgebraicRoot.ofRefined (ZPoly.squareFreeCore p) hprim hpos
        hdeg hsimple rep).exact?)
      (fun rep _ => AlgebraicRoot.exact?_isSome _)
    obtain ⟨roots, hroots⟩ := Option.isSome_iff_exists.mp hexactSome
    rw [hroots, Option.bind_some] at heq
    have hout : ZPoly.algebraicRoots p =
        (roots.toList.mergeSort AlgebraicNumber.rootLe).toArray :=
      (Option.some.inj heq).symm
    obtain ⟨hsizeIso, hgetIso⟩ := array_mapM_some_get hmap
    obtain ⟨hsizeRoots, hgetRoots⟩ := array_mapM_some_get hroots
    have hraw : ∀ (i : Nat) (hi : i < isolations.size) (hj : i < refined.size),
        refined[i].1 = isolations[i] := by
      intro i hi hj
      have hto := hgetIso i hi hj
      rw [DyadicRootIsolation.toRefined?] at hto
      split at hto
      · exact (congrArg Subtype.val (Option.some.inj hto)).symm
      · exact absurd hto (by simp)
    have hvalue : ∀ (i : Nat) (hi : i < refined.size) (hj : i < roots.size),
        roots[i].toComplex = DyadicRootIsolation.root isolations[i] := by
      intro i hi hj
      have h := hgetRoots i hi hj
      rw [AlgebraicRoot.exact?_sound
        (AlgebraicRoot.ofRefined (ZPoly.squareFreeCore p) hprim hpos hdeg hsimple
          refined[i]) h]
      show (DyadicRootIsolation.sound refined[i].1).choose =
        (DyadicRootIsolation.sound isolations[i]).choose
      rw [hraw i (by omega) hi]
    rw [hout, List.toList_toArray, (List.mergeSort_perm _ _).nodup_iff,
      List.nodup_iff_injective_get]
    intro i j hij
    have hi : i.1 < roots.size := by simp
    have hj : j.1 < roots.size := by simp
    by_contra hne
    have hne' : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
    have hroot := isolate_roots_ne (ZPoly.squareFreeCore p) hsimple
      (separationDepth (ZPoly.squareFreeCore p) : Int) .nkThenPellet hisolate
      (i := i.1) (j := j.1) (by omega) (by omega) hne'
    have hij' : roots[i.1].toComplex = roots[j.1].toComplex := by
      simp only [List.get_eq_getElem, Array.getElem_toList] at hij
      rw [hij]
    rw [hvalue i.1 (by omega) hi, hvalue j.1 (by omega) hj] at hij'
    exact hroot hij'

end ZPoly

namespace AlgebraicNumber

/-- The fixed-field coordinates of a canonical number evaluate to its value. -/
theorem toQAdjoin_toComplex (a : AlgebraicNumber) :
    PolyQuot.toComplex a.toQAdjoin a.rep a.rep_mk = a.toComplex := by
  unfold PolyQuot.toComplex AlgebraicNumber.toQAdjoin
  show Polynomial.eval₂ (algebraMap ℚ ℂ) a.rep.root
    (HexPolyMathlib.toPolynomial (PolyQuot.reduceCoeffs a.p (DensePoly.ofList [0, 1]))) =
      a.toComplex
  rw [PolyQuot.eval_reduceCoeffs]
  have hX : HexPolyMathlib.toPolynomial (DensePoly.ofList ([0, 1] : List Rat)) =
      Polynomial.X := by
    ext n
    rw [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_X]
    simp only [DensePoly.coeff_ofList]
    rcases n with _ | _ | n <;> simp [List.getD]; rfl
  rw [hX, Polynomial.eval₂_X]
  rfl

/-- The approximation ball contains the represented value. -/
theorem approx_mem (a : AlgebraicNumber) (prec : Int) :
    a.toComplex ∈ (a.approx prec).set := by
  have h := PolyQuot.approx_sound a.toQAdjoin a.rep a.rep_mk prec
  rw [toQAdjoin_toComplex] at h
  exact h

/-- The approximation ball has the requested radius. -/
theorem approx_radius (a : AlgebraicNumber) (prec : Int) :
    (a.approx prec).realRadius ≤ (2 : ℝ) ^ (-prec) :=
  PolyQuot.approx_radius a.toQAdjoin a.rep a.rep_mk prec

/-- Complex roots of an integer polynomial are closed under conjugation. -/
theorem isRoot_conj {p : ZPoly} {z : ℂ} (hz : (toPolyℂ p).IsRoot z) :
    (toPolyℂ p).IsRoot (starRingEnd ℂ z) := by
  simp only [Polynomial.IsRoot.def, toPolyℂ, Polynomial.eval_map] at hz ⊢
  have hcomp : (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  rw [← hcomp, ← Polynomial.hom_eval₂, hz, map_zero]

/-- The imaginary part of a stored isolation's centre. -/
private theorem center_im (s : DyadicSquare) :
    (HexRootsMathlib.DyadicSquare.center s).im = Dyadic.toReal s.im := by
  simp [HexRootsMathlib.DyadicSquare.center_eq, Hex.DyadicSquare.center]

/-- The reality test is exact at the stored separation precision. -/
theorem isReal_iff (a : AlgebraicNumber) : a.isReal = true ↔ a.toComplex.im = 0 := by
  have hpne : a.p ≠ 0 := RefinedIsolation.poly_ne_zero a.rep
  set s := a.rep.1.square with hs
  have hmem : a.toComplex ∈ DyadicSquare.closedDisc s :=
    RefinedIsolation.root_mem_closedDisc a.rep
  have hdist : dist a.toComplex (HexRootsMathlib.DyadicSquare.center s) ≤
      DyadicSquare.radius s := by
    simpa only [DyadicSquare.closedDisc, Metric.mem_closedBall] using hmem
  have hradiusHi : DyadicSquare.radius s < Dyadic.toReal s.radiusHi := by
    rw [DyadicSquare.radius_eq, DyadicSquare.radiusHi_eq, DyadicSquare.halfWidth_eq]
    exact mul_lt_mul_of_pos_left sqrt_two_lt_sqrt2Hi (zpow_pos (by norm_num) _)
  have himDist : |a.toComplex.im - Dyadic.toReal s.im| ≤ DyadicSquare.radius s := by
    have h := Complex.abs_im_le_norm (a.toComplex - HexRootsMathlib.DyadicSquare.center s)
    rw [Complex.sub_im, center_im] at h
    rw [dist_eq_norm] at hdist
    exact h.trans hdist
  have hHiSep : Dyadic.toReal s.radiusHi ≤
      (2 : ℝ) ^ (-(mahlerPrec a.p : ℤ)) * (1449 / 1024 : ℝ) := by
    rw [DyadicSquare.radiusHi_eq, DyadicSquare.halfWidth_eq]
    have hsqrt : Dyadic.toReal Hex.sqrt2Hi = (1449 / 1024 : ℝ) := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    rw [hsqrt]
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hprop := a.rep.property
    rw [← hs] at hprop
    omega
  unfold AlgebraicNumber.isReal DyadicSquare.meetsRealAxis
  rw [← hs]
  simp only [Bool.and_eq_true, decide_eq_true_eq, ← Dyadic.toReal_le_toReal_iff,
    Dyadic.toReal_neg]
  constructor
  · rintro ⟨hlo, hhi⟩
    by_contra hne
    have hconj := isRoot_conj (RefinedIsolation.isRoot a.rep)
    have hne' : a.toComplex ≠ starRingEnd ℂ a.toComplex := by
      intro h
      exact hne (Complex.conj_eq_iff_im.mp h.symm)
    have hsep := mahlerPrec_separates a.p hpne a.toComplex (starRingEnd ℂ a.toComplex)
      (RefinedIsolation.isRoot a.rep) hconj hne'
    rw [Complex.sub_conj, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_mul, abs_two] at hsep
    have himLarge : 2 * Dyadic.toReal s.radiusHi < |a.toComplex.im| := by
      linarith
    have hcenter : |Dyadic.toReal s.im| ≤ Dyadic.toReal s.radiusHi := abs_le.mpr ⟨hlo, hhi⟩
    have htri := abs_sub_abs_le_abs_sub a.toComplex.im (Dyadic.toReal s.im)
    linarith
  · intro him
    have : |Dyadic.toReal s.im| ≤ DyadicSquare.radius s := by
      simpa [him] using himDist
    exact abs_le.mp (this.trans hradiusHi.le)

end AlgebraicNumber

/--
info: 'Hex.ZPoly.algebraicRoots?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZPoly.algebraicRoots?_isSome

/--
info: 'Hex.ZPoly.mem_algebraicRoots_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZPoly.mem_algebraicRoots_iff

/--
info: 'Hex.ZPoly.algebraicRoots_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ZPoly.algebraicRoots_nodup

/--
info: 'Hex.AlgebraicNumber.isReal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicNumber.isReal_iff

/--
info: 'Hex.AlgebraicNumber.approx_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicNumber.approx_mem

end Hex
