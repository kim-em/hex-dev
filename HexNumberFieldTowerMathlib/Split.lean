/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Adjoin

public section

/-!
# Correctness of splitting towers

The input leading coefficient supplies the scalar omitted from the compact
runtime root array.  Thus the soundness predicate reconstructs nonmonic inputs
without adding redundant data to {name}`Hex.NumberTower.Splitting`.
-/

namespace Hex.NumberTower

namespace Norm

private theorem oneLevel_isRoot (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (z : ℂ)
    (hroot : (rawPolynomial (level :: lower)
      (Factor.rawPoly (level :: lower) f)).IsRoot z) :
    (rawPolynomial lower
      (Factor.rawPoly lower (oneLevel level lower f 0))).IsRoot z := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  letI : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  letI : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  have hdvd := shifted_dvd_norm level lower hvalid hinjectiveTop f 0
  have hdvdComplex := Polynomial.map_dvd
    (LevelSemantics.coeffHom (level :: lower) hvalid hinjectiveTop hinvTop)
    hdvd
  have hhom :
      (LevelSemantics.coeffHom (level :: lower) hvalid hinjectiveTop hinvTop).comp
          (lowerHom level lower hvalid hinjectiveTop) =
        LevelSemantics.coeffHom lower hvalid.2.2 hinjectiveLower hinvLower := by
    ext a
    change LevelSemantics.coeffDenote (level :: lower)
        (lowerHom level lower hvalid hinjectiveTop a) =
      LevelSemantics.coeffDenote lower a
    rw [lowerHom_apply, LevelSemantics.coeffDenote_lift level lower
      (Nat.zero_lt_of_lt hvalid.1.1)]
  rw [toPolynomial_shiftTop_zero level lower hvalid hinjectiveTop,
    Polynomial.map_map, hhom,
    ← rawPolynomial_eq_map (level :: lower) hvalid hinjectiveTop hinvTop,
    ← rawPolynomial_eq_map lower hvalid.2.2 hinjectiveLower hinvLower]
      at hdvdComplex
  exact hroot.dvd hdvdComplex

private theorem iterated_isRoot (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) (z : ℂ)
    (hroot : (rawPolynomial levels
      (Factor.rawPoly levels f)).IsRoot z) :
    (rawPolynomial []
      (Factor.rawPoly [] (iterated levels f))).IsRoot z := by
  induction levels generalizing f with
  | nil => simpa [iterated] using hroot
  | cons level lower ih =>
      apply ih hvalid.2.2
        (hinjective.tail level lower hvalid.1.1)
      exact oneLevel_isRoot level lower hvalid hinjective f z hroot

private theorem basePolynomial (f : Array (Array Rat)) :
    rawPolynomial [] (Factor.rawPoly [] f) =
      (HexPolyMathlib.toPolynomial (Factor.toRatPoly f)).map
        (algebraMap Rat ℂ) := by
  letI : Field (Arithmetic.Coeff []) := LevelSemantics.coeffFieldNil
  have hvalidNil : LevelsValid [] := by exact trivial
  have hhom :
      (algebraMap Rat ℂ).comp LevelSemantics.coeffRatEquiv.toRingHom =
        LevelSemantics.coeffHom [] hvalidNil
          LevelSemantics.DenoteInjective.nil
          LevelSemantics.coeffDenote_inv_nil := by
    ext a
    rw [← LevelSemantics.coeff_ofData_data [] a, RingHom.comp_apply]
    change ((LevelSemantics.coeffRatEquiv
        (Arithmetic.Coeff.ofData [] a.data) : Rat) : ℂ) = _
    rw [LevelSemantics.coeffRatEquiv_ofData]
    change ((a.data.getD 0 0 : Rat) : ℂ) =
      LevelSemantics.coeffDenote [] (Arithmetic.Coeff.ofData [] a.data)
    simp [LevelSemantics.coeffDenote, Arithmetic.Coeff.ofData,
      LevelSemantics.denote, Arithmetic.fixedCoeffs, levelsDim, Array.getD]
  rw [rawPolynomial_eq_map [] hvalidNil LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil,
    ← hhom, ← Polynomial.map_map, LevelSemantics.map_rawPoly_nil]

/-- Every root in the fixed tower embedding remains a root of the absolute
iterated norm. -/
theorem iterated_isRoot_toRat (T : NumberTower) (f : Poly T) (z : ℂ)
    (hroot : (T.toPolynomial f).IsRoot z) :
    ((HexPolyMathlib.toPolynomial
      (Factor.toRatPoly (iterated T.levels.toList
        (f.toArray.map coeffs)))).map (algebraMap Rat ℂ)).IsRoot z := by
  have hraw : (rawPolynomial T.levels.toList
      (Factor.rawPoly T.levels.toList
        (f.toArray.map coeffs))).IsRoot z := by
    rwa [rawPolynomial_rawPoly]
  have hiterated := iterated_isRoot T.levels.toList T.valid
    (coeffDenote_injective T) (f.toArray.map coeffs) z hraw
  rwa [basePolynomial] at hiterated

private theorem toRatPoly_ne_zero (f : Array (Array Rat))
    (hf : Factor.rawPoly [] f ≠ 0) : Factor.toRatPoly f ≠ 0 := by
  letI : Field (Arithmetic.Coeff []) := LevelSemantics.coeffFieldNil
  intro hzero
  have hmap := LevelSemantics.map_rawPoly_nil f
  rw [hzero, HexPolyMathlib.toPolynomial_zero] at hmap
  have hrawPoly : HexPolyMathlib.toPolynomial (Factor.rawPoly [] f) = 0 :=
    (Polynomial.map_eq_zero_iff
      LevelSemantics.coeffRatEquiv.injective).mp hmap
  apply hf
  exact (HexPolyMathlib.equiv
    (R := Arithmetic.Coeff [])).injective hrawPoly

end Norm

private theorem rawPoly_ne_zero (T : NumberTower) (f : Poly T) (hf : f ≠ 0) :
    Factor.rawPoly T.levels.toList (f.toArray.map coeffs) ≠ 0 := by
  intro hzero
  apply hf
  apply toPolynomial_injective T
  rw [← rawPolynomial_rawPoly T f, hzero, Norm.rawPolynomial_zero,
    toPolynomial_zero]

private theorem primitivePart_isRoot (p : DensePoly Rat) (hp : p ≠ 0)
    {z : ℂ}
    (hz : ((HexPolyMathlib.toPolynomial p).map
      (algebraMap Rat ℂ)).IsRoot z) :
    (HexRootsMathlib.toPolyℂ (ZPoly.ratPolyPrimitivePart p)).IsRoot z := by
  obtain ⟨unit, hunit⟩ := ZPoly.ratPolyPrimitivePart_rational_associate p
  have hunitNe : unit ≠ 0 := by
    intro hzero
    apply hp
    rw [hunit, hzero]
    simp
  have hpoly := congrArg HexPolyMathlib.toPolynomial hunit
  rw [HexPolyMathlib.toPolynomial_scale,
    HexPolyZMathlib.toPolynomial_toRatPoly] at hpoly
  have hpolyComplex := congrArg
    (fun q : Polynomial Rat => q.map (algebraMap Rat ℂ)) hpoly
  have hcomp : (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
      Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hcomp]
      at hpolyComplex
  rw [hpolyComplex] at hz
  change Polynomial.eval z
      (Polynomial.C ((unit : Rat) : ℂ) *
        HexRootsMathlib.toPolyℂ (ZPoly.ratPolyPrimitivePart p)) = 0 at hz
  rw [Polynomial.eval_mul, Polynomial.eval_C] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hunitNe)

private theorem retainRoots?_isSome (T : NumberTower) (f : Poly T) :
    ∀ candidates, (retainRoots? T f candidates).isSome := by
  intro candidates
  induction candidates with
  | nil => rfl
  | cons candidate candidates ih =>
      obtain ⟨keep, hkeep⟩ := Option.isSome_iff_exists.mp
        (Evaluation.vanishesAt?_isSome T f candidate)
      obtain ⟨retained, hretained⟩ := Option.isSome_iff_exists.mp ih
      rw [retainRoots?, hkeep, hretained]
      cases keep <;> rfl

private theorem retainRoots?_sound (T : NumberTower) (f : Poly T) :
    ∀ candidates retained,
      retainRoots? T f candidates = some retained →
      ∀ candidate ∈ retained,
        Evaluation.vanishesAt? T f candidate = some true := by
  intro candidates
  induction candidates with
  | nil =>
      intro retained hrun candidate hcandidate
      simp [retainRoots?] at hrun
      subst retained
      simp at hcandidate
  | cons head tail ih =>
      intro retained hrun candidate hcandidate
      obtain ⟨keep, hkeep⟩ := Option.isSome_iff_exists.mp
        (Evaluation.vanishesAt?_isSome T f head)
      obtain ⟨tailRetained, htail⟩ := Option.isSome_iff_exists.mp
        (retainRoots?_isSome T f tail)
      cases keep with
      | false =>
          have hretained : tailRetained = retained := by
            simpa [retainRoots?, hkeep, htail] using hrun
          exact ih tailRetained htail candidate (by simpa [hretained] using hcandidate)
      | true =>
          have hretained : head :: tailRetained = retained := by
            simpa [retainRoots?, hkeep, htail] using hrun
          rw [← hretained] at hcandidate
          rcases List.mem_cons.mp hcandidate with hcandidate | hcandidate
          · subst candidate
            exact hkeep
          · exact ih tailRetained htail candidate hcandidate

private theorem retainRoots?_complete (T : NumberTower) (f : Poly T) :
    ∀ candidates candidate retained,
      candidate ∈ candidates →
      Evaluation.vanishesAt? T f candidate = some true →
      retainRoots? T f candidates = some retained →
      candidate ∈ retained := by
  intro candidates
  induction candidates with
  | nil => simp
  | cons head tail ih =>
      intro candidate retained hcandidate htrue hrun
      obtain ⟨keep, hkeep⟩ := Option.isSome_iff_exists.mp
        (Evaluation.vanishesAt?_isSome T f head)
      obtain ⟨tailRetained, htail⟩ := Option.isSome_iff_exists.mp
        (retainRoots?_isSome T f tail)
      rcases List.mem_cons.mp hcandidate with hcandidate | hcandidate
      · subst candidate
        have hkeepTrue : keep = true := by simpa [hkeep] using htrue
        subst keep
        have hretained : head :: tailRetained = retained := by
          simpa [retainRoots?, hkeep, htail] using hrun
        rw [← hretained]
        simp
      · cases keep with
        | false =>
            have hretained : tailRetained = retained := by
              simpa [retainRoots?, hkeep, htail] using hrun
            simpa [← hretained] using
              ih candidate tailRetained hcandidate htrue htail
        | true =>
            have hretained : head :: tailRetained = retained := by
              simpa [retainRoots?, hkeep, htail] using hrun
            rw [← hretained]
            exact List.mem_cons_of_mem head
              (ih candidate tailRetained hcandidate htrue htail)

/-- A root returned by the absolute eliminant filter is a root of the input
tower polynomial in the fixed embedding. -/
theorem factorRoot?_sound (T : NumberTower) (f : Poly T)
    {candidate : AlgebraicRoot} (h : factorRoot? T f = some candidate) :
    Polynomial.eval candidate.toComplex (T.toPolynomial f) = 0 := by
  unfold factorRoot? at h
  dsimp only at h
  split at h
  next hprim =>
    split at h
    next hpos =>
      split at h
      next hdegree =>
        split at h
        next hsimple =>
          cases hisolate : isolate (factorEliminant T f) hsimple
              (separationDepth (factorEliminant T f) : Int) with
          | none => simp [hisolate] at h
          | some isolations =>
              rw [hisolate] at h
              simp only [Option.bind_eq_bind, Option.bind_some] at h
              cases hrefined : isolations.mapM
                  DyadicRootIsolation.toRefined? with
              | none => simp [hrefined] at h
              | some refined =>
                  rw [hrefined] at h
                  simp only [Option.bind_some] at h
                  let candidates := refined.toList.map
                    fun rep : RefinedIsolation (factorEliminant T f) =>
                      ({ p := factorEliminant T f
                         prim := hprim
                         pos_lc := hpos
                         pos_degree := hdegree
                         squarefree := hsimple
                         x := SimpleRoot.mk rep
                         rep
                         rep_mk := rfl } : AlgebraicRoot)
                  cases hretained : retainRoots? T f candidates with
                  | none => simp [candidates, hretained] at h
                  | some retained =>
                      rw [show refined.toList.map _ = candidates by rfl,
                        hretained] at h
                      cases retained with
                      | nil => simp at h
                      | cons head tail =>
                          have hhead : head = candidate := by
                            simpa using h
                          subst candidate
                          have htrue := retainRoots?_sound T f candidates
                            (head :: tail) hretained head (by simp)
                          exact (Evaluation.vanishesAt?_eq_some_true_iff
                            T f head).mp htrue
        next hsimple => simp at h
      next hdegree => simp at h
    next hpos => simp at h
  next hprim => simp at h

/-- Every positive-degree tower polynomial supplies an absolute root through
its iterated-norm eliminant. -/
theorem factorRoot?_isSome (T : NumberTower) (f : Poly T)
    (hdegreeF : 0 < f.degree?.getD 0) :
    (factorRoot? T f).isSome := by
  have hf : f ≠ 0 := by
    intro hzero
    subst f
    simp at hdegreeF
  have hraw : Factor.rawPoly T.levels.toList
      (f.toArray.map coeffs) ≠ 0 := rawPoly_ne_zero T f hf
  have hiterated : Factor.rawPoly []
      (Norm.iterated T.levels.toList (f.toArray.map coeffs)) ≠ 0 :=
    Norm.iterated_ne_zero T.levels.toList T.valid
      (coeffDenote_injective T) (f.toArray.map coeffs) hraw
  let absolute := Factor.toRatPoly
    (Norm.iterated T.levels.toList (f.toArray.map coeffs))
  have habsolute : absolute ≠ 0 := by
    exact Norm.toRatPoly_ne_zero
      (Norm.iterated T.levels.toList (f.toArray.map coeffs)) hiterated
  let primitive := ZPoly.ratPolyPrimitivePart absolute
  have hprimitive : primitive ≠ 0 := by
    obtain ⟨unit, hunit⟩ :=
      ZPoly.ratPolyPrimitivePart_rational_associate absolute
    intro hzero
    apply habsolute
    change ZPoly.ratPolyPrimitivePart absolute = 0 at hzero
    rw [hunit, hzero]
    simp
  have hsemanticDegree : 0 < (T.toPolynomial f).natDegree := by
    simpa using hdegreeF
  obtain ⟨z, hz⟩ := Complex.exists_root
    (Polynomial.natDegree_pos_iff_degree_pos.mp hsemanticDegree)
  have habsoluteRoot :
      ((HexPolyMathlib.toPolynomial absolute).map
        (algebraMap Rat ℂ)).IsRoot z := by
    simpa [absolute] using Norm.iterated_isRoot_toRat T f z hz
  have hprimitiveRoot :
      (HexRootsMathlib.toPolyℂ primitive).IsRoot z :=
    primitivePart_isRoot absolute habsolute habsoluteRoot
  have hcoreRoot :
      (HexRootsMathlib.toPolyℂ (factorEliminant T f)).IsRoot z := by
    simpa [factorEliminant, absolute, primitive] using
      HexPolyZMathlib.isRoot_squareFreeCore hprimitive hprimitiveRoot
  have hcoreNe : factorEliminant T f ≠ 0 := by
    simpa [factorEliminant, absolute, primitive] using
      ZPoly.squareFreeCore_ne_zero primitive hprimitive
  have hprim : ZPoly.content (factorEliminant T f) = 1 := by
    simpa [factorEliminant, absolute, primitive, ZPoly.Primitive] using
      ZPoly.squareFreeCore_primitive primitive hprimitive
  have hpos : 0 < (factorEliminant T f).leadingCoeff := by
    simpa [factorEliminant, absolute, primitive] using
      ZPoly.leadingCoeff_squareFreeCore_pos primitive hprimitive
  have hsimple : HasOnlySimpleRoots (factorEliminant T f) := by
    simpa [factorEliminant, absolute, primitive, HasOnlySimpleRoots] using
      ZPoly.squareFreeRat_squareFreeCore primitive hprimitive
  have hcoreSize : (factorEliminant T f).size ≠ 0 := by
    intro hsize
    exact hcoreNe ((DensePoly.size_eq_zero_iff _).mp hsize)
  have hdegree : 0 < (factorEliminant T f).degree?.getD 0 := by
    by_contra hnot
    exact HexRootsMathlib.not_isRoot_of_degree_not_pos
      (factorEliminant T f) hcoreSize hnot z hcoreRoot
  unfold factorRoot?
  dsimp only
  rw [dif_pos hprim, dif_pos hpos, dif_pos hdegree, dif_pos hsimple]
  have hisolateSome := HexRootsMathlib.isolate_isSome
    (factorEliminant T f) hsimple hcoreNe
    (separationDepth (factorEliminant T f) : Int) .nkThenPellet
  cases hisolate : isolate (factorEliminant T f) hsimple
      (separationDepth (factorEliminant T f) : Int) with
  | none => simp [hisolate] at hisolateSome
  | some isolations =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hmapSome := HexRootsMathlib.array_mapM_isSome
        (xs := isolations) (f := DyadicRootIsolation.toRefined?)
        (fun iso hiso => by
          unfold DyadicRootIsolation.toRefined?
          rw [dif_pos (HexRootsMathlib.isolate_refined
            (factorEliminant T f) hsimple
            (separationDepth (factorEliminant T f) : Int)
            .nkThenPellet hisolate iso hiso)]
          rfl)
      cases hrefined : isolations.mapM
          DyadicRootIsolation.toRefined? with
      | none => simp [hrefined] at hmapSome
      | some refined =>
          simp only [Option.bind_some]
          obtain ⟨iso, hiso, hisoRoot⟩ :=
            HexRootsMathlib.isolate_root_mem_of_pos
              (factorEliminant T f) hsimple
              (separationDepth (factorEliminant T f) : Int)
              .nkThenPellet hdegree hisolate hcoreRoot
          obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
          have hi : i < isolations.size := by simpa using hiList
          obtain ⟨hmapSize, hmapGet⟩ :=
            HexRootsMathlib.array_mapM_some_get hrefined
          have hj : i < refined.size := by
            simpa [← hmapSize] using hi
          have hto := hmapGet i hi hj
          have hrawIso : refined[i].1 = isolations[i] := by
            rw [DyadicRootIsolation.toRefined?] at hto
            split at hto
            · exact (congrArg Subtype.val (Option.some.inj hto)).symm
            · simp at hto
          have harrIso : isolations[i] = iso := by
            rw [← hidx]
            exact (Array.getElem_toList hi).symm
          have hrefinedRoot :
              HexRootsMathlib.RefinedIsolation.root refined[i] = z := by
            change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 = z
            rw [hrawIso, harrIso]
            exact hisoRoot
          let candidate : AlgebraicRoot :=
            { p := factorEliminant T f
              prim := hprim
              pos_lc := hpos
              pos_degree := hdegree
              squarefree := hsimple
              x := SimpleRoot.mk refined[i]
              rep := refined[i]
              rep_mk := rfl }
          have hcandidateValue : candidate.toComplex = z :=
            hrefinedRoot
          have hcandidateZero : Polynomial.eval candidate.toComplex
              (T.toPolynomial f) = 0 := by
            rw [hcandidateValue]
            exact hz
          have htrue : Evaluation.vanishesAt? T f candidate = some true :=
            (Evaluation.vanishesAt?_eq_some_true_iff
              T f candidate).mpr hcandidateZero
          let candidates := refined.toList.map
            fun rep : RefinedIsolation (factorEliminant T f) =>
              ({ p := factorEliminant T f
                 prim := hprim
                 pos_lc := hpos
                 pos_degree := hdegree
                 squarefree := hsimple
                 x := SimpleRoot.mk rep
                 rep
                 rep_mk := rfl } : AlgebraicRoot)
          have hcandidateMem : candidate ∈ candidates := by
            apply List.mem_map.mpr
            exact ⟨refined[i], Array.getElem_mem_toList hj, rfl⟩
          obtain ⟨retained, hretained⟩ := Option.isSome_iff_exists.mp
            (retainRoots?_isSome T f candidates)
          have hretainedMem : candidate ∈ retained :=
            retainRoots?_complete T f candidates candidate retained
              hcandidateMem htrue hretained
          cases retained with
          | nil => simp at hretainedMem
          | cons head tail =>
              rw [show refined.toList.map _ = candidates by rfl,
                hretained]
              rfl

private theorem linearRoots?_get {T : NumberTower}
    {factors : Array (Poly T × Nat)} {roots : Array (Elem T × Nat)}
    (h : linearRoots? factors = some roots) :
    factors.size = roots.size ∧
      ∀ (i : Nat) (hi : i < factors.size) (hj : i < roots.size),
        factors[i].1.degree?.getD 0 = 1 ∧
          0 < factors[i].2 ∧
          roots[i] =
            (-(factors[i].1.coeff 0) / factors[i].1.leadingCoeff,
              factors[i].2) := by
  unfold linearRoots? at h
  obtain ⟨hsize, hget⟩ := HexRootsMathlib.array_mapM_some_get h
  refine ⟨hsize, ?_⟩
  intro i hi hj
  have hentry := hget i hi hj
  split at hentry
  next hcondition =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcondition
    exact ⟨hcondition.1, hcondition.2,
      (Option.some.inj hentry).symm⟩
  next hcondition => simp at hentry

private theorem mapPoly_id (T : NumberTower) (f : Poly T) :
    mapPoly id f = f := by
  rw [mapPoly, Array.map_id, DensePoly.ofCoeffs_toArray]

private theorem toPolynomial_mapPoly {T U : NumberTower}
    (embed : Elem T → Elem U)
    (hpreserves : ∀ a, U.toComplex (embed a) = T.toComplex a)
    (f : Poly T) :
    U.toPolynomial (mapPoly embed f) = T.toPolynomial f := by
  ext n
  rw [coeff_toPolynomial, coeff_toPolynomial]
  rw [mapPoly, DensePoly.coeff_ofCoeffs,
    Array.getD_eq_getD_getElem?, Array.getElem?_map]
  by_cases hn : n < f.toArray.size
  · rw [Array.getElem?_eq_getElem hn]
    simp only [Option.map_some, Option.getD_some]
    have hcoeff : f.toArray[n] = f.coeff n :=
      (Array.getElem_eq_getD (xs := f.toArray) (i := n)
        (h := hn) (0 : Elem T)).trans (DensePoly.toArray_getD f n)
    rw [hcoeff, hpreserves]
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt hn)]
    simp only [Option.map_none, Option.getD_none]
    have hzero : f.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (by simpa using Nat.le_of_not_gt hn)
    rw [hzero]
    exact (map_zero U).trans (map_zero T).symm

private theorem mapPoly_comp {T U V : NumberTower}
    (outer : Elem U → Elem V) (inner : Elem T → Elem U)
    (houter : ∀ a, V.toComplex (outer a) = U.toComplex a)
    (hinner : ∀ a, U.toComplex (inner a) = T.toComplex a)
    (f : Poly T) :
    mapPoly outer (mapPoly inner f) = mapPoly (outer ∘ inner) f := by
  apply toPolynomial_injective V
  rw [toPolynomial_mapPoly outer houter,
    toPolynomial_mapPoly inner hinner,
    toPolynomial_mapPoly (outer ∘ inner)]
  intro a
  exact (houter (inner a)).trans (hinner a)

private theorem identity_preserves (T : NumberTower) :
    (Extension.identity T).PreservesEmbedding := by
  intro a
  rfl

private abbrev composeExtension {T : NumberTower} (outer : Extension T)
    (inner : Extension outer.tower) : Extension T :=
  { tower := inner.tower
    embed := fun a => inner.embed (outer.embed a)
    gen := inner.gen
    root := inner.root }

private theorem size_eq_two_of_degree_one {T : NumberTower} (f : Poly T)
    (hdegree : f.degree?.getD 0 = 1) : f.size = 2 := by
  have hpos : 0 < f.size := by
    by_contra hnot
    have hzero : f.size = 0 := by omega
    rw [(DensePoly.degree?_eq_none_iff f).2 hzero] at hdegree
    simp at hdegree
  rw [DensePoly.degree?_eq_some_of_pos_size f hpos] at hdegree
  simp only [Option.getD_some] at hdegree
  omega

private theorem linearFactor_semantic {T : NumberTower} (f : Poly T)
    (hdegree : f.degree?.getD 0 = 1) (hmonic : f.leadingCoeff = 1) :
    T.toPolynomial f = Polynomial.X - Polynomial.C
      (T.toComplex (-f.coeff 0 / f.leadingCoeff)) := by
  have hsize := size_eq_two_of_degree_one f hdegree
  have hcoeffOne : f.coeff 1 = f.leadingCoeff := by
    rw [DensePoly.leadingCoeff_eq_coeff_last f (by omega), hsize]
  have hshape := Polynomial.eq_X_add_C_of_natDegree_le_one
    (p := T.toPolynomial f) (by simpa using hdegree.le)
  rw [coeff_toPolynomial, coeff_toPolynomial, hcoeffOne, hmonic,
    map_one] at hshape
  have hroot : T.toComplex (-f.coeff 0 / f.leadingCoeff) =
      -T.toComplex (f.coeff 0) := by
    rw [map_div, map_neg, hmonic, map_one]
    simp
  rw [hshape, hroot]
  simp

private theorem toPolynomial_linear (T : NumberTower) (root : Elem T) :
    T.toPolynomial (DensePoly.ofCoeffs #[-root, 1]) =
      Polynomial.X - Polynomial.C (T.toComplex root) := by
  ext n
  rw [coeff_toPolynomial, DensePoly.coeff_ofCoeffs]
  cases n with
  | zero => simp [map_neg]
  | succ n =>
      cases n with
      | zero => simp [map_one]
      | succ n =>
          rw [Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none (by simp)]
          simp only [Option.getD_none]
          change T.toComplex (0 : Elem T) = _
          rw [map_zero]
          simp [Polynomial.coeff_X]

private theorem toPolynomial_polyPowSemantic (T : NumberTower)
    (f : Poly T) (n : Nat) :
    T.toPolynomial (Factorization.polyPow f n) =
      T.toPolynomial f ^ n := by
  induction n with
  | zero => simp [Factorization.polyPow]
  | succ n ih =>
      rw [Factorization.polyPow, toPolynomial_mul, ih, pow_succ]

private theorem leadingCoeff_toPolynomial (T : NumberTower) (f : Poly T) :
    (T.toPolynomial f).leadingCoeff = T.toComplex f.leadingCoeff := by
  by_cases hpos : 0 < f.size
  · rw [Polynomial.leadingCoeff, natDegree_toPolynomial,
      DensePoly.degree?_eq_some_of_pos_size f hpos, Option.getD_some,
      coeff_toPolynomial, DensePoly.leadingCoeff_eq_coeff_last f hpos]
  · have hzero : f = 0 :=
      (DensePoly.size_eq_zero_iff f).mp (by omega)
    subst f
    rw [toPolynomial_zero, Polynomial.leadingCoeff_zero,
      DensePoly.leadingCoeff_zero, map_zero]

private theorem leadingCoeff_mapPoly {T U : NumberTower}
    (embed : Elem T → Elem U)
    (hpreserves : ∀ a, U.toComplex (embed a) = T.toComplex a)
    (f : Poly T) :
    (mapPoly embed f).leadingCoeff = embed f.leadingCoeff := by
  apply toComplex_injective U
  rw [← leadingCoeff_toPolynomial,
    toPolynomial_mapPoly embed hpreserves,
    leadingCoeff_toPolynomial, hpreserves]

namespace Roots

/-- Product of the recorded monic linear factors. The `.all` case denotes the
zero polynomial. -/
@[expose]
def linearProduct {T : NumberTower} : Roots T → Poly T
  | .all => 0
  | .finite roots =>
      roots.foldl
        (fun product entry =>
          product * Factorization.polyPow
            (DensePoly.ofCoeffs #[-entry.1, 1]) entry.2)
        1

/-- Every finite root entry has positive multiplicity. -/
def Positive {T : NumberTower} : Roots T → Prop
  | .all => True
  | .finite roots => ∀ entry ∈ roots.toList, 0 < entry.2

/-- A finite root array contains no duplicate tower values. -/
def NoDuplicates {T : NumberTower} : Roots T → Prop
  | .all => True
  | .finite roots =>
      roots.toList.Pairwise fun a b => a.1 ≠ b.1

end Roots

private theorem linearProduct_semantic {T : NumberTower}
    (roots : Array (Elem T × Nat)) :
    T.toPolynomial (Roots.linearProduct (.finite roots)) =
      (roots.toList.map fun entry =>
        (Polynomial.X - Polynomial.C (T.toComplex entry.1)) ^
          entry.2).prod := by
  have fold : ∀ (items : List (Elem T × Nat)) (init : Poly T),
      T.toPolynomial
          (items.foldl (fun product entry =>
            product * Factorization.polyPow
              (DensePoly.ofCoeffs #[-entry.1, 1]) entry.2) init) =
        T.toPolynomial init *
          (items.map fun entry =>
            (Polynomial.X - Polynomial.C (T.toComplex entry.1)) ^
              entry.2).prod := by
    intro items
    induction items with
    | nil => simp
    | cons entry items ih =>
        intro init
        rw [List.foldl_cons, ih, List.map_cons, List.prod_cons,
          toPolynomial_mul, toPolynomial_polyPowSemantic,
          toPolynomial_linear]
        ac_rfl
  rw [Roots.linearProduct, ← Array.foldl_toList, fold]
  simp

private theorem linearProducts_eq {T : NumberTower} {f : Poly T}
    (r : Factorization T f) (hsound : r.Sound)
    {roots : Array (Elem T × Nat)}
    (hlinear : linearRoots? r.factors = some roots) :
    (roots.toList.map fun entry =>
        (Polynomial.X - Polynomial.C (T.toComplex entry.1)) ^
          entry.2).prod =
      (r.factors.toList.map fun factor =>
        T.toPolynomial factor.1 ^ factor.2).prod := by
  obtain ⟨hsize, hget⟩ := linearRoots?_get hlinear
  have harr :
      roots.map (fun entry =>
          (Polynomial.X - Polynomial.C (T.toComplex entry.1)) ^
            entry.2) =
        r.factors.map (fun factor =>
          T.toPolynomial factor.1 ^ factor.2) := by
    apply Array.ext
    · simpa using hsize.symm
    · intro i hiRoots hiFactors
      simp only [Array.getElem_map]
      have hiRoots' : i < roots.size := by simpa using hiRoots
      have hiFactors' : i < r.factors.size := by simpa using hiFactors
      have hentry := hget i hiFactors' hiRoots'
      have hfactor := hsound.2.1 r.factors[i]
        (Array.getElem_mem_toList hiFactors')
      rw [hentry.2.2]
      exact congrArg (fun p : Polynomial ℂ => p ^ r.factors[i].2)
        (linearFactor_semantic r.factors[i].1 hentry.1 hfactor.1).symm
  have hlists := congrArg Array.toList harr
  simpa only [Array.toList_map] using congrArg List.prod hlists

private theorem factorization_scalar_eq_leadingCoeff {T : NumberTower}
    {f : Poly T} (r : Factorization T f) (hsound : r.Sound) :
    r.scalar = f.leadingCoeff := by
  have hmonicFactors : ∀ entry : Poly T × Nat,
      entry ∈ r.factors.toList →
        (T.toPolynomial (entry.1) ^ entry.2).Monic := by
    intro entry hentry
    have hfactor := hsound.2.1 entry hentry
    have hmonic : (T.toPolynomial (entry.1)).Monic := by
      change (T.toPolynomial (entry.1)).leadingCoeff = 1
      rw [leadingCoeff_toPolynomial, hfactor.1, map_one]
    exact hmonic.pow _
  have hproductMonic :
      (r.factors.toList.map fun factor =>
        T.toPolynomial factor.1 ^ factor.2).prod.Monic := by
    have listMonic : ∀ items : List (Poly T × Nat),
        (∀ entry ∈ items,
          (T.toPolynomial entry.1 ^ entry.2).Monic) →
        (items.map fun factor =>
          T.toPolynomial factor.1 ^ factor.2).prod.Monic := by
      intro items
      induction items with
      | nil => simp
      | cons entry entries ih =>
          intro hall
          rw [List.map_cons, List.prod_cons]
          exact (hall entry (by simp)).mul
            (ih (fun tail htail => hall tail (by simp [htail])))
    exact listMonic r.factors.toList hmonicFactors
  have hreconstruct := congrArg T.toPolynomial hsound.1
  rw [semantic_reconstruct] at hreconstruct
  have hlead := congrArg Polynomial.leadingCoeff hreconstruct
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    hproductMonic.leadingCoeff,
    leadingCoeff_toPolynomial, mul_one] at hlead
  exact toComplex_injective T hlead

private theorem linearRoots_positive {T : NumberTower} {f : Poly T}
    (r : Factorization T f) {roots : Array (Elem T × Nat)}
    (hlinear : linearRoots? r.factors = some roots) :
    (Roots.finite roots).Positive := by
  obtain ⟨hsize, hget⟩ := linearRoots?_get hlinear
  intro entry hentry
  obtain ⟨i, hi, hidx⟩ := List.mem_iff_getElem.mp hentry
  have hiRoots : i < roots.size := by simpa using hi
  have hiFactors : i < r.factors.size := by simpa [hsize] using hiRoots
  have hdata := hget i hiFactors hiRoots
  have hroot : roots[i] = entry := by simpa using hidx
  rw [← hroot, hdata.2.2]
  exact hdata.2.1

private theorem linearRoots_nodup {T : NumberTower} {f : Poly T}
    (r : Factorization T f) (hsound : r.Sound)
    {roots : Array (Elem T × Nat)}
    (hlinear : linearRoots? r.factors = some roots) :
    (Roots.finite roots).NoDuplicates := by
  obtain ⟨hsize, hget⟩ := linearRoots?_get hlinear
  have hpairwise := factor_fsts_pairwise r hsound
  rw [List.pairwise_iff_getElem] at hpairwise
  change roots.toList.Pairwise fun a b => a.1 ≠ b.1
  rw [List.pairwise_iff_getElem]
  intro i j hiRoots hjRoots hij hrootEq
  have hiFactors : i < r.factors.size := by simpa [hsize] using hiRoots
  have hjFactors : j < r.factors.size := by simpa [hsize] using hjRoots
  have hiData := hget i hiFactors hiRoots
  have hjData := hget j hjFactors hjRoots
  have hvalues :
      -r.factors[i].1.coeff 0 / r.factors[i].1.leadingCoeff =
        -r.factors[j].1.coeff 0 / r.factors[j].1.leadingCoeff := by
    simpa [hiData.2.2, hjData.2.2] using hrootEq
  have hiSound := hsound.2.1 r.factors[i]
    (Array.getElem_mem_toList hiFactors)
  have hjSound := hsound.2.1 r.factors[j]
    (Array.getElem_mem_toList hjFactors)
  have hpolynomials : r.factors[i].1 = r.factors[j].1 := by
    apply toPolynomial_injective T
    rw [linearFactor_semantic r.factors[i].1 hiData.1 hiSound.1,
      linearFactor_semantic r.factors[j].1 hjData.1 hjSound.1,
      hvalues]
  exact hpairwise i j (by simpa using hiFactors) (by simpa using hjFactors)
    hij hpolynomials

private theorem linearRoot_isRoot {T : NumberTower} {f : Poly T}
    (r : Factorization T f) (hsound : r.Sound)
    {roots : Array (Elem T × Nat)}
    (hlinear : linearRoots? r.factors = some roots)
    (entry : Elem T × Nat) (hentry : entry ∈ roots.toList) :
    Polynomial.eval (T.toComplex entry.1) (T.toPolynomial f) = 0 := by
  obtain ⟨hsize, hget⟩ := linearRoots?_get hlinear
  obtain ⟨i, hi, hidx⟩ := List.mem_iff_getElem.mp hentry
  have hiRoots : i < roots.size := by simpa using hi
  have hiFactors : i < r.factors.size := by simpa [hsize] using hiRoots
  have hdata := hget i hiFactors hiRoots
  have hroot : roots[i] = entry := by simpa using hidx
  have hfactor := hsound.2.1 r.factors[i]
    (Array.getElem_mem_toList hiFactors)
  have hfactorRoot : Polynomial.eval (T.toComplex entry.1)
      (T.toPolynomial r.factors[i].1) = 0 := by
    rw [linearFactor_semantic r.factors[i].1 hdata.1 hfactor.1]
    have hvalue : entry.1 =
        -r.factors[i].1.coeff 0 / r.factors[i].1.leadingCoeff := by
      calc
        entry.1 = roots[i].1 := congrArg Prod.fst hroot.symm
        _ = -r.factors[i].1.coeff 0 /
            r.factors[i].1.leadingCoeff := congrArg Prod.fst hdata.2.2
    rw [hvalue]
    simp
  rw [← hsound.1, semantic_reconstruct,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply mul_eq_zero.mpr
  right
  rw [Polynomial.eval_list_prod, List.prod_eq_zero_iff]
  apply List.mem_map.mpr
  refine ⟨T.toPolynomial r.factors[i].1 ^ r.factors[i].2, ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨r.factors[i], Array.getElem_mem_toList hiFactors, rfl⟩
  · rw [Polynomial.eval_pow, hfactorRoot, zero_pow]
    exact Nat.ne_of_gt hdata.2.1

private theorem factor_isRoot {T : NumberTower} {f : Poly T}
    (r : Factorization T f) (hsound : r.Sound)
    (entry : Poly T × Nat) (hentry : entry ∈ r.factors.toList)
    (candidate : AlgebraicRoot)
    (hroot : Polynomial.eval candidate.toComplex
      (T.toPolynomial entry.1) = 0) :
    Polynomial.eval candidate.toComplex (T.toPolynomial f) = 0 := by
  have hpositive := (hsound.2.1 entry hentry).2.1
  rw [← hsound.1, semantic_reconstruct,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply mul_eq_zero.mpr
  right
  rw [Polynomial.eval_list_prod, List.prod_eq_zero_iff]
  apply List.mem_map.mpr
  refine ⟨T.toPolynomial entry.1 ^ entry.2, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  · rw [Polynomial.eval_pow, hroot, zero_pow]
    exact Nat.ne_of_gt hpositive

open scoped TowerField in
private theorem not_contains_factor_root {T : NumberTower} {f : Poly T}
    (r : Factorization T f) (hsound : r.Sound)
    (entry : Poly T × Nat) (hentry : entry ∈ r.factors.toList)
    (candidate : AlgebraicRoot)
    (hdegree : 1 < entry.1.degree?.getD 0)
    (hroot : Polynomial.eval candidate.toComplex
      (T.toPolynomial entry.1) = 0) :
    ¬ Extension.AlreadyContains T candidate := by
  unfold Extension.AlreadyContains
  rintro ⟨a, ha⟩
  have hrelative : (HexPolyMathlib.toPolynomial entry.1).eval a = 0 := by
    apply toComplex_injective T
    rw [map_zero T]
    change T.embedding
        ((HexPolyMathlib.toPolynomial entry.1).eval a) = 0
    rw [← Polynomial.eval_map_apply, ← toPolynomial_eq_map]
    change Polynomial.eval (T.toComplex a)
      (T.toPolynomial entry.1) = 0
    rw [ha]
    exact hroot
  have hirreducible := (hsound.2.1 entry hentry).2.2.toMathlib
  have hdegreeNe :
      (HexPolyMathlib.toPolynomial entry.1).natDegree ≠ 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    omega
  exact hirreducible.not_isRoot_of_natDegree_ne_one hdegreeNe hrelative

private theorem adjoin_dim_le {T : NumberTower} (candidate : AlgebraicRoot)
    {E : Extension T} (h : adjoin? T candidate = some E) :
    T.dim ≤ E.tower.dim := by
  unfold adjoin? at h
  obtain ⟨factorization, hfactorization, h⟩ :=
    Option.bind_eq_some_iff.mp h
  obtain ⟨selected, hselected, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hdegreeZero : selected.degree?.getD 0 = 0
  · simp [hdegreeZero] at h
  by_cases hdegreeOne : selected.degree?.getD 0 = 1
  · simp only [hdegreeZero, hdegreeOne, one_ne_zero, ↓reduceIte,
      Option.some.injEq] at h
    subst E
    exact Nat.le_refl T.dim
  · simp only [hdegreeZero, hdegreeOne, ↓reduceIte] at h
    obtain ⟨tower, htower, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst E
    rw [Internal.extend?_dim T (levelOfFactor candidate selected) htower]
    change T.dim ≤ selected.degree?.getD 0 * T.dim
    rw [Nat.mul_comm]
    exact Nat.le_mul_of_pos_right T.dim (by omega)

open scoped TowerField in
private theorem nonlinear_find_isSome {T : NumberTower} {f : Poly T}
    (r : Factorization T f) (hsound : r.Sound)
    (hlinear : linearRoots? r.factors = none) :
    (r.factors.toList.find? fun entry =>
      decide (1 < entry.1.degree?.getD 0)).isSome := by
  cases hfind : r.factors.toList.find? fun entry =>
      decide (1 < entry.1.degree?.getD 0) with
  | some entry => rfl
  | none =>
      have hmapSome : (linearRoots? r.factors).isSome := by
        unfold linearRoots?
        apply HexRootsMathlib.array_mapM_isSome
        intro entry hentry
        have hentrySound := hsound.2.1 entry hentry
        have hnot : ¬1 < entry.1.degree?.getD 0 := by
          have := (List.find?_eq_none.mp hfind entry hentry)
          simpa using this
        have hdegree : entry.1.degree?.getD 0 = 1 := by
          have hirreducible := hentrySound.2.2.toMathlib
          have hpositive : 0 < entry.1.degree?.getD 0 := by
            simpa only [HexPolyMathlib.natDegree_toPolynomial] using
              hirreducible.natDegree_pos
          omega
        simp [hdegree, hentrySound.2.1]
      rw [hlinear] at hmapSome
      contradiction

private abbrev ContainsValue (T : NumberTower) (z : ℂ) : Prop :=
  ∃ a : Elem T, T.toComplex a = z

private noncomputable def missingRoots (T : NumberTower) (f : Poly T) :
    Finset ℂ := by
  classical
  exact (T.toPolynomial f).roots.toFinset.filter fun z =>
    ¬ContainsValue T z

private theorem missingRoots_card_le (T : NumberTower) (f : Poly T) :
    (missingRoots T f).card ≤ f.degree?.getD 0 := by
  classical
  unfold missingRoots
  calc
    (missingRoots T f).card ≤
        (T.toPolynomial f).roots.toFinset.card :=
      Finset.card_mono (Finset.filter_subset _ _)
    _ ≤ (T.toPolynomial f).roots.card := Multiset.toFinset_card_le _
    _ ≤ (T.toPolynomial f).natDegree := Polynomial.card_roots' _
    _ = f.degree?.getD 0 := natDegree_toPolynomial T f

private theorem missingRoots_decreases {T : NumberTower} {f : Poly T}
    (candidate : AlgebraicRoot) (step : Extension T)
    (hstep : step.Sound candidate) (hf : T.toPolynomial f ≠ 0)
    (hroot : Polynomial.eval candidate.toComplex (T.toPolynomial f) = 0)
    (hmissing : ¬Extension.AlreadyContains T candidate) :
    (missingRoots step.tower (mapPoly step.embed f)).card <
      (missingRoots T f).card := by
  classical
  have hpoly : step.tower.toPolynomial (mapPoly step.embed f) =
      T.toPolynomial f := toPolynomial_mapPoly step.embed hstep.1 f
  have hsubset : missingRoots step.tower (mapPoly step.embed f) ⊆
      missingRoots T f := by
    intro z hz
    unfold missingRoots at hz ⊢
    rcases Finset.mem_filter.mp hz with ⟨hzroot, hznot⟩
    apply Finset.mem_filter.mpr
    constructor
    · simpa only [hpoly] using hzroot
    · rintro ⟨a, ha⟩
      apply hznot
      exact ⟨step.embed a, (hstep.1 a).trans ha⟩
  have hcandidateOld : candidate.toComplex ∈ missingRoots T f := by
    unfold missingRoots
    apply Finset.mem_filter.mpr
    constructor
    · exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots hf).mpr hroot)
    · exact hmissing
  have hcandidateNew : candidate.toComplex ∉
      missingRoots step.tower (mapPoly step.embed f) := by
    intro hcandidate
    unfold missingRoots at hcandidate
    have hnot := (Finset.mem_filter.mp hcandidate).2
    apply hnot
    exact ⟨step.gen, hstep.2.1.trans hstep.2.2.1⟩
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_of_subset hsubset).mpr
    ⟨candidate.toComplex, hcandidateOld, hcandidateNew⟩

/-- Membership in a finite root result.  The all-roots result has no finite
entries to enumerate. -/
def Roots.Contains {T : NumberTower} (roots : Roots T)
    (entry : Elem T × Nat) : Prop :=
  match roots with
  | .all => False
  | .finite entries => entry ∈ entries.toList

namespace Splitting

/-- Reconstruct the mapped input from its leading coefficient and returned
monic linear factors. -/
@[expose]
def reconstruct {T : NumberTower} {f : Poly T}
    (S : Splitting T f) : Poly S.extension.tower :=
  match S.roots with
  | .all => 0
  | .finite roots =>
      DensePoly.C (S.extension.embed f.leadingCoeff) *
        (Roots.linearProduct (.finite roots))

/-- Closure of the embedded base and returned roots under field operations. -/
inductive GeneratedBy {T : NumberTower} {f : Poly T}
    (S : Splitting T f) : Elem S.extension.tower → Prop
  | base (a : Elem T) : GeneratedBy S (S.extension.embed a)
  | root (entry : Elem S.extension.tower × Nat)
      (h : S.roots.Contains entry) :
      GeneratedBy S entry.1
  | add {a b} : GeneratedBy S a → GeneratedBy S b → GeneratedBy S (a + b)
  | neg {a} : GeneratedBy S a → GeneratedBy S (-a)
  | mul {a b} : GeneratedBy S a → GeneratedBy S b → GeneratedBy S (a * b)
  | inv {a} : GeneratedBy S a → GeneratedBy S a⁻¹

/-- Mathematical meaning of a checked splitting result. -/
def Sound {T : NumberTower} {f : Poly T} (S : Splitting T f) : Prop :=
  S.extension.PreservesEmbedding ∧
    S.reconstruct = mapPoly S.extension.embed f ∧
    (S.roots = Roots.all ↔ T.toPolynomial f = 0) ∧
    S.roots.Positive ∧
    S.roots.NoDuplicates ∧
    (∀ entry, S.roots.Contains entry →
      Polynomial.eval (S.extension.tower.toComplex entry.1)
        (S.extension.tower.toPolynomial
          (mapPoly S.extension.embed f)) = 0) ∧
    ∀ a : Elem S.extension.tower, GeneratedBy S a

end Splitting

private theorem mem_roots_of_isRoot {T : NumberTower} {f : Poly T}
    (S : Splitting T f) (hS : S.Sound) (hf : T.toPolynomial f ≠ 0)
    (a : Elem T)
    (ha : Polynomial.eval (T.toComplex a) (T.toPolynomial f) = 0) :
    ∃ entry, S.roots.Contains entry ∧
      S.extension.embed a = entry.1 := by
  have hpreserves := hS.1
  cases hroots : S.roots with
  | all =>
      have := hS.2.2.1.mp hroots
      exact (hf this).elim
  | finite roots =>
      have hmappedRoot : Polynomial.eval
          (S.extension.tower.toComplex (S.extension.embed a))
          (S.extension.tower.toPolynomial
            (mapPoly S.extension.embed f)) = 0 := by
        rw [toPolynomial_mapPoly S.extension.embed hpreserves,
          hpreserves]
        exact ha
      have hreconstruct := hS.2.1
      rw [← hreconstruct] at hmappedRoot
      rw [Splitting.reconstruct, hroots] at hmappedRoot
      rw [toPolynomial_mul, toPolynomial_C, linearProduct_semantic,
        Polynomial.eval_mul, Polynomial.eval_C] at hmappedRoot
      have hlead : S.extension.tower.toComplex
          (S.extension.embed f.leadingCoeff) ≠ 0 := by
        rw [hpreserves]
        rw [← leadingCoeff_toPolynomial]
        exact Polynomial.leadingCoeff_ne_zero.mpr hf
      have hproduct := (mul_eq_zero.mp hmappedRoot).resolve_left hlead
      rw [Polynomial.eval_list_prod, List.prod_eq_zero_iff] at hproduct
      simp only [List.map_map, Function.comp_apply] at hproduct
      obtain ⟨entry, hentry, hentryZero⟩ := List.mem_map.mp hproduct
      have hpositive := hS.2.2.2.1
      rw [hroots] at hpositive
      have hentryPositive := hpositive entry hentry
      change Polynomial.eval
          (S.extension.tower.toComplex (S.extension.embed a))
          ((Polynomial.X - Polynomial.C
            (S.extension.tower.toComplex entry.1)) ^ entry.2) = 0
        at hentryZero
      rw [Polynomial.eval_pow] at hentryZero
      have hlinearZero := eq_zero_of_pow_eq_zero hentryZero
      have hvalues : S.extension.tower.toComplex (S.extension.embed a) =
          S.extension.tower.toComplex entry.1 := by
        have hsub : S.extension.tower.toComplex (S.extension.embed a) -
            S.extension.tower.toComplex entry.1 = 0 := by
          simpa using hlinearZero
        exact sub_eq_zero.mp hsub
      refine ⟨entry, ?_, toComplex_injective S.extension.tower hvalues⟩
      simpa [Roots.Contains, hroots] using hentry

private theorem generated_evalPoly {T : NumberTower} {f : Poly T}
    (step : Extension T) (inner : Splitting step.tower (mapPoly step.embed f))
    (hstep : step.PreservesEmbedding)
    (hinner : inner.extension.PreservesEmbedding)
    (hgen : Splitting.GeneratedBy
      ({ extension := composeExtension step inner.extension
         roots := inner.roots } : Splitting T f)
      (inner.extension.embed step.gen)) :
    ∀ p : Poly T, Splitting.GeneratedBy
      ({ extension := composeExtension step inner.extension
         roots := inner.roots } : Splitting T f)
      (inner.extension.embed (step.evalPoly p step.gen)) := by
  let S : Splitting T f :=
    { extension := composeExtension step inner.extension
      roots := inner.roots }
  change ∀ p : Poly T, Splitting.GeneratedBy S
    (inner.extension.embed (step.evalPoly p step.gen))
  intro p
  unfold Extension.evalPoly
  rw [← Array.foldr_toList]
  let coefficients := p.toArray.toList
  change Splitting.GeneratedBy S
    (inner.extension.embed
      (coefficients.foldr
        (fun coefficient value => step.embed coefficient + step.gen * value) 0))
  induction coefficients with
  | nil =>
      have hzero : inner.extension.embed (0 : Elem step.tower) = 0 := by
        apply toComplex_injective inner.extension.tower
        rw [hinner, map_zero, map_zero]
      rw [List.foldr_nil, hzero]
      have hbase := Splitting.GeneratedBy.base
        (S := S) (0 : Elem T)
      have hbaseZero : (composeExtension step inner.extension).embed
          (0 : Elem T) = 0 := by
        have hstepZero : step.embed (0 : Elem T) = 0 := by
          apply toComplex_injective step.tower
          rw [hstep, map_zero, map_zero]
        change inner.extension.embed (step.embed (0 : Elem T)) = 0
        rw [hstepZero, hzero]
      rwa [hbaseZero] at hbase
  | cons coefficient coefficients ih =>
      rw [List.foldr_cons,
        Extension.embed_add inner.extension hinner,
        Extension.embed_mul inner.extension hinner]
      apply Splitting.GeneratedBy.add
      · exact Splitting.GeneratedBy.base
          (S := S) coefficient
      · exact Splitting.GeneratedBy.mul hgen ih

private theorem composeSplitting_sound {T : NumberTower} {f : Poly T}
    (candidate : AlgebraicRoot) (step : Extension T)
    (inner : Splitting step.tower (mapPoly step.embed f))
    (hstep : step.Sound candidate) (hinner : inner.Sound)
    (hf : T.toPolynomial f ≠ 0)
    (hcandidate : Polynomial.eval candidate.toComplex
      (T.toPolynomial f) = 0) :
    ({ extension := composeExtension step inner.extension,
       roots := inner.roots } : Splitting T f).Sound := by
  let S : Splitting T f :=
    { extension := composeExtension step inner.extension
      roots := inner.roots }
  unfold Extension.Sound at hstep
  have hSroots : S.roots = inner.roots := rfl
  have hpreserves : S.extension.PreservesEmbedding :=
    fun a => (hinner.1 (step.embed a)).trans (hstep.1 a)
  have hlead := leadingCoeff_mapPoly step.embed hstep.1 f
  have hreconstruct : S.reconstruct = mapPoly S.extension.embed f := by
    dsimp only [S, composeExtension, Splitting.reconstruct]
    have hcomp :=
      mapPoly_comp inner.extension.embed step.embed hinner.1 hstep.1 f
    change mapPoly inner.extension.embed (mapPoly step.embed f) =
      mapPoly (fun a => inner.extension.embed (step.embed a)) f at hcomp
    rw [← hcomp, ← hinner.2.1]
    cases hroots : inner.roots with
    | all => simp [Splitting.reconstruct, hroots]
    | finite roots =>
        simp only [Splitting.reconstruct, hroots]
        rw [hlead]
  have hzero : S.roots = Roots.all ↔ T.toPolynomial f = 0 := by
    change inner.roots = Roots.all ↔ T.toPolynomial f = 0
    rw [← toPolynomial_mapPoly step.embed hstep.1]
    exact hinner.2.2.1
  have hrootsCorrect : ∀ entry,
      S.roots.Contains entry →
      Polynomial.eval (S.extension.tower.toComplex entry.1)
        (S.extension.tower.toPolynomial
          (mapPoly S.extension.embed f)) = 0 := by
    intro entry hentry
    change Elem inner.extension.tower × Nat at entry
    have hlocal := hinner.2.2.2.2.2.1 entry
    have hentry' : inner.roots.Contains entry := by
      rw [hSroots] at hentry
      exact hentry
    have := hlocal hentry'
    rw [mapPoly_comp inner.extension.embed step.embed hinner.1 hstep.1 f]
      at this
    exact this
  have hlocalNe : step.tower.toPolynomial (mapPoly step.embed f) ≠ 0 := by
    rw [toPolynomial_mapPoly step.embed hstep.1]
    exact hf
  have hgenRoot : Polynomial.eval (step.tower.toComplex step.gen)
      (step.tower.toPolynomial (mapPoly step.embed f)) = 0 := by
    rw [toPolynomial_mapPoly step.embed hstep.1,
      hstep.2.1, hstep.2.2.1]
    exact hcandidate
  obtain ⟨rootEntry, hrootMem, hgenEq⟩ :=
    mem_roots_of_isRoot inner hinner hlocalNe step.gen hgenRoot
  have hgen : Splitting.GeneratedBy S
      (inner.extension.embed step.gen) := by
    have hrootMemS : S.roots.Contains rootEntry := by
      rw [hSroots]
      exact hrootMem
    have hroot := Splitting.GeneratedBy.root (S := S) rootEntry hrootMemS
    rw [hgenEq]
    exact hroot
  have hgenerated : ∀ a : Elem S.extension.tower,
      Splitting.GeneratedBy S a := by
    intro a
    have translate : ∀ {b : Elem inner.extension.tower},
        Splitting.GeneratedBy inner b → Splitting.GeneratedBy S b := by
      intro b hb
      induction hb with
      | base value =>
          have hstepGenerated := hstep.2.2.2.1
          unfold Extension.Generated at hstepGenerated
          obtain ⟨p, hp⟩ := hstepGenerated value
          have hvalue := generated_evalPoly step inner hstep.1 hinner.1 hgen p
          rw [hp] at hvalue
          exact hvalue
      | root entry hentry =>
          have hentryS : S.roots.Contains entry := by
            rw [hSroots]
            exact hentry
          exact Splitting.GeneratedBy.root (S := S) entry hentryS
      | add _ _ ihA ihB => exact Splitting.GeneratedBy.add ihA ihB
      | neg _ ih => exact Splitting.GeneratedBy.neg ih
      | mul _ _ ihA ihB => exact Splitting.GeneratedBy.mul ihA ihB
      | inv _ ih => exact Splitting.GeneratedBy.inv ih
    exact translate (hinner.2.2.2.2.2.2 a)
  exact ⟨hpreserves, hreconstruct, hzero,
    hinner.2.2.2.1, hinner.2.2.2.2.1,
    hrootsCorrect, hgenerated⟩

private theorem linearSplitting_sound {T : NumberTower} {f : Poly T}
    (r : Factorization T f) (hsound : r.Sound)
    {roots : Array (Elem T × Nat)}
    (hlinear : linearRoots? r.factors = some roots)
    (hf : T.toPolynomial f ≠ 0) :
    ({ extension := Extension.identity T
       roots := .finite roots } : Splitting T f).Sound := by
  let S : Splitting T f :=
    { extension := Extension.identity T
      roots := .finite roots }
  have hreconstruct : S.reconstruct = mapPoly S.extension.embed f := by
    apply toPolynomial_injective T
    change T.toPolynomial
        (DensePoly.C f.leadingCoeff * Roots.linearProduct (.finite roots)) =
      T.toPolynomial (mapPoly id f)
    rw [toPolynomial_mul, toPolynomial_C, linearProduct_semantic,
      linearProducts_eq r hsound hlinear,
      ← factorization_scalar_eq_leadingCoeff r hsound,
      ← semantic_reconstruct r, hsound.1, mapPoly_id]
  refine ⟨identity_preserves T, hreconstruct, ?_,
    linearRoots_positive r hlinear,
    linearRoots_nodup r hsound hlinear, ?_, ?_⟩
  · simp [S, hf]
  · intro entry hentry
    change entry ∈ roots.toList at hentry
    change Polynomial.eval (T.toComplex entry.1)
      (T.toPolynomial (mapPoly id f)) = 0
    rw [mapPoly_id]
    exact linearRoot_isRoot r hsound hlinear entry hentry
  · intro a
    change Splitting.GeneratedBy S a
    have hbase := Splitting.GeneratedBy.base (S := S) a
    have hid : id a = a := rfl
    rw [← hid]
    exact hbase

private theorem splitAux_isSome (T : NumberTower) (f : Poly T)
    (fuel : Nat) (hf : T.toPolynomial f ≠ 0)
    (hbound : (missingRoots T f).card ≤ fuel) :
    (splitAux T f fuel).isSome := by
  induction fuel generalizing T f with
  | zero =>
      obtain ⟨factorization, hfactorization⟩ :=
        Option.isSome_iff_exists.mp (factor?_isSome T f)
      have hfactorizationSound := factor?_sound T f hfactorization
      cases hlinear : linearRoots? factorization.factors with
      | some roots =>
          unfold splitAux
          simp [hfactorization, hlinear]
      | none =>
          obtain ⟨nonlinear, hnonlinear⟩ :=
            Option.isSome_iff_exists.mp
              (nonlinear_find_isSome factorization
                hfactorizationSound hlinear)
          have hdegree : 1 < nonlinear.1.degree?.getD 0 := by
            have hselected := List.find?_some
              (p := fun entry : Poly T × Nat =>
                decide (1 < entry.1.degree?.getD 0)) hnonlinear
            simpa using hselected
          obtain ⟨candidate, hcandidate⟩ :=
            Option.isSome_iff_exists.mp
              (factorRoot?_isSome T nonlinear.1 (by omega))
          obtain ⟨step, hstep⟩ := Option.isSome_iff_exists.mp
            (adjoin?_isSome T candidate)
          have hnonlinearMem := List.mem_of_find?_eq_some hnonlinear
          have hfactorRoot := factorRoot?_sound T nonlinear.1 hcandidate
          have hcandidateRoot : Polynomial.eval candidate.toComplex
              (T.toPolynomial f) = 0 :=
            factor_isRoot factorization hfactorizationSound nonlinear
              hnonlinearMem candidate hfactorRoot
          have hnotContains := not_contains_factor_root factorization
            hfactorizationSound nonlinear hnonlinearMem candidate
            hdegree hfactorRoot
          have hdecrease := missingRoots_decreases candidate step
            (adjoin?_sound T candidate hstep) hf hcandidateRoot hnotContains
          omega
  | succ fuel ih =>
      obtain ⟨factorization, hfactorization⟩ :=
        Option.isSome_iff_exists.mp (factor?_isSome T f)
      have hfactorizationSound := factor?_sound T f hfactorization
      cases hlinear : linearRoots? factorization.factors with
      | some roots =>
          unfold splitAux
          simp [hfactorization, hlinear]
      | none =>
          obtain ⟨nonlinear, hnonlinear⟩ :=
            Option.isSome_iff_exists.mp
              (nonlinear_find_isSome factorization
                hfactorizationSound hlinear)
          have hdegree : 1 < nonlinear.1.degree?.getD 0 := by
            have hselected := List.find?_some
              (p := fun entry : Poly T × Nat =>
                decide (1 < entry.1.degree?.getD 0)) hnonlinear
            simpa using hselected
          obtain ⟨candidate, hcandidate⟩ :=
            Option.isSome_iff_exists.mp
              (factorRoot?_isSome T nonlinear.1 (by omega))
          obtain ⟨step, hstep⟩ := Option.isSome_iff_exists.mp
            (adjoin?_isSome T candidate)
          have hnonlinearMem := List.mem_of_find?_eq_some hnonlinear
          have hfactorRoot := factorRoot?_sound T nonlinear.1 hcandidate
          have hcandidateRoot : Polynomial.eval candidate.toComplex
              (T.toPolynomial f) = 0 :=
            factor_isRoot factorization hfactorizationSound nonlinear
              hnonlinearMem candidate hfactorRoot
          have hnotContains := not_contains_factor_root factorization
            hfactorizationSound nonlinear hnonlinearMem candidate
            hdegree hfactorRoot
          have hstepSound := adjoin?_sound T candidate hstep
          have hdimensionNe : step.tower.dim ≠ T.dim := by
            intro hequal
            exact hnotContains (hstepSound.2.2.2.2.mp hequal)
          have hdimension : T.dim < step.tower.dim :=
            lt_of_le_of_ne (adjoin_dim_le candidate hstep)
              hdimensionNe.symm
          have hlocalNe : step.tower.toPolynomial
              (mapPoly step.embed f) ≠ 0 := by
            rw [toPolynomial_mapPoly step.embed hstepSound.1]
            exact hf
          have hdecrease := missingRoots_decreases candidate step
            hstepSound hf hcandidateRoot hnotContains
          have hlocalBound :
              (missingRoots step.tower (mapPoly step.embed f)).card ≤ fuel := by
            omega
          obtain ⟨inner, hinner⟩ := Option.isSome_iff_exists.mp
            (ih step.tower (mapPoly step.embed f) hlocalNe hlocalBound)
          have hnonlinearArray : factorization.factors.find?
              (fun entry => decide (1 < entry.1.degree?.getD 0)) =
              some nonlinear := by
            simpa using hnonlinear
          unfold splitAux
          simp [hfactorization, hlinear, hnonlinearArray, hcandidate, hstep,
            Nat.not_le_of_lt hdimension, hinner]

private theorem splitAux_sound (T : NumberTower) (f : Poly T)
    (fuel : Nat) (hf : T.toPolynomial f ≠ 0)
    {S : Splitting T f} (h : splitAux T f fuel = some S) :
    S.Sound := by
  induction fuel generalizing T f S with
  | zero =>
      unfold splitAux at h
      obtain ⟨factorization, hfactorization, h⟩ :=
        Option.bind_eq_some_iff.mp h
      cases hlinear : linearRoots? factorization.factors with
      | none => simp [hlinear] at h
      | some roots =>
          simp only [hlinear, Option.some.injEq] at h
          subst S
          exact linearSplitting_sound factorization
            (factor?_sound T f hfactorization) hlinear hf
  | succ fuel ih =>
      unfold splitAux at h
      obtain ⟨factorization, hfactorization, h⟩ :=
        Option.bind_eq_some_iff.mp h
      cases hlinear : linearRoots? factorization.factors with
      | some roots =>
          simp only [hlinear, Option.some.injEq] at h
          subst S
          exact linearSplitting_sound factorization
            (factor?_sound T f hfactorization) hlinear hf
      | none =>
          rw [hlinear] at h
          obtain ⟨nonlinear, hnonlinear, h⟩ :=
            Option.bind_eq_some_iff.mp h
          obtain ⟨candidate, hcandidate, h⟩ :=
            Option.bind_eq_some_iff.mp h
          obtain ⟨step, hstep, h⟩ := Option.bind_eq_some_iff.mp h
          split at h
          next hdimension => simp at h
          next hdimension =>
            obtain ⟨inner, hinner, h⟩ := Option.bind_eq_some_iff.mp h
            simp only [Option.some.injEq] at h
            subst S
            have hfactorizationSound :=
              factor?_sound T f hfactorization
            have hcandidateRoot : Polynomial.eval candidate.toComplex
                (T.toPolynomial f) = 0 :=
              factor_isRoot factorization hfactorizationSound nonlinear
                (List.mem_of_find?_eq_some hnonlinear) candidate
                (factorRoot?_sound T nonlinear.1 hcandidate)
            have hstepSound := adjoin?_sound T candidate hstep
            have hlocalNe : step.tower.toPolynomial
                (mapPoly step.embed f) ≠ 0 := by
              rw [toPolynomial_mapPoly step.embed hstepSound.1]
              exact hf
            have hinnerSound := ih step.tower (mapPoly step.embed f)
              hlocalNe hinner
            rw [Splitting.trans_eq step inner]
            exact composeSplitting_sound candidate step inner hstepSound
              hinnerSound hf hcandidateRoot

private theorem zeroSplitting_sound (T : NumberTower) :
    ({ extension := Extension.identity T
       roots := .all } : Splitting T (0 : Poly T)).Sound := by
  let S : Splitting T (0 : Poly T) :=
    { extension := Extension.identity T
      roots := .all }
  refine ⟨identity_preserves T, ?_, ?_, trivial, trivial, ?_, ?_⟩
  · change 0 = mapPoly id (0 : Poly T)
    exact (mapPoly_id T 0).symm
  · simp [S, toPolynomial_zero]
  · intro entry hentry
    exact (by simpa [S, Roots.Contains] using hentry)
  · intro a
    change Splitting.GeneratedBy S a
    exact Splitting.GeneratedBy.base (S := S) a

private theorem constantSplitting_sound {T : NumberTower} {f : Poly T}
    (hf : T.toPolynomial f ≠ 0) (hdegree : f.degree?.getD 0 = 0) :
    ({ extension := Extension.identity T
       roots := .finite #[] } : Splitting T f).Sound := by
  let S : Splitting T f :=
    { extension := Extension.identity T
      roots := .finite #[] }
  have hpoly : T.toPolynomial f =
      Polynomial.C (T.toComplex f.leadingCoeff) := by
    have hconstant := Polynomial.eq_C_of_natDegree_eq_zero
      (p := T.toPolynomial f) (by simpa using hdegree)
    rw [hconstant]
    congr 1
    rw [← leadingCoeff_toPolynomial]
    simp [Polynomial.leadingCoeff, hdegree]
  have hreconstruct : S.reconstruct = mapPoly S.extension.embed f := by
    apply toPolynomial_injective T
    change T.toPolynomial
        (DensePoly.C f.leadingCoeff * Roots.linearProduct
          (.finite (#[] : Array (Elem T × Nat)))) =
      T.toPolynomial (mapPoly id f)
    rw [toPolynomial_mul, toPolynomial_C, linearProduct_semantic,
      mapPoly_id, hpoly]
    simp
  refine ⟨identity_preserves T, hreconstruct, ?_, ?_, ?_, ?_, ?_⟩
  · simp [S, hf]
  · change (Roots.finite (#[] : Array (Elem T × Nat))).Positive
    rintro ⟨a, b⟩ hentry
    simp at hentry
  · simp [S, Roots.NoDuplicates]
  · intro entry hentry
    exact (by simpa [S, Roots.Contains] using hentry)
  · intro a
    change Splitting.GeneratedBy S a
    exact Splitting.GeneratedBy.base (S := S) a

/-- Every returned split payload reconstructs the input and generates the
result extension from the listed roots. -/
theorem split?_sound (T : NumberTower) (f : Poly T)
    {S : Splitting T f} (h : T.split? f = some S) :
    S.Sound := by
  unfold split? at h
  split at h
  next hzero =>
    have hfzero : f = 0 :=
      DensePoly.size_eq_zero_iff f |>.mp
        ((DensePoly.isZero_eq_true_iff f).mp hzero)
    subst f
    simp only [Option.some.injEq] at h
    subst S
    exact zeroSplitting_sound T
  next hnonzero =>
    have hf : T.toPolynomial f ≠ 0 := by
      intro hzero
      have hfzero : f = 0 := toPolynomial_injective T hzero
      subst f
      have hzeroTest : (0 : Poly T).isZero = true :=
        (DensePoly.isZero_eq_true_iff (0 : Poly T)).mpr
          DensePoly.size_zero
      rw [hzeroTest] at hnonzero
      contradiction
    split at h
    next hdegree =>
      simp only [Option.some.injEq] at h
      subst S
      exact constantSplitting_sound hf hdegree
    next hdegree =>
      exact splitAux_sound T f (f.degree?.getD 0) hf h

/-- The bounded split/refactor loop succeeds for every tower polynomial. -/
theorem split?_isSome (T : NumberTower) (f : Poly T) :
    (T.split? f).isSome := by
  unfold split?
  split
  · rfl
  · rename_i hnonzero
    split
    · rfl
    · have hf : T.toPolynomial f ≠ 0 := by
        intro hzero
        have hfzero : f = 0 := toPolynomial_injective T hzero
        subst f
        have hzeroTest : (0 : Poly T).isZero = true :=
          (DensePoly.isZero_eq_true_iff (0 : Poly T)).mpr
            DensePoly.size_zero
        rw [hzeroTest] at hnonzero
        contradiction
      exact splitAux_isSome T f (f.degree?.getD 0) hf
        (missingRoots_card_le T f)

end Hex.NumberTower
