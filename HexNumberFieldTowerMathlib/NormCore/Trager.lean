/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.NormCore.Basic

public section

namespace Hex.NumberTower

namespace Norm

/-- A complex root of the mapped lower-field relation satisfies the explicit
monic relation used by conjugate evaluation. -/
private theorem relation_sum_of_mem_rootSet (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ =
        (LevelSemantics.coeffDenote lower a)⁻¹)
    (x : ℂ) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjective hinv
    let ι : Arithmetic.Coeff lower →+* ℂ :=
      LevelSemantics.coeffHom lower hvalid.2.2 hinjective hinv
    letI : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
    x ∈ (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level lower)).rootSet ℂ →
    (∑ j ∈ Finset.range level.degree,
        LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
      x ^ level.degree = 0 := by
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjective hinv
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    LevelSemantics.coeffHom lower hvalid.2.2 hinjective hinv
  let : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  change x ∈ (HexPolyMathlib.toPolynomial
    (Arithmetic.Coeff.relation level lower)).rootSet ℂ → _
  intro hx
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  have hpDegree : p.natDegree = level.degree := by
    simpa [p, relation] using
      LevelSemantics.relation_degree level lower hvalid
  have hxzero := Polynomial.aeval_eq_zero_of_mem_rootSet hx
  rw [Polynomial.aeval_def] at hxzero
  change p.eval₂ ι x = 0 at hxzero
  rw [Polynomial.eval₂_eq_sum_range' (n := level.degree + 1) ι
      (by rw [hpDegree]; omega) x,
    Finset.sum_range_succ] at hxzero
  have hbelow : ∀ j < level.degree, relation.coeff j =
      Arithmetic.Coeff.ofData lower (level.defining.getD j #[]) := by
    intro j hj
    have hle : j ≤ level.degree := Nat.le_of_lt hj
    simp [relation, Arithmetic.Coeff.relation, Array.getD, hj, hle]
  have htop : relation.coeff level.degree = 1 := by
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hsum :
      (∑ j ∈ Finset.range level.degree, ι (p.coeff j) * x ^ j) =
        ∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [HexPolyMathlib.coeff_toPolynomial,
      hbelow j (Finset.mem_range.mp hj)]
    simp [ι, LevelSemantics.coeffHom, LevelSemantics.coeffDenote,
      Arithmetic.Coeff.ofData, LevelSemantics.denote_fixed]
  have hιone : ι (1 : Arithmetic.Coeff lower) = 1 := ι.map_one
  rw [hsum, HexPolyMathlib.coeff_toPolynomial, htop, hιone,
    one_mul] at hxzero
  exact hxzero

/-- Re-decoding an executable one-level norm recovers the dense resultant
before its coefficients were flattened for the recursive call. -/
theorem rawPoly_oneLevel (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) :
    Factor.rawPoly lower (oneLevel level lower f c) =
      DensePoly.resultant (definingOuter level lower)
        (shiftedOuter level lower f c) := by
  let result := DensePoly.resultant (definingOuter level lower)
    (shiftedOuter level lower f c)
  change DensePoly.ofCoeffs
      (result.toArray.map Arithmetic.Coeff.data |>.map
        (Arithmetic.Coeff.ofData lower)) = result
  rw [Array.map_map]
  have harray : result.toArray.map
      (Arithmetic.Coeff.ofData lower ∘ Arithmetic.Coeff.data) =
        result.toArray := by
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp [Function.comp_def]
  rw [harray, DensePoly.ofCoeffs_toArray]

/-- One executable Trager elimination step is the corresponding polynomial
resultant after semantic interpretation of the lower tower. -/
theorem oneLevel_resultant (level : Level) (lower : List Level)
    (hlower : LevelsValid lower)
    (hinjective : LevelSemantics.DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      LevelSemantics.coeffDenote lower a⁻¹ =
        (LevelSemantics.coeffDenote lower a)⁻¹)
    (f : Array (Array Rat)) (c : Int) :
    rawPolynomial lower
        (DensePoly.ofCoeffs <| (oneLevel level lower f c).map
          (Arithmetic.Coeff.ofData lower)) =
      Polynomial.resultant
        (rawOuter lower (definingOuter level lower))
        (rawOuter lower (shiftedOuter level lower f c))
        (m := (definingOuter level lower).degree?.getD 0)
        (n := (shiftedOuter level lower f c).degree?.getD 0) := by
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hlower hinjective hinv
  let : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let : IsDomain (DensePoly (Arithmetic.Coeff lower)) :=
    (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff lower)).toMulEquiv.isDomain
        (Polynomial (Arithmetic.Coeff lower))
  let outer := definingOuter level lower
  let shifted := shiftedOuter level lower f c
  let result := DensePoly.resultant outer shifted
  have honeLevel : oneLevel level lower f c =
      result.toArray.map Arithmetic.Coeff.data := by
    rfl
  have hroundTrip :
      DensePoly.ofCoeffs
          ((oneLevel level lower f c).map
            (Arithmetic.Coeff.ofData lower)) = result := by
    rw [honeLevel, Array.map_map]
    have harray : result.toArray.map
        (Arithmetic.Coeff.ofData lower ∘ Arithmetic.Coeff.data) =
          result.toArray := by
      apply Array.ext
      · simp
      · intro i hi₁ hi₂
        simp [Function.comp_def]
    rw [harray, DensePoly.ofCoeffs_toArray]
  rw [hroundTrip, ← rawPolynomialHom_apply lower hlower hinjective hinv]
  dsimp only [result]
  rw [DensePoly.toPolynomial_resultant,
    ← Polynomial.resultant_map_map]
  rw [← rawOuter_eq_map lower hlower hinjective hinv outer,
    ← rawOuter_eq_map lower hlower hinjective hinv shifted]

/-- Shifting a current-level polynomial first and then eliminating with zero
shift gives the same lower-field norm as eliminating with that shift. -/
theorem oneLevel_shift_zero (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (c : Int) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    Factor.rawPoly lower
        (oneLevel level lower (Factor.shiftTop level lower f c) 0) =
      Factor.rawPoly lower (oneLevel level lower f c) := by
  classical
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    LevelSemantics.coeffHom lower hvalid.2.2 hinjectiveLower hinvLower
  let : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  let shifted := Factor.shiftTop level lower f c
  let M := rawOuter lower (definingOuter level lower)
  let G := rawOuter lower (shiftedOuter level lower f c)
  let G₀ := rawOuter lower (shiftedOuter level lower shifted 0)
  let n := (shiftedOuter level lower f c).degree?.getD 0
  let n₀ := (shiftedOuter level lower shifted 0).degree?.getD 0
  let R := rawPolynomial lower
    (Factor.rawPoly lower (oneLevel level lower f c))
  let R₀ := rawPolynomial lower
    (Factor.rawPoly lower (oneLevel level lower shifted 0))
  have hhomInjective : Function.Injective
      (rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower) := by
    intro a b hab
    apply rawPolynomial_injective lower hvalid.2.2 hinjectiveLower hinvLower
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower, ← rawPolynomialHom_apply lower hvalid.2.2
      hinjectiveLower hinvLower]
    exact hab
  have hrawOuterDegree
      (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      (rawOuter lower g).natDegree = g.degree?.getD 0 := by
    rw [rawOuter_eq_map lower hvalid.2.2 hinjectiveLower hinvLower,
      Polynomial.natDegree_map_eq_of_injective hhomInjective,
      HexPolyMathlib.natDegree_toPolynomial]
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [LevelSemantics.relation_size level lower hvalid]
      omega), LevelSemantics.relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hrawRelation : rawPolynomial lower relation = p.map ι := by
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower]
    rfl
  have hM : M = (p.map ι).map Polynomial.C := by
    change rawOuter lower (definingOuter level lower) = _
    rw [rawOuter_defining level lower hvalid hinjectiveLower hinvLower,
      hrawRelation]
  have hMMonic : M.Monic := by
    rw [hM]
    exact Polynomial.Monic.map Polynomial.C
      (Polynomial.Monic.map ι hpMonic)
  have hMSplits : M.Splits := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).map Polynomial.C
  have hMRoots : M.roots = (p.map ι).roots.map Polynomial.C := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).roots_map Polynomial.C
  have hRResult : R = Polynomial.resultant M G
      (m := (definingOuter level lower).degree?.getD 0) (n := n) := by
    simpa [R, M, G, n, Factor.rawPoly] using
      oneLevel_resultant level lower hvalid.2.2 hinjectiveLower
        hinvLower f c
  have hR₀Result : R₀ = Polynomial.resultant M G₀
      (m := (definingOuter level lower).degree?.getD 0) (n := n₀) := by
    simpa [R₀, M, G₀, n₀, shifted, Factor.rawPoly] using
      oneLevel_resultant level lower hvalid.2.2 hinjectiveLower
        hinvLower shifted 0
  have hRProd : R = (M.roots.map G.eval).prod := by
    rw [hRResult, ← hrawOuterDegree (definingOuter level lower)]
    have hprod := Polynomial.resultant_eq_prod_eval M G n
      (by simpa [G, n] using
        (hrawOuterDegree (shiftedOuter level lower f c)).le) hMSplits
    simpa [hMMonic.leadingCoeff] using hprod
  have hR₀Prod : R₀ = (M.roots.map G₀.eval).prod := by
    rw [hR₀Result, ← hrawOuterDegree (definingOuter level lower)]
    have hprod := Polynomial.resultant_eq_prod_eval M G₀ n₀
      (by simpa [G₀, n₀] using
        (hrawOuterDegree (shiftedOuter level lower shifted 0)).le) hMSplits
    simpa [hMMonic.leadingCoeff] using hprod
  have heval (r : Polynomial ℂ) (hr : r ∈ M.roots) :
      G₀.eval r = G.eval r := by
    rw [hMRoots] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hr
    let xr : p.rootSet ℂ := ⟨x, by
      change x ∈ (p.map ι).roots.toFinset
      simpa using hx⟩
    have hrelation := relation_sum_of_mem_rootSet level lower hvalid
      hinjectiveLower hinvLower x xr.property
    calc
      G₀.eval (Polynomial.C x) =
          conjugatePolynomial level lower x shifted := by
            simpa [G₀] using eval_shiftedOuter level lower hvalid
              hinjectiveLower hinvLower shifted 0 x
      _ = (conjugatePolynomial level lower x f).comp
          (Polynomial.X - Polynomial.C ((c : ℂ) * x)) := by
            exact conjugatePolynomial_shiftTop level lower hvalid
              hinjectiveTop x hrelation f c
      _ = G.eval (Polynomial.C x) := by
            symm
            simpa [G] using eval_shiftedOuter level lower hvalid
              hinjectiveLower hinvLower f c x
  have hmaps : M.roots.map G₀.eval = M.roots.map G.eval := by
    apply Multiset.map_congr rfl
    intro r hr
    exact heval r hr
  apply rawPolynomial_injective lower hvalid.2.2 hinjectiveLower hinvLower
  change R₀ = R
  rw [hR₀Prod, hRProd, hmaps]

/-- The shifted current-level polynomial divides the lifted one-level norm.
This is the Bézout divisibility direction behind Trager recovery. -/
theorem shifted_dvd_norm (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (c : Int) :
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
    HexPolyMathlib.toPolynomial
        (Factor.rawPoly (level :: lower)
          (Factor.shiftTop level lower f c)) ∣
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly lower (oneLevel level lower f c))).map
          (lowerHom level lower hvalid hinjectiveTop) := by
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let : IsDomain (DensePoly (Arithmetic.Coeff lower)) :=
    (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff lower)).toMulEquiv.isDomain
        (Polynomial (Arithmetic.Coeff lower))
  let M := HexPolyMathlib.toPolynomial (definingOuter level lower)
  let G := HexPolyMathlib.toPolynomial (shiftedOuter level lower f c)
  let m := (definingOuter level lower).degree?.getD 0
  let n := (shiftedOuter level lower f c).degree?.getD 0
  let Φ := outerEvalHom level lower hvalid hinjectiveTop
  have hMdegree : M.natDegree = m := by
    simp [M, m, HexPolyMathlib.natDegree_toPolynomial]
  have hGdegree : G.natDegree = n := by
    simp [G, n, HexPolyMathlib.natDegree_toPolynomial]
  have hMtop : M.coeff level.degree = DensePoly.C 1 := by
    simp [M, definingOuter, Array.getD]
  have hMtopNe : M.coeff level.degree ≠ 0 := by
    rw [hMtop]
    intro hzero
    have hcoeff := congrArg
      (fun p : DensePoly (Arithmetic.Coeff lower) => p.coeff 0) hzero
    simpa using hcoeff
  have hmPos : 0 < m := by
    rw [← hMdegree]
    exact lt_of_lt_of_le (Nat.zero_lt_of_lt hvalid.1.1)
      (Polynomial.le_natDegree_of_ne_zero hMtopNe)
  obtain ⟨p, q, _hp, _hq, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant M G
      (by rw [hMdegree]) (by rw [hGdegree]) (Or.inl hmPos.ne')
  have hresult : Factor.rawPoly lower (oneLevel level lower f c) =
      Polynomial.resultant M G (m := m) (n := n) := by
    rw [rawPoly_oneLevel, DensePoly.toPolynomial_resultant]
  have hMzero : Φ M = 0 := by
    rw [show M = HexPolyMathlib.toPolynomial
      (definingOuter level lower) from rfl,
      outerEvalHom_apply level lower hvalid hinjectiveTop]
    exact outerEval_defining level lower hvalid hinjectiveTop
  have hGshift : Φ G = HexPolyMathlib.toPolynomial
      (Factor.rawPoly (level :: lower)
        (Factor.shiftTop level lower f c)) := by
    rw [show G = HexPolyMathlib.toPolynomial
      (shiftedOuter level lower f c) from rfl,
      outerEvalHom_apply level lower hvalid hinjectiveTop]
    exact outerEval_shifted level lower hvalid hinjectiveTop f c
  have hresultLift : Φ (Polynomial.C
      (Polynomial.resultant M G (m := m) (n := n))) =
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly lower (oneLevel level lower f c))).map
            (lowerHom level lower hvalid hinjectiveTop) := by
    simp only [Φ, outerEvalHom, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, RingHom.comp_apply]
    rw [← hresult]
    rfl
  have hmapped := congrArg Φ hbezout
  rw [Φ.map_add, Φ.map_mul, Φ.map_mul, hMzero, hGshift, zero_mul, zero_add,
    hresultLift] at hmapped
  exact ⟨Φ q, hmapped.symm⟩

/-- A one-level Trager norm of a nonzero current-level polynomial is
nonzero. -/
theorem oneLevel_ne_zero (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat)) (c : Int)
    (hf : Factor.rawPoly (level :: lower) f ≠ 0) :
    Factor.rawPoly lower (oneLevel level lower f c) ≠ 0 := by
  classical
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    LevelSemantics.coeffHom lower hvalid.2.2 hinjectiveLower hinvLower
  let : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  have hpDegree : p.natDegree = level.degree := by
    simpa [p, relation] using
      LevelSemantics.relation_degree level lower hvalid
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [LevelSemantics.relation_size level lower hvalid]
      omega), LevelSemantics.relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hrelation (x : p.rootSet ℂ) :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) *
            (x : ℂ) ^ j) + (x : ℂ) ^ level.degree = 0 :=
    relation_sum_of_mem_rootSet level lower hvalid hinjectiveLower
      hinvLower x x.property
  let P := HexPolyMathlib.toPolynomial
    (Factor.rawPoly (level :: lower) f)
  have hPne : P ≠ 0 := by
    intro hzero
    apply hf
    exact (HexPolyMathlib.equiv
      (R := Arithmetic.Coeff (level :: lower))).injective hzero
  have hconjugateNe (x : p.rootSet ℂ) :
      conjugatePolynomial level lower x f ≠ 0 := by
    have hmap : conjugatePolynomial level lower x f =
        P.map (conjugateMap level lower hvalid hinjectiveTop x
          (hrelation x)) := by
      simpa [P] using conjugatePolynomial_eq_map level lower hvalid
        hinjectiveTop x (hrelation x) f
    rw [hmap]
    intro hzero
    apply hPne
    exact (Polynomial.map_eq_zero_iff
      (conjugateMap level lower hvalid hinjectiveTop x
        (hrelation x)).injective).mp hzero
  let M := rawOuter lower (definingOuter level lower)
  let G := rawOuter lower (shiftedOuter level lower f c)
  let n := (shiftedOuter level lower f c).degree?.getD 0
  let R := rawPolynomial lower
    (Factor.rawPoly lower (oneLevel level lower f c))
  have hhomInjective : Function.Injective
      (rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower) := by
    intro a b hab
    apply rawPolynomial_injective lower hvalid.2.2 hinjectiveLower hinvLower
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower, ← rawPolynomialHom_apply lower hvalid.2.2
      hinjectiveLower hinvLower]
    exact hab
  have hrawOuterDegree
      (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      (rawOuter lower g).natDegree = g.degree?.getD 0 := by
    rw [rawOuter_eq_map lower hvalid.2.2 hinjectiveLower hinvLower,
      Polynomial.natDegree_map_eq_of_injective hhomInjective,
      HexPolyMathlib.natDegree_toPolynomial]
  have hrawRelation : rawPolynomial lower relation = p.map ι := by
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower]
    rfl
  have hM : M = (p.map ι).map Polynomial.C := by
    change rawOuter lower (definingOuter level lower) = _
    rw [rawOuter_defining level lower hvalid hinjectiveLower hinvLower,
      hrawRelation]
  have hMMonic : M.Monic := by
    rw [hM]
    exact Polynomial.Monic.map Polynomial.C
      (Polynomial.Monic.map ι hpMonic)
  have hMSplits : M.Splits := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).map Polynomial.C
  have hMRoots : M.roots = (p.map ι).roots.map Polynomial.C := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).roots_map Polynomial.C
  have hRResult : R = Polynomial.resultant M G
      (m := (definingOuter level lower).degree?.getD 0) (n := n) := by
    simpa [R, M, G, n, Factor.rawPoly] using
      oneLevel_resultant level lower hvalid.2.2 hinjectiveLower
        hinvLower f c
  have hRProd : R = (M.roots.map G.eval).prod := by
    rw [hRResult, ← hrawOuterDegree (definingOuter level lower)]
    have hprod := Polynomial.resultant_eq_prod_eval M G n
      (by simpa [G, n] using
        (hrawOuterDegree (shiftedOuter level lower f c)).le) hMSplits
    simpa [hMMonic.leadingCoeff] using hprod
  have hfactorNe (r : Polynomial ℂ) (hr : r ∈ M.roots) :
      G.eval r ≠ 0 := by
    rw [hMRoots] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hr
    let xr : p.rootSet ℂ := ⟨x, by
      change x ∈ (p.map ι).roots.toFinset
      simpa using hx⟩
    have hspecialize : G.eval (Polynomial.C x) =
        (conjugatePolynomial level lower x f).comp
          (Polynomial.X - Polynomial.C ((c : ℂ) * x)) := by
      simpa [G] using eval_shiftedOuter level lower hvalid
        hinjectiveLower hinvLower f c x
    rw [hspecialize]
    intro hzero
    rcases Polynomial.comp_eq_zero_iff.mp hzero with hconj | hlinear
    · exact hconjugateNe xr hconj
    · have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff 1)
          hlinear.2
      simpa using hcoeff
  have hproductNe : (M.roots.map G.eval).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨r, hr, heq⟩ := Multiset.mem_map.mp hzero
    exact hfactorNe r hr heq
  have hRne : R ≠ 0 := by
    rw [hRProd]
    exact hproductNe
  intro hzero
  apply hRne
  rw [show R = rawPolynomial lower
      (Factor.rawPoly lower (oneLevel level lower f c)) from rfl,
    hzero, rawPolynomial_zero]

/-- Eliminating every validated tower level preserves nonzeroness. -/
theorem iterated_ne_zero (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat))
    (hf : Factor.rawPoly levels f ≠ 0) :
    Factor.rawPoly [] (iterated levels f) ≠ 0 := by
  induction levels generalizing f with
  | nil => simpa [iterated] using hf
  | cons level lower ih =>
      apply ih hvalid.2.2
        (hinjective.tail level lower hvalid.1.1)
      exact oneLevel_ne_zero level lower hvalid hinjective f 0 hf

/-- The one-level Trager norm is multiplicative on canonically encoded
current-level polynomials. -/
theorem oneLevel_mul (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (a b : DensePoly (Arithmetic.Coeff (level :: lower))) (c : Int) :
    Factor.rawPoly lower
        (oneLevel level lower (Factor.polyCoords (a * b)) c) =
      Factor.rawPoly lower
          (oneLevel level lower (Factor.polyCoords a) c) *
        Factor.rawPoly lower
          (oneLevel level lower (Factor.polyCoords b) c) := by
  classical
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    LevelSemantics.coeffHom lower hvalid.2.2 hinjectiveLower hinvLower
  let : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  let M := rawOuter lower (definingOuter level lower)
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [LevelSemantics.relation_size level lower hvalid]
      omega), LevelSemantics.relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hrawRelation : rawPolynomial lower relation = p.map ι := by
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower]
    rfl
  have hM : M = (p.map ι).map Polynomial.C := by
    change rawOuter lower (definingOuter level lower) = _
    rw [rawOuter_defining level lower hvalid hinjectiveLower
      hinvLower, hrawRelation]
  have hMMonic : M.Monic := by
    rw [hM]
    exact Polynomial.Monic.map Polynomial.C
      (Polynomial.Monic.map ι hpMonic)
  have hMSplits : M.Splits := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).map Polynomial.C
  have hhomInjective : Function.Injective
      (rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower) := by
    intro u v huv
    apply rawPolynomial_injective lower hvalid.2.2 hinjectiveLower hinvLower
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower, ← rawPolynomialHom_apply lower hvalid.2.2
      hinjectiveLower hinvLower]
    exact huv
  have hrawOuterDegree
      (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      (rawOuter lower g).natDegree = g.degree?.getD 0 := by
    rw [rawOuter_eq_map lower hvalid.2.2 hinjectiveLower hinvLower,
      Polynomial.natDegree_map_eq_of_injective hhomInjective,
      HexPolyMathlib.natDegree_toPolynomial]
  have hnormProd (u : DensePoly (Arithmetic.Coeff (level :: lower))) :
      rawPolynomial lower
          (Factor.rawPoly lower
            (oneLevel level lower (Factor.polyCoords u) c)) =
        (M.roots.map
          (rawOuter lower
            (shiftedOuter level lower (Factor.polyCoords u) c)).eval).prod := by
    let G := rawOuter lower
      (shiftedOuter level lower (Factor.polyCoords u) c)
    let n := (shiftedOuter level lower
      (Factor.polyCoords u) c).degree?.getD 0
    have hresult : rawPolynomial lower
        (Factor.rawPoly lower
          (oneLevel level lower (Factor.polyCoords u) c)) =
        Polynomial.resultant M G
          (m := (definingOuter level lower).degree?.getD 0) (n := n) := by
      simpa [M, G, n, Factor.rawPoly] using
        oneLevel_resultant level lower hvalid.2.2 hinjectiveLower
          hinvLower (Factor.polyCoords u) c
    have hproduct : rawPolynomial lower
        (Factor.rawPoly lower
          (oneLevel level lower (Factor.polyCoords u) c)) =
        M.leadingCoeff ^ n * (M.roots.map G.eval).prod := by
      rw [hresult, ← hrawOuterDegree (definingOuter level lower)]
      exact Polynomial.resultant_eq_prod_eval M G n
        (by simpa [G, n] using
          (hrawOuterDegree
            (shiftedOuter level lower (Factor.polyCoords u) c)).le)
        hMSplits
    simpa [G, hMMonic.leadingCoeff] using hproduct
  have hMRoots : M.roots = (p.map ι).roots.map Polynomial.C := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).roots_map Polynomial.C
  have hrelationRoot (x : ℂ) (hx : x ∈ (p.map ι).roots) :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0 := by
    apply relation_sum_of_mem_rootSet level lower hvalid hinjectiveLower
      hinvLower x
    change x ∈ (p.map ι).roots.toFinset
    simpa using hx
  have hconjugateMul (x : ℂ) (hx : x ∈ (p.map ι).roots) :
      conjugatePolynomial level lower x (Factor.polyCoords (a * b)) =
        conjugatePolynomial level lower x (Factor.polyCoords a) *
          conjugatePolynomial level lower x (Factor.polyCoords b) := by
    let σ := conjugateMap level lower hvalid hinjectiveTop x
      (hrelationRoot x hx)
    rw [conjugatePolynomial_eq_map level lower hvalid hinjectiveTop x
        (hrelationRoot x hx),
      conjugatePolynomial_eq_map level lower hvalid hinjectiveTop x
        (hrelationRoot x hx),
      conjugatePolynomial_eq_map level lower hvalid hinjectiveTop x
        (hrelationRoot x hx)]
    rw [rawPoly_polyCoords, rawPoly_polyCoords, rawPoly_polyCoords,
      HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]
  have hGmul (x : ℂ) (hx : x ∈ (p.map ι).roots) :
      (rawOuter lower
          (shiftedOuter level lower (Factor.polyCoords (a * b)) c)).eval
            (Polynomial.C x) =
        (rawOuter lower
            (shiftedOuter level lower (Factor.polyCoords a) c)).eval
              (Polynomial.C x) *
          (rawOuter lower
            (shiftedOuter level lower (Factor.polyCoords b) c)).eval
              (Polynomial.C x) := by
    rw [eval_shiftedOuter level lower hvalid hinjectiveLower hinvLower,
      eval_shiftedOuter level lower hvalid hinjectiveLower hinvLower,
      eval_shiftedOuter level lower hvalid hinjectiveLower hinvLower,
      hconjugateMul x hx, Polynomial.mul_comp]
  apply rawPolynomial_injective lower hvalid.2.2 hinjectiveLower hinvLower
  rw [rawPolynomial_mul lower hvalid.2.2 hinjectiveLower hinvLower,
    hnormProd, hnormProd, hnormProd, hMRoots]
  simp only [Multiset.map_map, Function.comp_apply]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  exact Multiset.map_congr rfl fun x hx => hGmul x hx

/-- The norm of a coefficientwise lower-field lift is the expected power by
the relative degree. -/
theorem oneLevel_lift (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (q : DensePoly (Arithmetic.Coeff lower)) :
    let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
    let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
      hinjectiveLower
    let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
      hinjectiveTop
    letI : Field (Arithmetic.Coeff lower) :=
      coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
    let lifted := HexPolyMathlib.ofPolynomial
      ((HexPolyMathlib.toPolynomial q).map
        (lowerHom level lower hvalid hinjectiveTop))
    HexPolyMathlib.toPolynomial
        (Factor.rawPoly lower
          (oneLevel level lower (Factor.polyCoords lifted) 0)) =
      (HexPolyMathlib.toPolynomial q) ^ level.degree := by
  classical
  let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let lifted := HexPolyMathlib.ofPolynomial
    ((HexPolyMathlib.toPolynomial q).map
      (lowerHom level lower hvalid hinjectiveTop))
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    LevelSemantics.coeffHom lower hvalid.2.2 hinjectiveLower hinvLower
  let : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  let M := rawOuter lower (definingOuter level lower)
  let G := rawOuter lower
    (shiftedOuter level lower (Factor.polyCoords lifted) 0)
  let n := (shiftedOuter level lower
    (Factor.polyCoords lifted) 0).degree?.getD 0
  have hpDegree : p.natDegree = level.degree := by
    simpa [p, relation] using
      LevelSemantics.relation_degree level lower hvalid
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [LevelSemantics.relation_size level lower hvalid]
      omega), LevelSemantics.relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hrawRelation : rawPolynomial lower relation = p.map ι := by
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower]
    rfl
  have hM : M = (p.map ι).map Polynomial.C := by
    change rawOuter lower (definingOuter level lower) = _
    rw [rawOuter_defining level lower hvalid hinjectiveLower
      hinvLower, hrawRelation]
  have hMMonic : M.Monic := by
    rw [hM]
    exact Polynomial.Monic.map Polynomial.C
      (Polynomial.Monic.map ι hpMonic)
  have hMSplits : M.Splits := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).map Polynomial.C
  have hhomInjective : Function.Injective
      (rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower) := by
    intro u v huv
    apply rawPolynomial_injective lower hvalid.2.2 hinjectiveLower hinvLower
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower, ← rawPolynomialHom_apply lower hvalid.2.2
      hinjectiveLower hinvLower]
    exact huv
  have hrawOuterDegree
      (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      (rawOuter lower g).natDegree = g.degree?.getD 0 := by
    rw [rawOuter_eq_map lower hvalid.2.2 hinjectiveLower hinvLower,
      Polynomial.natDegree_map_eq_of_injective hhomInjective,
      HexPolyMathlib.natDegree_toPolynomial]
  have hresult : rawPolynomial lower
      (Factor.rawPoly lower
        (oneLevel level lower (Factor.polyCoords lifted) 0)) =
      Polynomial.resultant M G
        (m := (definingOuter level lower).degree?.getD 0) (n := n) := by
    simpa [M, G, n, Factor.rawPoly] using
      oneLevel_resultant level lower hvalid.2.2 hinjectiveLower
        hinvLower (Factor.polyCoords lifted) 0
  have hproduct : rawPolynomial lower
      (Factor.rawPoly lower
        (oneLevel level lower (Factor.polyCoords lifted) 0)) =
      (M.roots.map G.eval).prod := by
    have h := Polynomial.resultant_eq_prod_eval M G n
      (by simpa [G, n] using
        (hrawOuterDegree
          (shiftedOuter level lower (Factor.polyCoords lifted) 0)).le)
      hMSplits
    rw [hresult, ← hrawOuterDegree (definingOuter level lower)]
    simpa [hMMonic.leadingCoeff] using h
  have hMRoots : M.roots = (p.map ι).roots.map Polynomial.C := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).roots_map Polynomial.C
  have hrelationRoot (x : ℂ) (hx : x ∈ (p.map ι).roots) :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0 := by
    apply relation_sum_of_mem_rootSet level lower hvalid hinjectiveLower
      hinvLower x
    change x ∈ (p.map ι).roots.toFinset
    simpa using hx
  have hGconst (x : ℂ) (hx : x ∈ (p.map ι).roots) :
      G.eval (Polynomial.C x) = rawPolynomial lower q := by
    let σ := conjugateMap level lower hvalid hinjectiveTop x
      (hrelationRoot x hx)
    have hcomp : σ.comp (lowerHom level lower hvalid hinjectiveTop) = ι := by
      apply RingHom.ext
      intro z
      change LevelSemantics.evalAt level lower x
          (LevelSemantics.liftCoeff level lower z).data =
        LevelSemantics.coeffDenote lower z
      change LevelSemantics.evalAt level lower x
          (Arithmetic.flattenBlocks level.degree (levelsDim lower)
            #[z.data]) = LevelSemantics.coeffDenote lower z
      rw [LevelSemantics.evalAt_flatten]
      unfold LevelSemantics.evalUpTo
      rw [Finset.sum_eq_single 0]
      · simp [LevelSemantics.coeffDenote, Array.getD]
      · intro i hi hi0
        have hget : (#[z.data] : Array (Array Rat)).getD i #[] = #[] := by
          simp [Array.getD, hi0]
        rw [hget, ← LevelSemantics.denote_fixed lower #[],
          LevelSemantics.denote_zero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr
          (Nat.zero_lt_of_lt hvalid.1.1))).elim
    have hconjugate := conjugatePolynomial_eq_map level lower hvalid
      hinjectiveTop x (hrelationRoot x hx) (Factor.polyCoords lifted)
    rw [show G = rawOuter lower
        (shiftedOuter level lower (Factor.polyCoords lifted) 0) from rfl,
      eval_shiftedOuter level lower hvalid hinjectiveLower hinvLower,
      hconjugate, rawPoly_polyCoords]
    simp only [Int.cast_zero, zero_mul, Polynomial.C_0,
      sub_zero, Polynomial.comp_X]
    rw [show HexPolyMathlib.toPolynomial lifted =
        (HexPolyMathlib.toPolynomial q).map
          (lowerHom level lower hvalid hinjectiveTop) by
      simp [lifted]]
    rw [Polynomial.map_map, hcomp]
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower hinvLower]
    rfl
  have hrootCard : (p.map ι).roots.card = level.degree := by
    rw [← (IsAlgClosed.splits (p.map ι)).natDegree_eq_card_roots,
      Polynomial.natDegree_map_eq_of_injective ι.injective, hpDegree]
  have hsemantic : rawPolynomial lower
      (Factor.rawPoly lower
        (oneLevel level lower (Factor.polyCoords lifted) 0)) =
      rawPolynomial lower q ^ level.degree := by
    rw [hproduct, hMRoots]
    simp only [Multiset.map_map, Function.comp_apply]
    have hmaps : (p.map ι).roots.map
        (fun x => G.eval (Polynomial.C x)) =
          (p.map ι).roots.map (fun _ => rawPolynomial lower q) :=
      Multiset.map_congr rfl fun x hx => hGconst x hx
    rw [hmaps, Multiset.map_const', Multiset.prod_replicate, hrootCard]
  have hmap (r : DensePoly (Arithmetic.Coeff lower)) :
      (HexPolyMathlib.toPolynomial r).map ι = rawPolynomial lower r := by
    change rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower r = _
    exact rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower hinvLower r
  apply Polynomial.map_injective ι ι.injective
  rw [Polynomial.map_pow, hmap, hmap]
  exact hsemantic

/-- A witnessed successful shift inside the remaining fuel makes the
executable bounded search succeed. -/
private theorem findSquarefreeShiftAux_isSome (level : Level)
    (lower : List Level) (f : Array (Array Rat)) (start fuel : Nat)
    (h : ∃ offset < fuel,
      isSquarefree lower
        (oneLevel level lower f (signedShift (start + offset))) = true) :
    (findSquarefreeShiftAux level lower f start fuel).isSome := by
  induction fuel generalizing start with
  | zero =>
      obtain ⟨offset, hoffset, _⟩ := h
      omega
  | succ fuel ih =>
      by_cases hcurrent :
          isSquarefree lower
            (oneLevel level lower f (signedShift start)) = true
      · simp [findSquarefreeShiftAux, hcurrent]
      · rw [findSquarefreeShiftAux]
        simp only [hcurrent]
        apply ih (start := start + 1)
        obtain ⟨offset, hoffset, hsuccess⟩ := h
        have hoffsetNe : offset ≠ 0 := by
          intro hzero
          subst offset
          exact hcurrent (by simpa using hsuccess)
        refine ⟨offset - 1, by omega, ?_⟩
        have hindex : start + 1 + (offset - 1) = start + offset := by
          omega
        rw [hindex]
        exact hsuccess

/-- It is enough to exhibit one successful shift in the advertised Trager
range; this lemma isolates the finite-search bookkeeping from the collision
argument. -/
private theorem findSquarefreeShift_isSome_of_exists (level : Level)
    (lower : List Level) (f : Array (Array Rat))
    (h : ∃ index < tragerShiftCount level.degree (f.size - 1),
      isSquarefree lower
        (oneLevel level lower f (signedShift index)) = true) :
    (findSquarefreeShift level lower f).isSome := by
  apply findSquarefreeShiftAux_isSome level lower f 0
    (tragerShiftCount level.degree (f.size - 1))
  simpa using h

/-- The deterministic signed enumeration never repeats a scalar. -/
private theorem signedShift_injective : Function.Injective signedShift := by
  intro i j hij
  apply AlgebraicPoly.Common.signedShift_injective
  change AlgebraicPoly.Common.signedShift i =
    AlgebraicPoly.Common.signedShift j at hij
  exact hij

/-- Among one more scalars than unordered pairs, one affine combination
separates a finite family, provided equal slopes already have distinct
intercepts. -/
private theorem exists_injective_affine_shift
    {F ι : Type*} [Field F] [Fintype ι]
    (intercept slope : ι → F) (bound : Nat)
    (hcard : Fintype.card ι ≤ bound)
    (hpersistent : ∀ i j, i ≠ j → slope i = slope j →
      intercept i ≠ intercept j)
    (scalar : Fin (Nat.choose bound 2 + 1) → F)
    (hscalar : Function.Injective scalar) :
    ∃ k, Function.Injective fun i => intercept i + scalar k * slope i := by
  classical
  by_contra hseparates
  push Not at hseparates
  have hwitness (k : Fin (Nat.choose bound 2 + 1)) :
      ∃ i j : ι, i ≠ j ∧
        intercept i + scalar k * slope i =
          intercept j + scalar k * slope j := by
    obtain ⟨i, j, hij, hne⟩ :=
      Function.not_injective_iff.mp (hseparates k)
    exact ⟨i, j, hne, hij⟩
  choose left right hne heq using hwitness
  let pair (k : Fin (Nat.choose bound 2 + 1)) :
      {z : Sym2 ι // ¬z.IsDiag} :=
    ⟨s(left k, right k), by simpa using hne k⟩
  have scalar_unique (i j : ι) (hij : i ≠ j) (c d : F)
      (hc : intercept i + c * slope i = intercept j + c * slope j)
      (hd : intercept i + d * slope i = intercept j + d * slope j) :
      c = d := by
    have hslope : slope i ≠ slope j := by
      intro hslope
      exact hpersistent i j hij hslope (by simpa [hslope] using hc)
    have hzero : (c - d) * (slope i - slope j) = 0 := by
      linear_combination hc - hd
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hslope))
  have hpair : Function.Injective pair := by
    intro k l hkl
    have hpairs : s(left k, right k) = s(left l, right l) :=
      congrArg Subtype.val hkl
    rcases Sym2.eq_iff.mp hpairs with hsame | hswap
    · obtain ⟨hleft, hright⟩ := hsame
      apply hscalar
      apply scalar_unique (left k) (right k) (hne k)
      · exact heq k
      · simpa [hleft, hright] using heq l
    · obtain ⟨hleft, hright⟩ := hswap
      apply hscalar
      apply scalar_unique (left k) (right k) (hne k)
      · exact heq k
      · simpa [hleft, hright] using (heq l).symm
  have hpairs := Fintype.card_le_of_injective pair hpair
  rw [Fintype.card_fin, Sym2.card_subtype_not_diag] at hpairs
  rw [HexRootsMathlib.choose_eq_choose] at hpairs
  have hchoose : (Fintype.card ι).choose 2 ≤ bound.choose 2 :=
    Nat.choose_le_choose 2 hcard
  omega

/-- The finite characteristic-zero collision bound finds a squarefree norm
for a squarefree positive-degree component whenever the current canonical
coefficient interpretation is injective.  This parameterized form is the one
used by the level-by-level Trager induction. -/
theorem findSquarefreeShift_isSome_of_injective
    (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjectiveTop : LevelSemantics.DenoteInjective (level :: lower))
    (f : Array (Array Rat))
    (hdegree : 0 < f.size - 1)
    (hsquarefree : Squarefree
      (rawPolynomial (level :: lower)
        (DensePoly.ofCoeffs <| f.map
          (Arithmetic.Coeff.ofData (level :: lower))))) :
    (findSquarefreeShift level lower f).isSome := by
  classical
  have hinjectiveLower : LevelSemantics.DenoteInjective lower :=
    hinjectiveTop.tail level lower hvalid.1.1
  let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
    hinjectiveLower
  let : Field (Arithmetic.Coeff lower) :=
    coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
  let : CommRing (DensePoly (Arithmetic.Coeff lower)) := denseCommRing
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    LevelSemantics.coeffHom lower hvalid.2.2 hinjectiveLower hinvLower
  let : CharZero (Arithmetic.Coeff lower) :=
    { cast_injective := fun m n h => by
        apply CharZero.cast_injective (R := ℂ)
        simpa only [map_natCast] using congrArg ι h }
  let : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  have hpIrreducible : Irreducible p := by
    simpa [p, relation] using
      LevelSemantics.relation_irreducible_of_injective level lower hvalid
        hinjectiveTop hinjectiveLower hinvLower
  have hpSeparable : p.Separable := hpIrreducible.separable
  have hpDegree : p.natDegree = level.degree := by
    simpa [p, relation] using
      LevelSemantics.relation_degree level lower hvalid
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [LevelSemantics.relation_size level lower hvalid]
      omega), LevelSemantics.relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hpRootsCard : Fintype.card (p.rootSet ℂ) = level.degree := by
    rw [Polynomial.card_rootSet_eq_natDegree hpSeparable
      (IsAlgClosed.splits _), hpDegree]
  let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
    hinjectiveTop
  let : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
  let P := HexPolyMathlib.toPolynomial
    (Factor.rawPoly (level :: lower) f)
  have hPSeparable : P.Separable := by
    have hraw : (rawPolynomial (level :: lower)
        (Factor.rawPoly (level :: lower) f)).Separable :=
      PerfectField.separable_iff_squarefree.mpr (by
        simpa [Factor.rawPoly] using hsquarefree)
    have hmap : rawPolynomial (level :: lower)
        (Factor.rawPoly (level :: lower) f) =
          P.map (LevelSemantics.coeffHom (level :: lower) hvalid
            hinjectiveTop hinvTop) := by
      rw [← rawPolynomialHom_apply (level :: lower) hvalid
        hinjectiveTop hinvTop]
      rfl
    rw [hmap] at hraw
    exact (Polynomial.separable_map
      (LevelSemantics.coeffHom (level :: lower) hvalid
        hinjectiveTop hinvTop)).mp hraw
  have hrelation (x : p.rootSet ℂ) :
      (∑ j ∈ Finset.range level.degree,
          LevelSemantics.denote lower (level.defining.getD j #[]) *
            (x : ℂ) ^ j) + (x : ℂ) ^ level.degree = 0 :=
    relation_sum_of_mem_rootSet level lower hvalid hinjectiveLower
      hinvLower x x.property
  have hconjugate (x : p.rootSet ℂ) :
      conjugatePolynomial level lower x f =
        P.map (conjugateMap level lower hvalid hinjectiveTop x
          (hrelation x)) := by
    simpa [P] using conjugatePolynomial_eq_map level lower hvalid
      hinjectiveTop x (hrelation x) f
  have hconjugateSeparable (x : p.rootSet ℂ) :
      (conjugatePolynomial level lower x f).Separable := by
    rw [hconjugate x]
    exact hPSeparable.map
  have hconjugateDegree (x : p.rootSet ℂ) :
      (conjugatePolynomial level lower x f).natDegree = P.natDegree := by
    rw [hconjugate x, Polynomial.natDegree_map_eq_of_injective
      (conjugateMap level lower hvalid hinjectiveTop x
        (hrelation x)).injective]
  have hconjugateRootsCard (x : p.rootSet ℂ) :
      Fintype.card ((conjugatePolynomial level lower x f).rootSet ℂ) =
        P.natDegree := by
    rw [Polynomial.card_rootSet_eq_natDegree (hconjugateSeparable x)
      (IsAlgClosed.splits _), hconjugateDegree x]
  have hPDegree : P.natDegree ≤ f.size - 1 := by
    let q : DensePoly (Arithmetic.Coeff (level :: lower)) :=
      Factor.rawPoly (level :: lower) f
    have hqSize : q.size ≤ f.size := by
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    change (HexPolyMathlib.toPolynomial q).natDegree ≤ f.size - 1
    rw [HexPolyMathlib.natDegree_toPolynomial]
    by_cases hqZero : q.size = 0
    · simp [q, DensePoly.degree?, hqZero]
    · rw [DensePoly.degree?_eq_some_of_pos_size q
        (Nat.pos_of_ne_zero hqZero), Option.getD_some]
      omega
  let RootPair := Σ x : p.rootSet ℂ,
    (conjugatePolynomial level lower x f).rootSet ℂ
  have hpairCard : Fintype.card RootPair =
      level.degree * P.natDegree := by
    change Fintype.card (Σ x : p.rootSet ℂ,
      (conjugatePolynomial level lower x f).rootSet ℂ) = _
    rw [Fintype.card_sigma]
    simp_rw [hconjugateRootsCard]
    simp [hpRootsCard]
  have hpairCardLe : Fintype.card RootPair ≤
      level.degree * (f.size - 1) := by
    rw [hpairCard]
    exact Nat.mul_le_mul_left level.degree hPDegree
  have hscalar : Function.Injective
      (fun k : Fin (Nat.choose (level.degree * (f.size - 1)) 2 + 1) =>
        ((signedShift k : Int) : ℂ)) := by
    intro a b hab
    apply Fin.ext
    apply signedShift_injective
    exact Int.cast_injective hab
  obtain ⟨k, hk⟩ := exists_injective_affine_shift
    (fun z : RootPair => (z.2 : ℂ))
    (fun z : RootPair => (z.1 : ℂ))
    (level.degree * (f.size - 1)) hpairCardLe (by
      intro a b hab hslope
      intro hintercept
      apply hab
      rcases a with ⟨aRoot, aInner⟩
      rcases b with ⟨bRoot, bInner⟩
      have hRoot : aRoot = bRoot := Subtype.ext hslope
      subst bRoot
      have hInner : aInner = bInner := Subtype.ext hintercept
      subst bInner
      rfl)
    (fun k => ((signedShift k : Int) : ℂ)) hscalar
  let c := signedShift (k : Nat)
  let M := rawOuter lower (definingOuter level lower)
  let G := rawOuter lower (shiftedOuter level lower f c)
  let n := (shiftedOuter level lower f c).degree?.getD 0
  let R := rawPolynomial lower
    (Factor.rawPoly lower (oneLevel level lower f c))
  have hhomInjective : Function.Injective
      (rawPolynomialHom lower hvalid.2.2 hinjectiveLower hinvLower) := by
    intro a b hab
    apply rawPolynomial_injective lower hvalid.2.2 hinjectiveLower hinvLower
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower, ← rawPolynomialHom_apply lower hvalid.2.2
      hinjectiveLower hinvLower]
    exact hab
  have hrawOuterDegree
      (g : DensePoly (DensePoly (Arithmetic.Coeff lower))) :
      (rawOuter lower g).natDegree = g.degree?.getD 0 := by
    rw [rawOuter_eq_map lower hvalid.2.2 hinjectiveLower hinvLower,
      Polynomial.natDegree_map_eq_of_injective hhomInjective,
      HexPolyMathlib.natDegree_toPolynomial]
  have hrawRelation : rawPolynomial lower relation = p.map ι := by
    rw [← rawPolynomialHom_apply lower hvalid.2.2 hinjectiveLower
      hinvLower]
    rfl
  have hM : M = (p.map ι).map Polynomial.C := by
    change rawOuter lower (definingOuter level lower) = _
    rw [rawOuter_defining level lower hvalid hinjectiveLower
      hinvLower, hrawRelation]
  have hMMonic : M.Monic := by
    rw [hM]
    exact Polynomial.Monic.map Polynomial.C
      (Polynomial.Monic.map ι hpMonic)
  have hMSplits : M.Splits := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).map Polynomial.C
  have hRResult : R = Polynomial.resultant M G
      (m := (definingOuter level lower).degree?.getD 0) (n := n) := by
    simpa [R, M, G, n, c, Factor.rawPoly] using
      oneLevel_resultant level lower hvalid.2.2 hinjectiveLower
        hinvLower f c
  have hRProd : R =
      M.leadingCoeff ^ n * (M.roots.map G.eval).prod := by
    rw [hRResult, ← hrawOuterDegree (definingOuter level lower)]
    exact Polynomial.resultant_eq_prod_eval M G n
      (by simpa [G, n] using
        (hrawOuterDegree (shiftedOuter level lower f c)).le) hMSplits
  have hRProd' : R = (M.roots.map G.eval).prod := by
    simpa [hMMonic.leadingCoeff] using hRProd
  have hMRoots : M.roots = (p.map ι).roots.map Polynomial.C := by
    rw [hM]
    exact (IsAlgClosed.splits (p.map ι)).roots_map Polynomial.C
  have hfactorNe (r : Polynomial ℂ) (hr : r ∈ M.roots) :
      G.eval r ≠ 0 := by
    rw [hMRoots] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hr
    let xr : p.rootSet ℂ := ⟨x, by
      change x ∈ (p.map ι).roots.toFinset
      simpa using hx⟩
    have hspecialize : G.eval (Polynomial.C x) =
        (conjugatePolynomial level lower x f).comp
          (Polynomial.X - Polynomial.C ((c : ℂ) * x)) := by
      simpa [G] using eval_shiftedOuter level lower hvalid
        hinjectiveLower hinvLower f c x
    rw [hspecialize]
    intro hzero
    rcases Polynomial.comp_eq_zero_iff.mp hzero with hconj | hlinear
    · exact (hconjugateSeparable xr).ne_zero hconj
    · have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff 1) hlinear.2
      simpa using hcoeff
  have hproductNe : (M.roots.map G.eval).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨r, hr, heq⟩ := Multiset.mem_map.mp hzero
    exact hfactorNe r hr heq
  have hRne : R ≠ 0 := by
    rw [hRProd']
    exact hproductNe
  let affine (z : RootPair) : ℂ :=
    (z.2 : ℂ) + (c : ℂ) * (z.1 : ℂ)
  have haffineInjective : Function.Injective affine := by
    simpa [affine, c] using hk
  have haffineRoot (z : RootPair) : affine z ∈ R.rootSet ℂ := by
    have hxRoots : (z.1 : ℂ) ∈ (p.map ι).roots := by
      have hzProperty := z.1.property
      change (z.1 : ℂ) ∈ (p.map ι).roots.toFinset at hzProperty
      simpa using hzProperty
    have hxM : Polynomial.C (z.1 : ℂ) ∈ M.roots := by
      rw [hMRoots]
      exact Multiset.mem_map.mpr ⟨z.1, hxRoots, rfl⟩
    have hfactorDvd : G.eval (Polynomial.C (z.1 : ℂ)) ∣ R := by
      rw [hRProd']
      exact Multiset.dvd_prod (Multiset.mem_map.mpr
        ⟨Polynomial.C (z.1 : ℂ), hxM, rfl⟩)
    have hinnerZero :
        (conjugatePolynomial level lower (z.1 : ℂ) f).eval (z.2 : ℂ) = 0 := by
      have hz := Polynomial.aeval_eq_zero_of_mem_rootSet z.2.property
      simpa [Polynomial.aeval_def] using hz
    have hspecialize : G.eval (Polynomial.C (z.1 : ℂ)) =
        (conjugatePolynomial level lower z.1 f).comp
          (Polynomial.X - Polynomial.C ((c : ℂ) * (z.1 : ℂ))) := by
      simpa [G] using eval_shiftedOuter level lower hvalid
        hinjectiveLower hinvLower f c (z.1 : ℂ)
    have hfactorZero :
        (G.eval (Polynomial.C (z.1 : ℂ))).eval (affine z) = 0 := by
      rw [hspecialize, Polynomial.eval_comp]
      convert hinnerZero using 1
      simp [affine]
    apply (Polynomial.mem_rootSet_of_ne hRne).2
    simpa [Polynomial.aeval_def] using
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hfactorDvd hfactorZero
  let rootMap (z : RootPair) : R.rootSet ℂ :=
    ⟨affine z, haffineRoot z⟩
  have hrootMapInjective : Function.Injective rootMap := by
    intro a b hab
    apply haffineInjective
    exact congrArg Subtype.val hab
  have hcardLower : Fintype.card RootPair ≤
      Fintype.card (R.rootSet ℂ) :=
    Fintype.card_le_of_injective rootMap hrootMapInjective
  have hfactorDegree (r : Polynomial ℂ) (hr : r ∈ M.roots) :
      (G.eval r).natDegree = P.natDegree := by
    rw [hMRoots] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hr
    let xr : p.rootSet ℂ := ⟨x, by
      change x ∈ (p.map ι).roots.toFinset
      simpa using hx⟩
    have hspecialize : G.eval (Polynomial.C x) =
        (conjugatePolynomial level lower x f).comp
          (Polynomial.X - Polynomial.C ((c : ℂ) * x)) := by
      simpa [G] using eval_shiftedOuter level lower hvalid
        hinjectiveLower hinvLower f c x
    rw [hspecialize, Polynomial.natDegree_comp, hconjugateDegree xr,
      Polynomial.natDegree_X_sub_C, mul_one]
  have hMDegree : M.natDegree = level.degree := by
    rw [hM,
      Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective,
      Polynomial.natDegree_map_eq_of_injective ι.injective, hpDegree]
  have hRdegree : R.natDegree ≤ level.degree * P.natDegree := by
    rw [hRProd']
    refine (Polynomial.natDegree_multiset_prod_le _).trans ?_
    have hdegrees :
        (M.roots.map G.eval).map Polynomial.natDegree =
          M.roots.map (fun _ => P.natDegree) := by
      simp only [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro r hr
      exact hfactorDegree r hr
    rw [hdegrees, Multiset.map_const', Multiset.sum_replicate,
      Nat.nsmul_eq_mul, ← hMSplits.natDegree_eq_card_roots, hMDegree]
  have hcardUpper : Fintype.card (R.rootSet ℂ) ≤ R.natDegree := by
    rw [Set.fintypeCard_eq_ncard]
    exact
      Polynomial.ncard_rootSet_le R ℂ
  have hcardEq : Fintype.card (R.rootSet ℂ) = R.natDegree := by
    rw [hpairCard] at hcardLower
    omega
  have hRSeparable : R.Separable :=
    (Polynomial.card_rootSet_eq_natDegree_iff_of_splits hRne
      (IsAlgClosed.splits _)).mp hcardEq
  apply findSquarefreeShift_isSome_of_exists
  refine ⟨k, k.isLt, ?_⟩
  apply (isSquarefree_iff lower hvalid.2.2 hinjectiveLower hinvLower _).mpr
  simpa [R, c] using hRSeparable.squarefree

end Norm

end Hex.NumberTower
