/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.ArithmeticCore.Basic

public section

namespace Hex.NumberTower

namespace LevelSemantics

/-- Dense evaluation sends zero to zero. -/
theorem denseMap_zero (lower : List Level) (x : ℂ)
    (hvalid : LevelsValid lower) (hinjective : DenoteInjective lower)
    (hinv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid hinjective hinv
    denseMap lower x hvalid hinjective hinv 0 = 0 := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid hinjective hinv
  simp [denseMap]

private theorem toPolynomial_dvd {R : Type*} [CommSemiring R] [DecidableEq R]
    {f g : DensePoly R} : f ∣ g →
      HexPolyMathlib.toPolynomial f ∣ HexPolyMathlib.toPolynomial g := by
  rintro ⟨q, rfl⟩
  exact ⟨HexPolyMathlib.toPolynomial q, by simp⟩

private theorem toPolynomial_ne_zero {R : Type*} [CommRing R] [DecidableEq R]
    {f : DensePoly R} (hf : f ≠ 0) : HexPolyMathlib.toPolynomial f ≠ 0 := by
  intro hzero
  apply hf
  calc
    f = HexPolyMathlib.ofPolynomial (HexPolyMathlib.toPolynomial f) :=
      (HexPolyMathlib.ofPolynomial_toPolynomial f).symm
    _ = 0 := by rw [hzero, HexPolyMathlib.ofPolynomial_zero]

/-- A dense polynomial of size one is the constant on its leading
coefficient. -/
private theorem eq_C_leadingCoeff_of_size_one {R : Type*} [Zero R]
    [DecidableEq R] (f : DensePoly R) (hsize : f.size = 1) :
    f = DensePoly.C f.leadingCoeff := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  by_cases hn : n = 0
  · subst n
    rw [DensePoly.leadingCoeff_eq_coeff_last f (by omega), hsize]
    rfl
  · rw [if_neg hn]
    exact DensePoly.coeff_eq_zero_of_size_le f (by omega)

/-- The first prescribed coefficient range of a dense polynomial, exposed as
lower-tower coordinate blocks. -/
@[expose]
def denseBlocks (degree : Nat) {lower : List Level}
    (f : DensePoly (Arithmetic.Coeff lower)) : Array (Array Rat) :=
  (Vector.ofFn fun i : Fin degree => (f.coeff i).data).toArray

/-- Embed a lower-coefficient dense polynomial as one canonical coefficient at
the extended level. -/
@[expose]
def liftDense (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff lower)) :
    Arithmetic.Coeff (level :: lower) :=
  ⟨Arithmetic.flattenBlocks level.degree (levelsDim lower)
      (denseBlocks level.degree f), by simp [levelsDim]⟩

/-- Dense-polynomial coefficient embedding denotes its finite evaluation. -/
theorem coeffDenote_liftDense (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff lower)) :
    coeffDenote (level :: lower) (liftDense level lower f) =
      denseEval lower level.root.toComplex level.degree f := by
  rw [coeffDenote, liftDense, denote_flatten, denseEval]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  simp [denseBlocks, coeffDenote, Array.getD, hi']

/-- Flattening an explicit range of dense coefficients denotes the prescribed
finite dense evaluation. -/
theorem denote_flatten_dense (level : Level) (lower : List Level)
    (f : DensePoly (Arithmetic.Coeff lower)) :
    denote (level :: lower)
        (Arithmetic.flattenBlocks level.degree (levelsDim lower)
          (((List.range level.degree).map fun i => (f.coeff i).data).toArray)) =
      denseEval lower level.root.toComplex level.degree f := by
  rw [denote_flatten, denseEval]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  simp [coeffDenote, Array.getD, hi']

/-- Injective extended-level denotation rules out every nonzero vanishing
dense polynomial below the defining degree. -/
theorem dense_eq_zero_of_eval (level : Level) (lower : List Level)
    (hinjective : DenoteInjective (level :: lower))
    (f : DensePoly (Arithmetic.Coeff lower))
    (hdegree : f.degree?.getD 0 < level.degree)
    (heval : denseEval lower level.root.toComplex level.degree f = 0) :
    f = 0 := by
  have hlift : liftDense level lower f = liftDense level lower 0 := by
    apply hinjective
    rw [coeffDenote_liftDense, coeffDenote_liftDense, heval]
    simp [denseEval, coeffDenote_zero]
  apply DensePoly.ext_coeff
  intro n
  by_cases hn : n < level.degree
  · have hblock := congrArg
      (fun c : Arithmetic.Coeff (level :: lower) =>
        Arithmetic.block c.data n (levelsDim lower)) hlift
    simp only [liftDense] at hblock
    rw [Arithmetic.block_flatten level.degree (levelsDim lower) n
        (denseBlocks level.degree f) hn,
      Arithmetic.block_flatten level.degree (levelsDim lower) n
        (denseBlocks level.degree 0) hn] at hblock
    have hf : (denseBlocks level.degree f).getD n #[] =
        (f.coeff n).data := by
      simp [denseBlocks, Array.getD, hn]
    have hz : (denseBlocks level.degree
        (0 : DensePoly (Arithmetic.Coeff lower))).getD n #[] =
        ((0 : DensePoly (Arithmetic.Coeff lower)).coeff n).data := by
      simp [denseBlocks, Array.getD, hn]
    rw [hf, hz, fixedCoeffs_eq_self lower (f.coeff n),
      fixedCoeffs_eq_self lower
        ((0 : DensePoly (Arithmetic.Coeff lower)).coeff n)] at hblock
    exact coeff_eq_of_data_eq hblock
  · rw [DensePoly.coeff_zero]
    apply DensePoly.coeff_eq_zero_of_size_le
    by_cases hf : f.size = 0
    · omega
    · have hdeg : f.degree?.getD 0 = f.size - 1 := by
        simp [DensePoly.degree?, hf]
      rw [hdeg] at hdegree
      omega

/-- The inversion input polynomial evaluates to the denotation of its top-level
coordinate array. -/
theorem denseEval_value (level : Level) (lower : List Level) (a : Array Rat) :
    denseEval lower level.root.toComplex level.degree
        (Arithmetic.Coeff.value level lower a) =
      denote (level :: lower) a := by
  rw [denseEval, denote_cons]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < level.degree := Finset.mem_range.mp hi
  congr 1
  simp [Arithmetic.Coeff.value, Arithmetic.Coeff.ofData,
    coeffDenote, Array.getD, hi', denote_fixed]

/-- The executable monic level relation evaluates to zero at the stored root. -/
theorem denseEval_relation (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    denseEval lower level.root.toComplex (level.degree + 1)
        (Arithmetic.Coeff.relation level lower) = 0 := by
  rw [denseEval, Finset.sum_range_succ]
  have hbelow : ∀ j < level.degree,
      (Arithmetic.Coeff.relation level lower).coeff j =
        Arithmetic.Coeff.ofData lower (level.defining.getD j #[]) := by
    intro j hj
    rw [Arithmetic.Coeff.relation, DensePoly.coeff_ofCoeffs]
    have hj' : j <
        (((List.range level.degree).map fun i =>
          Arithmetic.Coeff.ofData lower
            (level.defining.getD i #[])).toArray).size := by
      simpa using hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hj']
    simp [Array.getD_eq_getD_getElem?]
  have htop : (Arithmetic.Coeff.relation level lower).coeff level.degree = 1 := by
    simp [Arithmetic.Coeff.relation, Array.getD]
  have hsum :
      (∑ j ∈ Finset.range level.degree,
          coeffDenote lower
              ((Arithmetic.Coeff.relation level lower).coeff j) *
            level.root.toComplex ^ j) =
        ∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) *
            level.root.toComplex ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbelow j (Finset.mem_range.mp hj)]
    simp [Arithmetic.Coeff.ofData, coeffDenote, denote_fixed]
  rw [hsum]
  rw [htop, coeffDenote_one lower hvalid.2.2]
  simpa using relation_sum level lower hvalid

/-- The inversion input polynomial lies strictly below the current defining
degree. -/
theorem value_degree_lt (level : Level) (lower : List Level) (a : Array Rat)
    (hdegree : 0 < level.degree) :
    (Arithmetic.Coeff.value level lower a).degree?.getD 0 < level.degree := by
  have hsize : (Arithmetic.Coeff.value level lower a).size ≤ level.degree :=
    (DensePoly.size_ofCoeffs_le _).trans (by
      simp)
  by_cases hzero : (Arithmetic.Coeff.value level lower a).size = 0
  · simp [DensePoly.degree?, hzero, hdegree]
  · rw [DensePoly.degree?_eq_some_of_pos_size _ (Nat.pos_of_ne_zero hzero),
      Option.getD_some]
    omega

/-- Evaluation at the selected generator distinguishes all lower-coefficient
polynomials below the defining degree. This is the exact semantic consequence
of irreducibility needed to construct the next tower embedding. -/
def Separates (level : Level) (lower : List Level) : Prop :=
  ∀ f g : DensePoly (Arithmetic.Coeff lower),
    f.degree?.getD 0 < level.degree →
    g.degree?.getD 0 < level.degree →
    denseEval lower level.root.toComplex level.degree f =
    denseEval lower level.root.toComplex level.degree g →
    f = g

/-- Rational fixed-width coefficients have unique complex denotation. -/
theorem DenoteInjective.nil : DenoteInjective [] := by
  intro a b hab
  apply coeff_eq_of_data_eq
  have haSize : a.data.size = 1 := by
    simpa [levelsDim] using a.size_eq
  have hbSize : b.data.size = 1 := by
    simpa [levelsDim] using b.size_eq
  have hvalue : a.data.getD 0 0 = b.data.getD 0 0 := by
    change ((a.data.getD 0 0 : Rat) : ℂ) =
      ((b.data.getD 0 0 : Rat) : ℂ) at hab
    exact_mod_cast hab
  apply Array.ext
  · omega
  · intro i hai hbi
    have hi : i = 0 := by omega
    subst i
    simpa [Array.getD, haSize, hbSize] using hvalue

/-- The nested-coefficient view `Arithmetic.Coeff.value` determines the flat
coordinate data, so equal values give equal canonical coefficients. -/
private theorem value_injective (level : Level) (lower : List Level)
    (hlowerDim : 0 < levelsDim lower)
    {a b : Arithmetic.Coeff (level :: lower)}
    (hvalue : Arithmetic.Coeff.value level lower a.data =
      Arithmetic.Coeff.value level lower b.data) :
    a = b := by
  apply coeff_eq_of_data_eq
  apply Array.ext
  · exact a.size_eq.trans b.size_eq.symm
  · intro k hka hkb
    have hk : k < level.degree * levelsDim lower := by
      have hka' := hka
      rw [a.size_eq] at hka'
      simpa [levelsDim] using hka'
    let i := k / levelsDim lower
    let j := k % levelsDim lower
    have hi : i < level.degree := by
      dsimp [i]
      exact (Nat.div_lt_iff_lt_mul hlowerDim).2 (by
        simpa [Nat.mul_comm] using hk)
    have hj : j < levelsDim lower := by
      exact Nat.mod_lt _ hlowerDim
    have hcoefficient := congrArg
      (fun f : DensePoly (Arithmetic.Coeff lower) => f.coeff i) hvalue
    have hblock : Arithmetic.block a.data i (levelsDim lower) =
        Arithmetic.block b.data i (levelsDim lower) := by
      simp only [Arithmetic.Coeff.value, DensePoly.coeff_ofCoeffs]
        at hcoefficient
      have hdata := congrArg Arithmetic.Coeff.data hcoefficient
      simpa [Arithmetic.Coeff.ofData, Arithmetic.fixedCoeffs,
        Arithmetic.block, Array.getD, hi] using hdata
    have hentry := congrArg
      (fun data : Array Rat => data.getD j 0) hblock
    have hkdecomp : i * levelsDim lower + j = k := by
      dsimp [i, j]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod k (levelsDim lower)
    simp [Arithmetic.block, Array.getD, hj] at hentry
    rw [hkdecomp] at hentry
    simpa [hka, hkb] using hentry

/-- Separating evaluation at one level extends injectivity of the lower fixed
embedding to injectivity of the next canonical coefficient carrier. -/
theorem DenoteInjective.cons (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) (hseparates : Separates level lower) :
    DenoteInjective (level :: lower) := by
  intro a b hab
  apply value_injective level lower (levelsDim_pos lower hvalid.2.2)
  apply hseparates
  · exact value_degree_lt level lower a.data
      (Nat.zero_lt_of_lt hvalid.1.1)
  · exact value_degree_lt level lower b.data
      (Nat.zero_lt_of_lt hvalid.1.1)
  · rw [denseEval_value, denseEval_value]
    exact hab

/-- The executable relation retains its monic top coefficient and therefore
has exactly defining degree plus one stored coefficients. -/
theorem relation_size (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    (Arithmetic.Coeff.relation level lower).size = level.degree + 1 := by
  have hle : (Arithmetic.Coeff.relation level lower).size ≤
      level.degree + 1 := (DensePoly.size_ofCoeffs_le _).trans (by
    simp)
  have htop : (Arithmetic.Coeff.relation level lower).coeff level.degree = 1 := by
    simp [Arithmetic.Coeff.relation, Array.getD]
  have hone : (1 : Arithmetic.Coeff lower) ≠ 0 := by
    intro h
    have hmap := congrArg (coeffDenote lower) h
    rw [coeffDenote_one lower hvalid.2.2, coeffDenote_zero lower] at hmap
    exact one_ne_zero hmap
  have hnle : ¬ (Arithmetic.Coeff.relation level lower).size ≤
      level.degree := by
    intro hsize
    exact hone (htop.symm.trans
      (DensePoly.coeff_eq_zero_of_size_le _ hsize))
  omega

/-- The executable relation has its advertised defaulted degree. -/
theorem relation_degree (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    (Arithmetic.Coeff.relation level lower).degree?.getD 0 = level.degree := by
  rw [DensePoly.degree?_eq_some_of_pos_size _ (by
      rw [relation_size level lower hvalid]
      omega), Option.getD_some, relation_size level lower hvalid]
  omega

/-- An irreducible defining relation that vanishes at the selected generator
makes evaluation injective below its degree. -/
theorem separates_of_irreducible (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hlowerInv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hlowerInv
    Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level lower)) →
      Separates level lower := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hlowerInv
  intro hirreducible
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    coeffHom lower hvalid.2.2 hlowerInjective hlowerInv
  letI : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    change relation.leadingCoeff = 1
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [relation_size level lower hvalid]
      omega), relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hpEval : Polynomial.aeval level.root.toComplex p = 0 := by
    change denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv relation = 0
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv (level.degree + 1) relation (by
        rw [relation_degree level lower hvalid]
        omega)]
    exact denseEval_relation level lower hvalid
  have hpMin : p = minpoly (Arithmetic.Coeff lower)
      level.root.toComplex :=
    minpoly.eq_of_irreducible_of_monic hirreducible hpEval hpMonic
  intro f g hf hg heval
  let fp := HexPolyMathlib.toPolynomial f
  let gp := HexPolyMathlib.toPolynomial g
  have hmap : Polynomial.aeval level.root.toComplex fp =
      Polynomial.aeval level.root.toComplex gp := by
    change denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv f =
        denseMap lower level.root.toComplex hvalid.2.2
          hlowerInjective hlowerInv g
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
        hlowerInjective hlowerInv level.degree f hf,
      denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
        hlowerInjective hlowerInv level.degree g hg]
    exact heval
  have hzero : Polynomial.aeval level.root.toComplex (fp - gp) = 0 := by
    rw [map_sub, hmap, sub_self]
  have hdvd : p ∣ fp - gp := by
    rw [hpMin]
    exact minpoly.dvd (Arithmetic.Coeff lower) level.root.toComplex hzero
  have hdiff : fp - gp = 0 := by
    by_contra hne
    have hlower := Polynomial.natDegree_le_of_dvd hdvd hne
    have hupper : (fp - gp).natDegree < level.degree :=
      (Polynomial.natDegree_sub_le fp gp).trans_lt (max_lt
        (by simpa [fp] using hf) (by simpa [gp] using hg))
    have hpDegree : p.natDegree = level.degree := by
      simpa [p, relation] using relation_degree level lower hvalid
    rw [hpDegree] at hlower
    omega
  have hpoly : fp = gp := sub_eq_zero.mp hdiff
  calc
    f = HexPolyMathlib.ofPolynomial fp := by
      simp [fp]
    _ = HexPolyMathlib.ofPolynomial gp := by rw [hpoly]
    _ = g := by simp [gp]

/-- Injectivity of canonical extended coordinates forces the monic level
relation to be the minimal polynomial of the selected generator over the
lower coefficient field. -/
theorem relation_irreducible_of_injective (level : Level)
    (lower : List Level) (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hlowerInv : ∀ a : Arithmetic.Coeff lower,
      coeffDenote lower a⁻¹ = (coeffDenote lower a)⁻¹) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hlowerInv
    Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level lower)) := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hlowerInv
  let relation := Arithmetic.Coeff.relation level lower
  let p := HexPolyMathlib.toPolynomial relation
  let ι : Arithmetic.Coeff lower →+* ℂ :=
    coeffHom lower hvalid.2.2 hlowerInjective hlowerInv
  letI : Algebra (Arithmetic.Coeff lower) ℂ := ι.toAlgebra
  have hpMonic : p.Monic := by
    rw [Polynomial.Monic.def]
    change (HexPolyMathlib.toPolynomial relation).leadingCoeff = 1
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    change relation.leadingCoeff = 1
    rw [DensePoly.leadingCoeff_eq_coeff_last relation (by
      rw [relation_size level lower hvalid]
      omega), relation_size level lower hvalid]
    simp [relation, Arithmetic.Coeff.relation, Array.getD]
  have hpEval : Polynomial.aeval level.root.toComplex p = 0 := by
    change denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv relation = 0
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hlowerInv (level.degree + 1) relation (by
        rw [relation_degree level lower hvalid]
        omega)]
    exact denseEval_relation level lower hvalid
  have hintegral : IsIntegral (Arithmetic.Coeff lower)
      level.root.toComplex := ⟨p, hpMonic, hpEval⟩
  let q := minpoly (Arithmetic.Coeff lower) level.root.toComplex
  have hqDegree : level.degree ≤ q.natDegree := by
    by_contra hdegree
    have hlt : q.natDegree < level.degree := by omega
    let dense : DensePoly (Arithmetic.Coeff lower) :=
      HexPolyMathlib.ofPolynomial q
    have hdenseDegree : dense.degree?.getD 0 < level.degree := by
      rw [← HexPolyMathlib.natDegree_toPolynomial]
      simpa [dense]
    have hdenseEval :
        denseEval lower level.root.toComplex level.degree dense = 0 := by
      rw [← denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
        hlowerInjective hlowerInv level.degree dense hdenseDegree]
      simp only [denseMap, dense,
        HexPolyMathlib.toPolynomial_ofPolynomial]
      change q.eval₂ ι level.root.toComplex = 0
      rw [← RingHom.algebraMap_toAlgebra ι]
      rw [← Polynomial.aeval_def]
      exact minpoly.aeval _ _
    have hdenseZero : dense = 0 :=
      dense_eq_zero_of_eval level lower hinjective dense
        hdenseDegree hdenseEval
    have hqZero : q = 0 := by
      have hmapped := congrArg HexPolyMathlib.toPolynomial hdenseZero
      simpa [dense] using hmapped
    exact (minpoly.ne_zero hintegral) hqZero
  have hpDegree : p.natDegree = level.degree := by
    simpa [p, relation] using relation_degree level lower hvalid
  have hqDvd : q ∣ p := minpoly.dvd _ _ hpEval
  have hpEq : p = q := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hintegral) hpMonic hqDvd
    rw [hpDegree]
    exact hqDegree
  change Irreducible p
  rw [hpEq]
  exact minpoly.irreducible hintegral

/-- For a nonzero input, the executable monic one-sided extended gcd with
the defining relation returns a nonzero constant gcd. -/
theorem xgcdLeftMonic_size_one (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hinv : ∀ b : Arithmetic.Coeff lower,
      coeffDenote lower b⁻¹ = (coeffDenote lower b)⁻¹)
    (a : Array Rat) (ha : denote (level :: lower) a ≠ 0) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hinv
    (DensePoly.xgcdLeftMonic (Arithmetic.Coeff.value level lower a)
      (Arithmetic.Coeff.relation level lower)).gcd.size = 1 := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hinv
  let value := Arithmetic.Coeff.value level lower a
  let relation := Arithmetic.Coeff.relation level lower
  let result := DensePoly.xgcdLeftMonic value relation
  let gcd := result.gcd
  change gcd.size = 1
  have hvalueDegree : value.degree?.getD 0 < level.degree :=
    value_degree_lt level lower a (Nat.zero_lt_of_lt hvalid.1.1)
  have hrelationDegree : relation.degree?.getD 0 = level.degree :=
    relation_degree level lower hvalid
  have hvalueMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv value = denote (level :: lower) a := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree value hvalueDegree]
    exact denseEval_value level lower a
  have hrelationMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv relation = 0 := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv (level.degree + 1) relation (by omega)]
    exact denseEval_relation level lower hvalid
  have hvalueNe : value ≠ 0 := by
    intro hzero
    apply ha
    rw [← hvalueMap, hzero,
      denseMap_zero lower level.root.toComplex hvalid.2.2
        hlowerInjective hinv]
  have hrelationNe : relation ≠ 0 := by
    intro hzero
    have hsize := relation_size level lower hvalid
    change relation.size = level.degree + 1 at hsize
    rw [hzero, DensePoly.size_zero] at hsize
    omega
  have hgcdDvdValue : gcd ∣ value :=
    (DensePoly.xgcdLeftMonic_dvd value relation).1
  have hgcdDvdRelation : gcd ∣ relation :=
    (DensePoly.xgcdLeftMonic_dvd value relation).2
  have hgcdNe : gcd ≠ 0 := by
    intro hzero
    rcases hgcdDvdValue with ⟨q, hq⟩
    apply hvalueNe
    rw [hq, hzero]
    exact DensePoly.zero_mul q
  have hgcdDegree : gcd.degree?.getD 0 < level.degree := by
    have hpolyValue : HexPolyMathlib.toPolynomial value ≠ 0 :=
      toPolynomial_ne_zero hvalueNe
    have hle := Polynomial.natDegree_le_of_dvd
      (toPolynomial_dvd hgcdDvdValue) hpolyValue
    rw [HexPolyMathlib.natDegree_toPolynomial,
      HexPolyMathlib.natDegree_toPolynomial] at hle
    exact hle.trans_lt hvalueDegree
  have hgcdMapNe : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv gcd ≠ 0 := by
    intro hmap
    apply hgcdNe
    apply dense_eq_zero_of_eval level lower hinjective gcd hgcdDegree
    rw [← denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree gcd hgcdDegree]
    exact hmap
  rcases hgcdDvdRelation with ⟨factor, hfactor⟩
  have hfactorNe : factor ≠ 0 := by
    intro hzero
    apply hrelationNe
    rw [hfactor, hzero]
    rw [DensePoly.mul_comm_poly gcd 0]
    exact DensePoly.zero_mul gcd
  have hgcdDegreeZero : gcd.degree?.getD 0 = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hgcdPos
    have hfactorDegree : factor.degree?.getD 0 < level.degree := by
      have hgcdPolyNe : HexPolyMathlib.toPolynomial gcd ≠ 0 :=
        toPolynomial_ne_zero hgcdNe
      have hfactorPolyNe : HexPolyMathlib.toPolynomial factor ≠ 0 :=
        toPolynomial_ne_zero hfactorNe
      have hsum : level.degree =
          gcd.degree?.getD 0 + factor.degree?.getD 0 := by
        calc
          level.degree = (HexPolyMathlib.toPolynomial relation).natDegree := by
            simpa using hrelationDegree.symm
          _ = (HexPolyMathlib.toPolynomial (gcd * factor)).natDegree := by
            rw [← hfactor]
          _ = (HexPolyMathlib.toPolynomial gcd *
                HexPolyMathlib.toPolynomial factor).natDegree := by
            rw [HexPolyMathlib.toPolynomial_mul]
          _ = (HexPolyMathlib.toPolynomial gcd).natDegree +
                (HexPolyMathlib.toPolynomial factor).natDegree := by
            rw [Polynomial.natDegree_mul hgcdPolyNe hfactorPolyNe]
          _ = gcd.degree?.getD 0 + factor.degree?.getD 0 := by
            rw [HexPolyMathlib.natDegree_toPolynomial,
              HexPolyMathlib.natDegree_toPolynomial]
      omega
    have hfactorMap : denseMap lower level.root.toComplex hvalid.2.2
        hlowerInjective hinv factor = 0 := by
      have hproduct :
          denseMap lower level.root.toComplex hvalid.2.2 hlowerInjective hinv gcd *
              denseMap lower level.root.toComplex hvalid.2.2 hlowerInjective hinv factor = 0 := by
        rw [← denseMap_mul lower level.root.toComplex hvalid.2.2
          hlowerInjective hinv gcd factor, ← hfactor]
        exact hrelationMap
      exact (mul_eq_zero.mp hproduct).resolve_left hgcdMapNe
    apply hfactorNe
    apply dense_eq_zero_of_eval level lower hinjective factor hfactorDegree
    rw [← denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree factor hfactorDegree]
    exact hfactorMap
  have hgcdSizePos : 0 < gcd.size := by
    by_contra hpos
    apply hgcdNe
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le gcd (by omega)
  rw [DensePoly.degree?_eq_some_of_pos_size gcd hgcdSizePos,
    Option.getD_some] at hgcdDegreeZero
  omega

/-- The normalized monic extended-gcd coefficient used by executable
inversion denotes the reciprocal of a nonzero top-level coordinate array. -/
theorem denote_xgcd_inverse (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (hlowerInjective : DenoteInjective lower)
    (hinv : ∀ b : Arithmetic.Coeff lower,
      coeffDenote lower b⁻¹ = (coeffDenote lower b)⁻¹)
    (a : Array Rat) (ha : denote (level :: lower) a ≠ 0) :
    letI : Field (Arithmetic.Coeff lower) :=
      coeffField lower hvalid.2.2 hlowerInjective hinv
    let value := Arithmetic.Coeff.value level lower a
    let relation := Arithmetic.Coeff.relation level lower
    let result := DensePoly.xgcdLeftMonic value relation
    let c := result.gcd.leadingCoeff
    let normalized := DensePoly.scale c⁻¹ result.left % relation
    denote (level :: lower)
        (Arithmetic.flattenBlocks level.degree (levelsDim lower)
          (((List.range level.degree).map fun i =>
            (normalized.coeff i).data).toArray)) =
      (denote (level :: lower) a)⁻¹ := by
  letI : Field (Arithmetic.Coeff lower) :=
    coeffField lower hvalid.2.2 hlowerInjective hinv
  let value := Arithmetic.Coeff.value level lower a
  let relation := Arithmetic.Coeff.relation level lower
  let result := DensePoly.xgcdLeftMonic value relation
  let c := result.gcd.leadingCoeff
  let scaled := DensePoly.scale c⁻¹ result.left
  change denote (level :: lower)
      (Arithmetic.flattenBlocks level.degree (levelsDim lower)
        (((List.range level.degree).map fun i =>
          ((scaled % relation).coeff i).data).toArray)) = _
  have hvalueDegree : value.degree?.getD 0 < level.degree :=
    value_degree_lt level lower a (Nat.zero_lt_of_lt hvalid.1.1)
  have hrelationDegree : relation.degree?.getD 0 = level.degree :=
    relation_degree level lower hvalid
  have hvalueMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv value = denote (level :: lower) a := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv level.degree value hvalueDegree]
    exact denseEval_value level lower a
  have hrelationMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv relation = 0 := by
    rw [denseMap_eq_denseEval lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv (level.degree + 1) relation (by omega)]
    exact denseEval_relation level lower hvalid
  have hgcdSize : result.gcd.size = 1 := by
    exact xgcdLeftMonic_size_one level lower hvalid hinjective
      hlowerInjective hinv a ha
  have hcNe : c ≠ 0 := by
    exact DensePoly.leadingCoeff_ne_zero_of_pos_size result.gcd
      (by rw [hgcdSize]; exact Nat.zero_lt_one)
  have hgcdC : result.gcd = DensePoly.C c :=
    eq_C_leadingCoeff_of_size_one result.gcd hgcdSize
  obtain ⟨t, hbezout⟩ := DensePoly.xgcdLeftMonic_bezout value relation
  change result.left * value + t * relation = result.gcd at hbezout
  have hmapBezout := congrArg
    (denseMap lower level.root.toComplex hvalid.2.2 hlowerInjective hinv)
    hbezout
  rw [denseMap_add, denseMap_mul, denseMap_mul, hrelationMap, mul_zero,
    add_zero, hgcdC, denseMap_C] at hmapBezout
  have hcMapNe : coeffDenote lower c ≠ 0 := by
    intro hmap
    apply hcNe
    apply hlowerInjective
    rw [hmap, coeffDenote_zero]
  have hscaledMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv scaled =
      (coeffDenote lower c)⁻¹ *
        denseMap lower level.root.toComplex hvalid.2.2
          hlowerInjective hinv result.left := by
    rw [denseMap_scale]
    exact congrArg (· * denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv result.left) (hinv c)
  have hnormalizedMap : denseMap lower level.root.toComplex hvalid.2.2
      hlowerInjective hinv (scaled % relation) =
      denseMap lower level.root.toComplex hvalid.2.2
        hlowerInjective hinv scaled := by
    have hdivision := EuclideanDomain.mod_add_div
      (HexPolyMathlib.toPolynomial scaled)
      (HexPolyMathlib.toPolynomial relation)
    have hmapDivision := congrArg
      (Polynomial.eval₂ (coeffHom lower hvalid.2.2 hlowerInjective hinv)
        level.root.toComplex) hdivision
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul] at hmapDivision
    have hrelationPolynomial :
        (HexPolyMathlib.toPolynomial relation).eval₂
            (coeffHom lower hvalid.2.2 hlowerInjective hinv)
            level.root.toComplex = 0 := hrelationMap
    rw [hrelationPolynomial, zero_mul, add_zero] at hmapDivision
    rw [denseMap, HexPolyMathlib.toPolynomial_mod, denseMap]
    exact hmapDivision
  have hnormalizedDegree : (scaled % relation).degree?.getD 0 < level.degree := by
    rw [← hrelationDegree]
    exact DensePoly.mod_degree_lt_of_pos_degree scaled relation (by
      rw [hrelationDegree]
      exact Nat.zero_lt_of_lt hvalid.1.1)
  rw [denote_flatten_dense, ← denseMap_eq_denseEval lower
    level.root.toComplex hvalid.2.2 hlowerInjective hinv level.degree
    (scaled % relation) hnormalizedDegree, hnormalizedMap, hscaledMap]
  apply (mul_eq_one_iff_eq_inv₀ ha).mp
  rw [mul_assoc, ← hvalueMap, hmapBezout]
  exact inv_mul_cancel₀ hcMapNe

/-- A lower-tower coefficient embedded as the constant coefficient of one
extension level. -/
@[expose]
def liftCoeff (level : Level) (lower : List Level)
    (a : Arithmetic.Coeff lower) : Arithmetic.Coeff (level :: lower) :=
  ⟨Arithmetic.flattenBlocks level.degree (levelsDim lower) #[a.data], by
    simp [levelsDim]⟩

/-- Constant-block embedding preserves coefficient denotation. -/
theorem coeffDenote_lift (level : Level) (lower : List Level)
    (hdegree : 0 < level.degree) (a : Arithmetic.Coeff lower) :
    coeffDenote (level :: lower) (liftCoeff level lower a) =
      coeffDenote lower a := by
  rw [coeffDenote, liftCoeff, denote_flatten]
  change (∑ i ∈ Finset.range level.degree,
      denote lower ((#[a.data] : Array (Array Rat)).getD i #[]) *
        level.root.toComplex ^ i) = denote lower a.data
  calc
    _ = denote lower ((#[a.data] : Array (Array Rat)).getD 0 #[]) *
        level.root.toComplex ^ 0 := by
      apply Finset.sum_eq_single 0
      · intro i hi hi0
        have hget : (#[a.data] : Array (Array Rat)).getD i #[] = #[] := by
          simp [Array.getD, hi0]
        rw [hget, ← denote_fixed lower #[], denote_zero]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hdegree)).elim
    _ = denote lower a.data := by simp [Array.getD]

/-- Injectivity at an extension level implies injectivity for its lower
coefficient tower. -/
theorem DenoteInjective.tail (level : Level) (lower : List Level)
    (hdegree : 1 < level.degree) (hinjective : DenoteInjective (level :: lower)) :
    DenoteInjective lower := by
  have hpositive : 0 < level.degree := Nat.zero_lt_of_lt hdegree
  intro a b hab
  have hlift : liftCoeff level lower a = liftCoeff level lower b := by
    apply hinjective
    rw [coeffDenote_lift level lower hpositive,
      coeffDenote_lift level lower hpositive]
    exact hab
  have hblock := congrArg
    (fun c : Arithmetic.Coeff (level :: lower) =>
      Arithmetic.block c.data 0 (levelsDim lower)) hlift
  simp only [liftCoeff] at hblock
  rw [Arithmetic.block_flatten level.degree (levelsDim lower) 0 #[a.data]
      hpositive,
    Arithmetic.block_flatten level.degree (levelsDim lower) 0 #[b.data]
      hpositive] at hblock
  simp [Array.getD] at hblock
  rw [fixedCoeffs_eq_self lower a, fixedCoeffs_eq_self lower b] at hblock
  cases a with
  | mk ad ha =>
      cases b with
      | mk bd hb =>
          simp only at hblock
          cases hblock
          rfl

/-- The executable fixed-width all-zero test is equivalent to semantic zero
when canonical coefficient denotation is injective. -/
theorem fixed_all_zero_iff (levels : List Level)
    (hinjective : DenoteInjective levels) (a : Array Rat) :
    (Arithmetic.fixedCoeffs (levelsDim levels) a).all (fun q => q = 0) = true ↔
      denote levels a = 0 := by
  constructor
  · intro hall
    rw [← denote_fixed levels a]
    have hdata : Arithmetic.fixedCoeffs (levelsDim levels) a =
        Arithmetic.fixedCoeffs (levelsDim levels) #[] := by
      apply Array.ext
      · simp [Arithmetic.fixedCoeffs]
      · intro i hi₁ hi₂
        have hi := (Array.all_eq_true.mp hall) i hi₁
        simpa [Arithmetic.fixedCoeffs, Array.getD] using hi
    rw [hdata, denote_zero]
  · intro hdenote
    have hcoeff : Arithmetic.Coeff.ofData levels a = 0 := by
      apply hinjective
      change denote levels (Arithmetic.fixedCoeffs (levelsDim levels) a) =
        coeffDenote levels 0
      rw [denote_fixed, hdenote, coeffDenote_zero]
    have hdata := congrArg Arithmetic.Coeff.data hcoeff
    change Arithmetic.fixedCoeffs (levelsDim levels) a =
      Arithmetic.fixedCoeffs (levelsDim levels) #[] at hdata
    rw [Array.all_eq_true]
    intro i hi
    have hentry := congrArg (fun data : Array Rat => data.getD i 0) hdata
    have hiBound : i < levelsDim levels := by
      simpa [Arithmetic.fixedCoeffs] using hi
    simpa [Arithmetic.fixedCoeffs, Array.getD, hiBound] using hentry

/-- Recursive extended-gcd coordinates denote complex inversion at every
validated tower depth, including the executable `0⁻¹ = 0` convention. -/
theorem denote_invCoords (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : DenoteInjective levels) (a : Array Rat) :
    denote levels (Arithmetic.invCoords levels a) = (denote levels a)⁻¹ := by
  induction levels generalizing a with
  | nil =>
      rw [show Arithmetic.invCoords [] a =
        #[if a.getD 0 0 = 0 then 0 else (a.getD 0 0)⁻¹] from rfl]
      simp only [denote]
      by_cases h : a[0]?.getD 0 = 0 <;> simp [h]
  | cons level lower ih =>
      have hlowerInjective : DenoteInjective lower :=
        DenoteInjective.tail level lower
          hvalid.1.1 hinjective
      have hlowerInv : ∀ b : Arithmetic.Coeff lower,
          coeffDenote lower b⁻¹ = (coeffDenote lower b)⁻¹ := by
        intro b
        change denote lower
            (Arithmetic.fixedCoeffs (levelsDim lower)
              (Arithmetic.invCoords lower b.data)) =
          (denote lower b.data)⁻¹
        rw [denote_fixed]
        exact ih hvalid.2.2 hlowerInjective b.data
      letI : Field (Arithmetic.Coeff lower) :=
        coeffField lower hvalid.2.2 hlowerInjective hlowerInv
      let zeroTest :=
        (Arithmetic.fixedCoeffs
          (level.degree * levelsDim lower) a).all (fun q => q = 0)
      by_cases hzero : zeroTest = true
      · have hdenote : denote (level :: lower) a = 0 :=
          (fixed_all_zero_iff (level :: lower) hinjective a).mp (by
            simpa [zeroTest, levelsDim] using hzero)
        have hrep : Array.replicate (level.degree * levelsDim lower) 0 =
            Arithmetic.fixedCoeffs (levelsDim (level :: lower)) #[] := by
          apply Array.ext
          · simp [levelsDim, Arithmetic.fixedCoeffs]
          · intro i hi₁ hi₂
            simp [Arithmetic.fixedCoeffs, Array.getD]
        rw [Arithmetic.invCoords]
        rw [show (Arithmetic.fixedCoeffs
            (level.degree * levelsDim lower) a).all (fun q => q = 0) = true by
          simpa [zeroTest] using hzero]
        simp only [if_true]
        rw [hrep, denote_zero, hdenote]
        simp
      · have ha : denote (level :: lower) a ≠ 0 := by
          intro hdenote
          apply hzero
          simpa [zeroTest, levelsDim] using
            (fixed_all_zero_iff (level :: lower) hinjective a).mpr hdenote
        have hgcdSize := xgcdLeftMonic_size_one level lower hvalid
          hinjective hlowerInjective hlowerInv a ha
        let value := Arithmetic.Coeff.value level lower a
        let relation := Arithmetic.Coeff.relation level lower
        let result := DensePoly.xgcdLeftMonic value relation
        have hcNe : result.gcd.leadingCoeff ≠ 0 := by
          exact DensePoly.leadingCoeff_ne_zero_of_pos_size result.gcd
            (by rw [hgcdSize]; exact Nat.zero_lt_one)
        rw [Arithmetic.invCoords]
        rw [show (Arithmetic.fixedCoeffs
            (level.degree * levelsDim lower) a).all (fun q => q = 0) = false by
          exact Bool.eq_false_of_not_eq_true hzero]
        simp only [Bool.false_eq_true, if_false]
        rw [if_pos hgcdSize, if_neg hcNe]
        exact denote_xgcd_inverse level lower hvalid hinjective
          hlowerInjective hlowerInv a ha

/-- Executable inversion of a canonical coefficient preserves denotation at
any validated level list with an injective fixed embedding. -/
theorem coeffDenote_inv (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : DenoteInjective levels) (a : Arithmetic.Coeff levels) :
    coeffDenote levels a⁻¹ = (coeffDenote levels a)⁻¹ := by
  change denote levels
      (Arithmetic.fixedCoeffs (levelsDim levels)
        (Arithmetic.invCoords levels a.data)) =
    (denote levels a.data)⁻¹
  rw [denote_fixed]
  exact denote_invCoords levels hvalid hinjective a.data

/-- Evaluation at any complex zero of the mapped defining relation is a ring
homomorphism from the canonical top-level coefficient field. -/
@[expose]
noncomputable def conjugateHom (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0) :
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffField (level :: lower) hvalid hinjective
        (coeffDenote_inv (level :: lower) hvalid hinjective)
    Arithmetic.Coeff (level :: lower) →+* ℂ := by
  letI : Field (Arithmetic.Coeff (level :: lower)) :=
    coeffField (level :: lower) hvalid hinjective
      (coeffDenote_inv (level :: lower) hvalid hinjective)
  exact
    { toFun := fun a => evalAt level lower x a.data
      map_zero' := evalAt_zero level lower hvalid x
      map_one' := evalAt_one level lower hvalid x
      map_add' := evalAt_add level lower hvalid x
      map_mul' := fun a b =>
        evalAt_mul level lower hvalid x hrelation a.data b.data }

@[simp]
theorem conjugateHom_apply (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower))
    (hinjective : DenoteInjective (level :: lower))
    (x : ℂ)
    (hrelation :
      (∑ j ∈ Finset.range level.degree,
          denote lower (level.defining.getD j #[]) * x ^ j) +
        x ^ level.degree = 0)
    (a : Arithmetic.Coeff (level :: lower)) :
    letI : Field (Arithmetic.Coeff (level :: lower)) :=
      coeffField (level :: lower) hvalid hinjective
        (coeffDenote_inv (level :: lower) hvalid hinjective)
    conjugateHom level lower hvalid hinjective x hrelation a =
      evalAt level lower x a.data := by
  rfl

/-- Executable inversion at the rational base preserves denotation. -/
theorem coeffDenote_inv_nil (a : Arithmetic.Coeff []) :
    coeffDenote [] a⁻¹ = (coeffDenote [] a)⁻¹ := by
  change denote []
      (Arithmetic.fixedCoeffs (levelsDim [])
        (Arithmetic.invCoords [] a.data)) =
    (denote [] a.data)⁻¹
  rw [denote_fixed]
  exact denote_invCoords [] trivial DenoteInjective.nil a.data

/-- Canonical base-tower coefficients are the rational field. -/
@[expose, reducible]
noncomputable def coeffFieldNil : Field (Arithmetic.Coeff []) :=
  coeffField [] (by exact trivial) DenoteInjective.nil coeffDenote_inv_nil

/-- Canonical base-tower coefficients are ring-equivalent to the rationals. -/
noncomputable def coeffRatEquiv :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    Arithmetic.Coeff [] ≃+* Rat := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  refine
    { toFun := fun a => a.data.getD 0 0
      invFun := fun q => Arithmetic.Coeff.ofData [] #[q]
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_ }
  · intro a
    cases a with
    | mk data hsize =>
        have hdata : Arithmetic.fixedCoeffs (levelsDim []) #[data.getD 0 0] =
            data := by
          apply Array.ext
          · simp [Arithmetic.fixedCoeffs, levelsDim, hsize]
          · intro i hi₁ hi₂
            have hi : i = 0 := by
              simp [Arithmetic.fixedCoeffs, levelsDim] at hi₁
              omega
            subst i
            simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD, hsize]
        have coeff_ext (x y : Arithmetic.Coeff [])
            (h : x.data = y.data) : x = y := by
          cases x with
          | mk xdata xsize =>
              cases y with
              | mk ydata ysize =>
                  simp only at h
                  subst ydata
                  rfl
        exact coeff_ext _ _ hdata
  · intro q
    change (Arithmetic.fixedCoeffs (levelsDim []) #[q]).getD 0 0 = q
    simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD]
  · intro a b
    change (Arithmetic.mulCoords [] a.data b.data).getD 0 0 =
      a.data.getD 0 0 * b.data.getD 0 0
    simp [Arithmetic.mulCoords, Array.getD]
  · intro a b
    change (Arithmetic.addCoords (levelsDim []) a.data b.data).getD 0 0 =
      a.data.getD 0 0 + b.data.getD 0 0
    simp [Arithmetic.addCoords, levelsDim, Array.getD]

/-- Under the rational identification of base-tower coefficients, rebuilding
from raw data reads off its first entry. -/
@[simp]
theorem coeffRatEquiv_ofData (data : Array Rat) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    coeffRatEquiv (Arithmetic.Coeff.ofData [] data) = data.getD 0 0 := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  change (Arithmetic.fixedCoeffs (levelsDim []) data).getD 0 0 =
    data.getD 0 0
  simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD]

/-- Mapping a raw base-tower polynomial through the canonical rational
equivalence recovers the rational polynomial stored by its coordinates. -/
theorem map_rawPoly_nil (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).map
        coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial (Factor.toRatPoly f) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial]
  by_cases hn : n < f.size
  · simp [Factor.rawPoly, Factor.toRatPoly, DensePoly.coeff_ofCoeffs,
      Array.getD, hn, coeffRatEquiv_ofData]
  · simp [Factor.rawPoly, Factor.toRatPoly, DensePoly.coeff_ofCoeffs,
      Array.getD, hn]
    exact coeffRatEquiv.map_zero

/-- The rational-base arm of the recursive checker proves ordinary
irreducibility after transporting canonical base coefficients to `Rat`. -/
theorem isIrreducible_nil_toMathlib (f : Array (Array Rat))
    (hcheck : Factor.isIrreducible [] f = true) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    Irreducible (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  simp only [Factor.isIrreducible, Bool.and_eq_true] at hcheck
  have hdegree := hcheck.1.1.1
  have hirreducible := hcheck.2
  have hdegree' : 0 < (Factor.rawPoly [] f).degree?.getD 0 :=
    of_decide_eq_true hdegree
  let raw := Factor.toRatPoly f
  let primitive := ZPoly.ratPolyPrimitivePart raw
  have hirreducibleInt :
      Irreducible (HexPolyZMathlib.toPolynomial primitive) :=
    (ZPoly.Irreducible_iff_polynomialIrreducible primitive).mp
      ((ZPoly.isIrreducible_iff primitive).mp hirreducible)
  have hprimitiveNe : primitive ≠ 0 := by
    intro hzero
    apply hirreducibleInt.ne_zero
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero
  have hprimitiveRatNe : HexPolyZMathlib.toPolyℚ primitive ≠ 0 :=
    HexPolyZMathlib.toPolyℚ_ne_zero hprimitiveNe
  have hrawDegree :
      0 < (HexPolyMathlib.toPolynomial raw).natDegree := by
    rw [← map_rawPoly_nil f,
      Polynomial.natDegree_map_eq_of_injective coeffRatEquiv.injective,
      HexPolyMathlib.natDegree_toPolynomial]
    exact hdegree'
  obtain ⟨unit, hunit⟩ :=
    ZPoly.ratPolyPrimitivePart_rational_associate raw
  have hunitNe : unit ≠ 0 := by
    intro hzero
    have hrawZero : HexPolyMathlib.toPolynomial raw = 0 := by
      rw [hunit, hzero]
      simp
    rw [hrawZero] at hrawDegree
    simp at hrawDegree
  have hassociate :
      HexPolyMathlib.toPolynomial raw =
        Polynomial.C unit * HexPolyZMathlib.toPolyℚ primitive := by
    rw [hunit, HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly]
  have hprimitiveDegree :
      0 < (HexPolyZMathlib.toPolyℚ primitive).natDegree := by
    have hdegreeEq := congrArg Polynomial.natDegree hassociate
    rw [Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hunitNe) hprimitiveRatNe] at hdegreeEq
    have hdegreeEq' :
        (HexPolyMathlib.toPolynomial raw).natDegree =
          (HexPolyZMathlib.toPolyℚ primitive).natDegree := by
      simpa using hdegreeEq
    exact hdegreeEq' ▸ hrawDegree
  have hdegreeInt :
      (HexPolyZMathlib.toPolynomial primitive).natDegree ≠ 0 := by
    rw [← Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom Rat) Int.cast_injective
      (HexPolyZMathlib.toPolynomial primitive)]
    exact Nat.ne_of_gt hprimitiveDegree
  have hirreducibleRat :
      Irreducible (HexPolyZMathlib.toPolyℚ primitive) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (hirreducibleInt.isPrimitive hdegreeInt)).mp hirreducibleInt
  have hrawIrreducible :
      Irreducible (HexPolyMathlib.toPolynomial raw) := by
    rw [hassociate, mul_comm]
    exact (irreducible_mul_isUnit
      (Polynomial.isUnit_C.mpr hunitNe.isUnit)).mpr hirreducibleRat
  apply (MulEquiv.irreducible_iff
    (f := (Polynomial.mapEquiv coeffRatEquiv).toMulEquiv)).mp
  change Irreducible
    ((HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).map
      coeffRatEquiv.toRingHom)
  rw [map_rawPoly_nil]
  exact hrawIrreducible

/-- Mapping the executable base relation through the canonical rational
equivalence recovers its raw rational polynomial. -/
theorem map_relation_nil (level : Level) (hstruct : level.Structural 1) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    (HexPolyMathlib.toPolynomial (Arithmetic.Coeff.relation level [])).map
        coeffRatEquiv.toRingHom =
      HexPolyMathlib.toPolynomial
        (Factor.toRatPoly (level.polynomial [])) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    HexPolyMathlib.coeff_toPolynomial]
  have hsize : level.defining.size = level.degree := hstruct.2.1
  have htop : Arithmetic.fixedCoeffs (levelsDim []) #[1] = #[1] := by
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs, levelsDim]
    · intro i hi₁ hi₂
      simp [Arithmetic.fixedCoeffs, levelsDim, Array.getD]
  have hpoly : level.polynomial [] = level.defining.push #[1] := by
    simp [Level.polynomial, htop]
  have hrat : Factor.toRatPoly (level.polynomial []) =
      DensePoly.ofCoeffs
        ((level.defining.map fun coefficient => coefficient.getD 0 0).push 1) := by
    rw [hpoly]
    simp [Factor.toRatPoly, Array.getD]
  by_cases hn : n < level.degree
  · have hndef : n < level.defining.size := by simpa [hsize] using hn
    have hleft : (Arithmetic.Coeff.relation level []).coeff n =
        Arithmetic.Coeff.ofData [] (level.defining.getD n #[]) := by
      simp [Arithmetic.Coeff.relation]
      rw [List.getElem?_append_left (by simpa using hn),
        List.getElem?_map, List.getElem?_range hn]
      simp [Array.getElem?_eq_getElem hndef]
    have hright : (Factor.toRatPoly (level.polynomial [])).coeff n =
        (level.defining.getD n #[]).getD 0 0 := by
      rw [hrat, DensePoly.coeff_ofCoeffs,
        Array.getD_eq_getD_getElem?, Array.getElem?_push_lt (by
          simpa [hsize] using hn)]
      simp only [Option.getD_some]
      rw [Array.getElem_map]
      have hd : level.defining.getD n #[] = level.defining[n] := by
        rw [Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem hndef]
        rfl
      rw [hd]
    rw [hleft, hright]
    change coeffRatEquiv
        (Arithmetic.Coeff.ofData [] (level.defining.getD n #[])) = _
    exact coeffRatEquiv_ofData (level.defining.getD n #[])
  · by_cases heq : n = level.degree
    · subst n
      have hleft : (Arithmetic.Coeff.relation level []).coeff level.degree =
          1 := by
        simp [Arithmetic.Coeff.relation]
      have hright :
          (Factor.toRatPoly (level.polynomial [])).coeff level.degree = 1 := by
        rw [hrat, DensePoly.coeff_ofCoeffs,
          Array.getD_eq_getD_getElem?]
        have hdegree : level.degree =
            (level.defining.map fun coefficient => coefficient.getD 0 0).size := by
          simp [hsize]
        rw [hdegree, Array.getElem?_push_size]
        rfl
      rw [hleft, hright, map_one]
    · have hgt : level.degree < n := by omega
      have hnle : ¬ n ≤ level.degree := by omega
      have hleft : (Arithmetic.Coeff.relation level []).coeff n = 0 := by
        simp [Arithmetic.Coeff.relation, hnle]
        change Arithmetic.Coeff.ofData [] #[] = (0 : Arithmetic.Coeff [])
        rfl
      have hright : (Factor.toRatPoly (level.polynomial [])).coeff n = 0 := by
        rw [hrat, DensePoly.coeff_ofCoeffs,
          Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (by simp [hsize]; omega)]
        change (0 : Rat) = 0
        rfl
      rw [hleft, hright, map_zero]

/-- A rational-presentation certificate makes the executable base relation
irreducible over the canonical base coefficient field. -/
theorem relation_irreducible_rational (level : Level)
    (hstruct : level.Structural 1) (hrelation : level.RationalRelation []) :
    letI : Field (Arithmetic.Coeff []) := coeffFieldNil
    Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level [])) := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  obtain ⟨_, original, checked, hp, hraw⟩ := hrelation
  letI : ZPoly.CheckedIrreducible original := checked
  have hirrOriginal :
      Irreducible (HexPolyZMathlib.toPolyℚ original) :=
    ZPoly.CheckedIrreducible.irreducibleRat original
  have hirrRoot :
      Irreducible (HexPolyZMathlib.toPolyℚ level.root.p) := by
    rw [hp]
    unfold ZPoly.normalizePrimitiveSign
    split <;> rename_i hsign
    · have hunit : IsUnit (Polynomial.C (-1 : Rat)) :=
        Polynomial.isUnit_C.mpr (by norm_num)
      have hirrNeg :
          Irreducible
            (HexPolyZMathlib.toPolyℚ original * Polynomial.C (-1 : Rat)) :=
        (irreducible_mul_isUnit hunit).mpr hirrOriginal
      simpa [HexPolyZMathlib.toPolyℚ,
        HexPolyMathlib.toPolynomial_scale, mul_comm] using hirrNeg
    · exact hirrOriginal
  have hlcInt : level.root.p.leadingCoeff ≠ 0 :=
    ne_of_gt level.root.pos_lc
  have hlcRat : (level.root.p.leadingCoeff : Rat) ≠ 0 :=
    fun h => hlcInt (Rat.intCast_eq_zero_iff.mp h)
  have hscaleUnit :
      IsUnit (Polynomial.C ((level.root.p.leadingCoeff : Rat)⁻¹)) :=
    Polynomial.isUnit_C.mpr (inv_ne_zero hlcRat).isUnit
  have hirrRaw :
      Irreducible (HexPolyMathlib.toPolynomial
        (Factor.toRatPoly (level.polynomial []))) := by
    rw [hraw, HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly, mul_comm]
    exact (irreducible_mul_isUnit hscaleUnit).mpr hirrRoot
  apply (MulEquiv.irreducible_iff
    (f := (Polynomial.mapEquiv coeffRatEquiv).toMulEquiv)).mp
  change Irreducible
    ((HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level [])).map coeffRatEquiv.toRingHom)
  rw [map_relation_nil level hstruct]
  exact hirrRaw

/-- Every validated one-level presentation has injective canonical complex
denotation.  Rational-presentation certificates use their stored primitive
associate; relative certificates over the rational base use the recursive
factor checker base case. -/
theorem DenoteInjective.singleton (level : Level)
    (hvalid : LevelsValid [level]) : DenoteInjective [level] := by
  letI : Field (Arithmetic.Coeff []) := coeffFieldNil
  have hrelation : Irreducible (HexPolyMathlib.toPolynomial
      (Arithmetic.Coeff.relation level [])) := by
    cases hvalid.2.1 with
    | rational hrat =>
        exact relation_irreducible_rational level hvalid.1 hrat
    | relative _ hchecker _ =>
        have hraw := isIrreducible_nil_toMathlib
          (level.polynomial []) hchecker
        have heq : Arithmetic.Coeff.relation level [] =
            Factor.rawPoly [] (level.polynomial []) := by
          apply (HexPolyMathlib.equiv
            (R := Arithmetic.Coeff [])).injective
          apply (Polynomial.mapEquiv coeffRatEquiv).injective
          change (HexPolyMathlib.toPolynomial
              (Arithmetic.Coeff.relation level [])).map
                coeffRatEquiv.toRingHom =
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly [] (level.polynomial []))).map
                coeffRatEquiv.toRingHom
          rw [map_relation_nil level hvalid.1,
            map_rawPoly_nil (level.polynomial [])]
        rw [heq]
        exact hraw
  exact DenoteInjective.cons level [] hvalid
    (separates_of_irreducible level [] hvalid DenoteInjective.nil
      coeffDenote_inv_nil hrelation)

end LevelSemantics

/-- Injectivity of canonical raw coefficient denotation induces injectivity of
the public fixed-width tower interpretation. -/
theorem toComplex_injective_of_denote (T : NumberTower)
    (hinjective : LevelSemantics.DenoteInjective T.levels.toList) :
    Function.Injective T.toComplex := by
  intro a b hab
  apply Elem.ext
  let ca := Arithmetic.Coeff.ofData T.levels.toList (coeffs a)
  let cb := Arithmetic.Coeff.ofData T.levels.toList (coeffs b)
  have hca : ca.data = coeffs a := by
    change Arithmetic.fixedCoeffs (levelsDim T.levels.toList) (coeffs a) =
      coeffs a
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs, dim]
    · intro i hi₁ hi₂
      have hi : i < T.dim := by simpa using hi₂
      simp [Arithmetic.fixedCoeffs, Array.getD, hi]
  have hcb : cb.data = coeffs b := by
    change Arithmetic.fixedCoeffs (levelsDim T.levels.toList) (coeffs b) =
      coeffs b
    apply Array.ext
    · simp [Arithmetic.fixedCoeffs, dim]
    · intro i hi₁ hi₂
      have hi : i < T.dim := by simpa using hi₂
      simp [Arithmetic.fixedCoeffs, Array.getD, hi]
  have hcoeff : ca = cb := by
    apply hinjective
    change LevelSemantics.denote T.levels.toList ca.data =
      LevelSemantics.denote T.levels.toList cb.data
    rw [hca, hcb]
    rw [← LevelSemantics.toComplex_eq_denote T a,
      ← LevelSemantics.toComplex_eq_denote T b]
    exact hab
  exact hca.symm.trans
    ((congrArg Arithmetic.Coeff.data hcoeff).trans hcb)

end Hex.NumberTower
