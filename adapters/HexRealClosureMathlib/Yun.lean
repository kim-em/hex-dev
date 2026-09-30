/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosure.Yun
public import HexRealClosureMathlib.Element
public import HexPolyMathlib.Euclid
public import Mathlib.FieldTheory.Separable
public import Mathlib.Basic.Real.Basic

public section

/-!
# Mathematical interpretation of Yun replay

Accepted replay gives the ordered-field polynomial product, separable and
pairwise coprime factors, and complete root and multiplicity labels after any
field map. `YunInvariant` proves that every public ordered-field decomposition
passes replay, including inputs with repeated factors.
-/

namespace Hex.RealClosure.Yun

/-- A cached selected-root coefficient stream runs Yun's raw recurrence with
the same result as its exact real-algebraic values. This theorem transports
the computation; `decompose_packed` in `YunInvariant` combines it with the
producer correctness theorem. -/
theorem map_packed {context : Nat} {d : Root context}
    (h : Root.Handle d) (f : DensePoly (Root.Handle.Value h)) :
    Decomposition.map (fun a : Root.Handle.Value h => a.value)
        (fun a => (Root.Handle.Value.eq_zero_iff a).symm)
        (decomposeRaw f) =
      decomposeRaw
        (DensePoly.Interpret.map
          (fun a : Root.Handle.Value h => a.value)
          (fun a => (Root.Handle.Value.eq_zero_iff a).symm) f) := by
  exact map_decomposeRaw
    (fun a : Root.Handle.Value h => a.value)
    (fun a => (Root.Handle.Value.eq_zero_iff a).symm)
    (fun a b => Root.Handle.Value.value_sub a b)
    (fun a b => Root.Handle.Value.value_mul a b)
    (fun a b => Root.Handle.Value.value_div a b)
    (fun a => Root.Handle.Value.value_inv a)
    (fun n => Root.Handle.Value.value_natCast n) f

/-- Convert powers without assuming a Mathlib monoid instance on `DensePoly`. -/
private theorem toPolynomial_pow {K : Type*} [CommRing K] [DecidableEq K]
    (p : DensePoly K) (n : Nat) :
    HexPolyMathlib.toPolynomial (p ^ n) =
      (HexPolyMathlib.toPolynomial p) ^ n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero,
      HexPolyMathlib.toPolynomial_one]
  | succ n ih =>
      rw [Lean.Grind.Semiring.pow_succ, HexPolyMathlib.toPolynomial_mul,
        ih, pow_succ]

/-- Executable reconstruction agrees with polynomial multiplication. -/
theorem toPolynomial_reconstruct {K : Type*} [CommRing K] [DecidableEq K]
    (unit : K) (entries : Array (DensePoly K × Nat)) :
    HexPolyMathlib.toPolynomial (reconstruct unit entries) =
      entries.toList.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C unit) := by
  have hfold (l : List (DensePoly K × Nat)) (acc : DensePoly K) :
      HexPolyMathlib.toPolynomial
        (l.foldl (fun product entry => product * entry.1 ^ entry.2) acc) =
      l.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (HexPolyMathlib.toPolynomial acc) := by
    induction l generalizing acc with
    | nil => rfl
    | cons entry rest ih =>
        simpa only [List.foldl_cons, HexPolyMathlib.toPolynomial_mul,
          toPolynomial_pow] using
          ih (acc * entry.1 ^ entry.2)
  simpa only [reconstruct, ← Array.foldl_toList,
    HexPolyMathlib.toPolynomial_C] using
    hfold entries.toList (DensePoly.C unit)

/-- Executable reconstruction is the scalar times the powered factor
product over any coefficient ring. -/
theorem toPolynomial_reconstruct_prod {K : Type*} [CommRing K] [DecidableEq K]
    (unit : K) (entries : Array (DensePoly K × Nat)) :
    HexPolyMathlib.toPolynomial (reconstruct unit entries) = Polynomial.C unit *
      (entries.toList.map fun entry =>
        (HexPolyMathlib.toPolynomial entry.1) ^ entry.2).prod := by
  rw [toPolynomial_reconstruct]
  have hfold (l : List (DensePoly K × Nat)) (acc : Polynomial K) :
      l.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2) acc =
      acc * (l.map fun entry =>
        (HexPolyMathlib.toPolynomial entry.1) ^ entry.2).prod := by
    induction l generalizing acc with
    | nil => simp
    | cons entry rest ih =>
        simp only [List.foldl_cons, List.map_cons, List.prod_cons]
        rw [ih]
        ring
  exact hfold entries.toList (Polynomial.C unit)

/-- A replay-accepted result has the same product in Mathlib polynomials. -/
theorem check_product_polynomial (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (h : check f (.factors unit entries) = true) :
    HexPolyMathlib.toPolynomial f =
      entries.toList.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C unit) := by
  rw [← toPolynomial_reconstruct]
  simpa only [reconstruct] using congrArg HexPolyMathlib.toPolynomial
    (check_reconstruct f unit entries h).1.symm

/-- An accepted product can be written as an ordinary polynomial list product. -/
theorem check_product_prod {F : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F]
    (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (h : check f (.factors unit entries) = true) :
    HexPolyMathlib.toPolynomial f = Polynomial.C unit *
      (entries.toList.map fun entry =>
        (HexPolyMathlib.toPolynomial entry.1) ^ entry.2).prod := by
  rw [← toPolynomial_reconstruct_prod]
  simpa only [reconstruct] using congrArg HexPolyMathlib.toPolynomial
    (check_reconstruct f unit entries h).1.symm

/-- Accepted replay has the same factorization after a field map. -/
theorem check_product_map {F K : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F] [Field K]
    (φ : F →+* K) (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (h : check f (.factors unit entries) = true) :
    (HexPolyMathlib.toPolynomial f).map φ =
      Polynomial.C (φ unit) *
        (entries.toList.map fun entry =>
          ((HexPolyMathlib.toPolynomial entry.1).map φ) ^
            entry.2).prod := by
  have hbase := congrArg (Polynomial.map φ)
    (check_product_prod f unit entries h)
  simpa only [Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_list_prod, Polynomial.map_pow,
    List.map_map, Function.comp_def] using hbase

/-- Accepted rational replay has the same factorization after mapping to ℝ. -/
theorem check_product_real (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (h : check f (.factors unit entries) = true) :
    (HexPolyMathlib.toPolynomial f).map (Rat.castHom ℝ) =
      Polynomial.C (unit : ℝ) *
        (entries.toList.map fun entry =>
          ((HexPolyMathlib.toPolynomial entry.1).map (Rat.castHom ℝ)) ^
            entry.2).prod := by
  simpa only [Rat.coe_castHom] using
    check_product_map (Rat.castHom ℝ) f unit entries h

/-- Powers of a nonzero polynomial over a field remain nonzero. -/
private theorem polynomial_pow_ne_zero {K : Type*} [Field K]
    (p : Polynomial K)
    (n : Nat) (hp : p ≠ 0) : p ^ n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact mul_ne_zero ih hp

/-- Root multiplicity of a power of a nonzero polynomial over a field. -/
private theorem rootMultiplicity_pow {K : Type*} [Field K]
    (p : Polynomial K) (n : Nat)
    (x : K) (hp : p ≠ 0) :
    Polynomial.rootMultiplicity x (p ^ n) =
      n * Polynomial.rootMultiplicity x p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,
        Polynomial.rootMultiplicity_mul
          (mul_ne_zero (polynomial_pow_ne_zero p n hp) hp), ih]
      simp [Nat.succ_mul]

private theorem product_ne_zero {K : Type*} [Field K]
    (l : List (Polynomial K × Nat))
    (h : ∀ entry ∈ l, entry.1 ≠ 0) :
    (l.map fun entry => entry.1 ^ entry.2).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons entry rest ih =>
      have he := h entry (by simp)
      have hrest : ∀ item ∈ rest, item.1 ≠ 0 := by
        intro item hmem
        exact h item (by simp [hmem])
      simpa only [List.map_cons, List.prod_cons] using
        mul_ne_zero (polynomial_pow_ne_zero entry.1 entry.2 he)
          (ih hrest)

/-- Root multiplicity distributes over the nonzero factor product. -/
private theorem rootMultiplicity_product {K : Type*} [Field K]
    (l : List (Polynomial K × Nat)) (x : K) :
    (∀ entry ∈ l, entry.1 ≠ 0) →
    Polynomial.rootMultiplicity x
      (l.map fun entry => entry.1 ^ entry.2).prod =
    (l.map fun entry => entry.2 *
      Polynomial.rootMultiplicity x entry.1).sum := by
  induction l with
  | nil => intro _; simp
  | cons entry rest ih =>
      intro h
      have he := h entry (by simp)
      have hrest : ∀ item ∈ rest, item.1 ≠ 0 := by
        intro item hmem
        exact h item (by simp [hmem])
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Polynomial.rootMultiplicity_mul
        (mul_ne_zero (polynomial_pow_ne_zero entry.1 entry.2 he)
          (product_ne_zero rest hrest)),
        rootMultiplicity_pow entry.1 entry.2 x he,
        ih hrest]

/-- Coprime polynomials over a field have no common root in that field. -/
private theorem coprime_no_common_root {K : Type*} [Field K]
    (p q : Polynomial K)
    (hcoprime : IsCoprime p q) (x : K)
    (hp : Polynomial.IsRoot p x) : ¬Polynomial.IsRoot q x := by
  intro hq
  have h := hcoprime.map (Polynomial.evalRingHom x)
  have hzero : IsCoprime (0 : K) 0 := by
    simpa only [Polynomial.coe_evalRingHom, hp.eq_zero, hq.eq_zero] using h
  exact not_isCoprime_zero_zero hzero

/-- A root of a separable polynomial has multiplicity one. -/
private theorem separable_rootMultiplicity_one {K : Type*} [Field K]
    (p : Polynomial K)
    (x : K) (hsep : p.Separable) (hroot : Polynomial.IsRoot p x) :
    Polynomial.rootMultiplicity x p = 1 :=
  Nat.le_antisymm
    (Polynomial.rootMultiplicity_le_one_of_separable hsep x)
    ((Polynomial.rootMultiplicity_pos hsep.ne_zero).mpr hroot)

private theorem rootMultiplicity_label {K : Type*} [Field K]
    (l : List (Polynomial K × Nat))
    (selected : Polynomial K × Nat) (x : K) :
    l.Pairwise (fun a b => IsCoprime a.1 b.1) →
    (∀ entry ∈ l, entry.1.Separable) →
    selected ∈ l → Polynomial.IsRoot selected.1 x →
    (l.map fun entry => entry.2 *
      Polynomial.rootMultiplicity x entry.1).sum = selected.2 := by
  induction l with
  | nil => intro _ _ hmem _; cases hmem
  | cons head rest ih =>
      intro hpair hsep hmem hroot
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hsepHead := hsep head (by simp)
      have hsepTail : ∀ entry ∈ rest, entry.1.Separable := by
        intro entry hentry
        exact hsep entry (by simp [hentry])
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with heq | hmemTail
      · subst selected
        rw [separable_rootMultiplicity_one head.1 x hsepHead hroot]
        have hsumzero : (rest.map fun entry => entry.2 *
            Polynomial.rootMultiplicity x entry.1).sum = 0 := by
          apply List.sum_eq_zero_iff_forall_eq_nat.mpr
          intro value hvalue
          obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hvalue
          have hnot := coprime_no_common_root head.1 entry.1
            (hhead entry hentry) x hroot
          simp [Polynomial.rootMultiplicity_eq_zero hnot]
        simp [hsumzero]
      · have hnot := coprime_no_common_root selected.1 head.1
          ((hhead selected hmemTail).symm) x hroot
        rw [Polynomial.rootMultiplicity_eq_zero hnot]
        simpa using ih htail hsepTail hmemTail hroot

/-- A constant executable gcd maps to a unit polynomial gcd. -/
private theorem gcd_isUnit {F : Type*} [Field F] [DecidableEq F]
    (p q : DensePoly F)
    (hp : p ≠ 0) (hdegree : (DensePoly.gcd p q).natDegree = 0) :
    IsUnit (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
      (HexPolyMathlib.toPolynomial q)) := by
  let G := EuclideanDomain.gcd (HexPolyMathlib.toPolynomial p)
    (HexPolyMathlib.toPolynomial q)
  have hmap : HexPolyMathlib.toPolynomial p ≠ 0 := by
    intro hzero
    apply hp
    have h := congrArg HexPolyMathlib.ofPolynomial hzero
    simpa using h
  have hassociated : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd p q)) G :=
    HexPolyMathlib.toPolynomial_gcd_associated p q
  have hGzero : G ≠ 0 := by
    intro hzero
    exact hmap (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hdegreeG : G.natDegree = 0 := by
    have hdegreeAssoc := Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassociated)
    have hgmap : (HexPolyMathlib.toPolynomial (DensePoly.gcd p q)).natDegree = 0 := by
      simpa [HexPolyMathlib.natDegree_toPolynomial] using hdegree
    rw [hdegreeAssoc] at hgmap
    exact hgmap
  rw [Polynomial.isUnit_iff_degree_eq_zero,
    Polynomial.degree_eq_natDegree hGzero]
  exact_mod_cast hdegreeG

/-- A factor accepted by ordered-field replay is separable. -/
theorem check_factor_separable {F : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F]
    (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (entry : DensePoly F × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) :
    (HexPolyMathlib.toPolynomial entry.1).Separable := by
  obtain ⟨_, hdegree, _, hgcd⟩ :=
    check_factor f unit entries entry hmem h
  have hp : entry.1 ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  have hGunit := gcd_isUnit entry.1
    (DensePoly.derivativeImpl entry.1) hp hgcd
  exact (Polynomial.separable_def _).2
    (EuclideanDomain.gcd_isUnit_iff.mp (by
      simpa [← DensePoly.derivative_eq_derivativeImpl,
        HexPolyMathlib.toPolynomial_derivative] using hGunit))

/-- Every accepted factor is squarefree. -/
theorem check_factor_squarefree {F : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F]
    (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (entry : DensePoly F × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) :
    Squarefree (HexPolyMathlib.toPolynomial entry.1) :=
  (check_factor_separable f unit entries entry hmem h).squarefree

/-- Accepted replay factors are pairwise coprime as mathematical polynomials. -/
theorem check_pairwise_coprime {F : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F]
    (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (h : check f (.factors unit entries) = true) :
    entries.toList.Pairwise (fun a b =>
      IsCoprime (HexPolyMathlib.toPolynomial a.1)
        (HexPolyMathlib.toPolynomial b.1)) := by
  apply (check_coprime f unit entries h).imp_of_mem
  intro a b ha _ hab
  have ha : a ∈ entries := Array.mem_toList_iff.mp ha
  have hdegree := (check_factor f unit entries a ha h).2.1
  have hnonzero : a.1 ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  exact EuclideanDomain.gcd_isUnit_iff.mp
    (gcd_isUnit a.1 b.1 hnonzero hab)

/-- A root of an accepted factor has its labelled multiplicity after a
field map. -/
theorem check_map_rootMultiplicity {F K : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F] [Field K]
    (φ : F →+* K) (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (entry : DensePoly F × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) (x : K)
    (hroot : Polynomial.IsRoot
      ((HexPolyMathlib.toPolynomial entry.1).map φ) x) :
    Polynomial.rootMultiplicity x
      ((HexPolyMathlib.toPolynomial f).map φ) =
      entry.2 := by
  let mapped := entries.toList.map fun item =>
    ((HexPolyMathlib.toPolynomial item.1).map φ, item.2)
  have hpair : mapped.Pairwise (fun a b => IsCoprime a.1 b.1) := by
    apply (check_pairwise_coprime f unit entries h).map
      (fun item =>
        ((HexPolyMathlib.toPolynomial item.1).map φ, item.2))
    intro a b hab
    exact hab.map (Polynomial.mapRingHom φ)
  have hsep : ∀ item ∈ mapped, item.1.Separable := by
    intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact (check_factor_separable f unit entries source
      (Array.mem_toList_iff.mp hsource) h).map
  have hmapped :
      ((HexPolyMathlib.toPolynomial entry.1).map φ, entry.2) ∈
        mapped := by
    apply List.mem_map.mpr
    exact ⟨entry, Array.mem_toList_iff.mpr hmem, rfl⟩
  have hnonzero : ∀ item ∈ mapped, item.1 ≠ 0 := by
    intro item hitem
    exact (hsep item hitem).ne_zero
  have hmap : (mapped.map fun item => item.1 ^ item.2).prod =
      (entries.toList.map fun item =>
        ((HexPolyMathlib.toPolynomial item.1).map φ) ^
          item.2).prod := by
    simp only [mapped, List.map_map, Function.comp_def]
  rw [check_product_map φ f unit entries h, ← hmap]
  have hmul : Polynomial.C (φ unit) *
      (mapped.map fun item => item.1 ^ item.2).prod ≠ 0 := by
    apply mul_ne_zero
    · apply Polynomial.C_ne_zero.mpr
      intro hzero
      exact check_unit f unit entries h
        ((RingHom.injective φ) (by simpa using hzero))
    · exact product_ne_zero mapped hnonzero
  rw [Polynomial.rootMultiplicity_mul hmul,
    Polynomial.rootMultiplicity_C, zero_add,
    rootMultiplicity_product mapped x hnonzero]
  exact rootMultiplicity_label mapped
    ((HexPolyMathlib.toPolynomial entry.1).map φ, entry.2)
    x hpair hsep hmapped hroot

/-- A checked Yun factor labels the multiplicity of each of its roots
in the original polynomial over the same ordered field. -/
theorem check_rootMultiplicity {K : Type*} [Field K] [DecidableEq K]
    [LinearOrder K] [IsStrictOrderedRing K]
    (f : DensePoly K) (unit : K)
    (entries : Array (DensePoly K × Nat))
    (entry : DensePoly K × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) (x : K)
    (hroot : Polynomial.IsRoot
      (HexPolyMathlib.toPolynomial entry.1) x) :
    Polynomial.rootMultiplicity x (HexPolyMathlib.toPolynomial f) =
      entry.2 := by
  simpa using check_map_rootMultiplicity (RingHom.id K)
    f unit entries entry hmem h x (by simpa using hroot)

/-- Replay identifies exactly the roots after mapping into a field. -/
theorem check_map_roots_iff {F K : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F] [Field K]
    (φ : F →+* K) (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (h : check f (.factors unit entries) = true) (x : K) :
    Polynomial.IsRoot ((HexPolyMathlib.toPolynomial f).map φ) x ↔
      ∃ entry ∈ entries,
        Polynomial.IsRoot
          ((HexPolyMathlib.toPolynomial entry.1).map φ) x := by
  let factors := entries.toList.map fun entry =>
    ((HexPolyMathlib.toPolynomial entry.1).map φ) ^ entry.2
  have hproduct : (HexPolyMathlib.toPolynomial f).map φ =
      Polynomial.C (φ unit) * factors.prod :=
    check_product_map φ f unit entries h
  constructor
  · intro hroot
    have hunit : φ unit ≠ 0 := by
      intro hzero
      exact check_unit f unit entries h
        ((RingHom.injective φ) (by simpa using hzero))
    have hzero : factors.prod.eval x = 0 := by
      have heval := hroot.eq_zero
      rw [hproduct, Polynomial.eval_mul, Polynomial.eval_C] at heval
      exact (mul_eq_zero.mp heval).resolve_left hunit
    rw [Polynomial.eval_list_prod] at hzero
    have hvalue : (0 : K) ∈ factors.map (Polynomial.eval x) :=
      List.prod_eq_zero_iff.mp hzero
    obtain ⟨factor, hfactor, hvalueEq⟩ := List.mem_map.mp hvalue
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hfactor
    refine ⟨entry, Array.mem_toList_iff.mp hentry, ?_⟩
    have hzeroPower :
        (((HexPolyMathlib.toPolynomial entry.1).map φ).eval x) ^
          entry.2 = 0 := by
      simpa only [Polynomial.eval_pow] using hvalueEq
    exact eq_zero_of_pow_eq_zero hzeroPower
  · rintro ⟨entry, hentry, hroot⟩
    have hpositive := (check_factor f unit entries entry hentry h).1
    rw [Polynomial.IsRoot, hproduct, Polynomial.eval_mul,
      Polynomial.eval_list_prod]
    apply mul_eq_zero.mpr
    right
    apply List.prod_eq_zero_iff.mpr
    apply List.mem_map.mpr
    refine ⟨((HexPolyMathlib.toPolynomial entry.1).map φ) ^ entry.2,
      ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨entry, Array.mem_toList_iff.mpr hentry, rfl⟩
    · simp [Polynomial.eval_pow, hroot.eq_zero,
        Nat.ne_of_gt hpositive]

/-- Checked Yun factors cover exactly the roots over the coefficient field. -/
theorem check_roots_iff {K : Type*} [Field K] [DecidableEq K]
    [LinearOrder K] [IsStrictOrderedRing K]
    (f : DensePoly K) (unit : K)
    (entries : Array (DensePoly K × Nat))
    (h : check f (.factors unit entries) = true) (x : K) :
    Polynomial.IsRoot (HexPolyMathlib.toPolynomial f) x ↔
      ∃ entry ∈ entries,
        Polynomial.IsRoot (HexPolyMathlib.toPolynomial entry.1) x := by
  simpa using check_map_roots_iff (RingHom.id K) f unit entries h x

/-- Replay identifies exactly the roots with a given multiplicity after
mapping into a field. -/
theorem check_map_roots_label {F K : Type*} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F] [Field K]
    (φ : F →+* K) (f : DensePoly F) (unit : F)
    (entries : Array (DensePoly F × Nat))
    (h : check f (.factors unit entries) = true) (x : K) (m : Nat) :
    (Polynomial.IsRoot ((HexPolyMathlib.toPolynomial f).map φ) x ∧
      Polynomial.rootMultiplicity x
        ((HexPolyMathlib.toPolynomial f).map φ) = m) ↔
      ∃ entry ∈ entries,
        Polynomial.IsRoot
          ((HexPolyMathlib.toPolynomial entry.1).map φ) x ∧
          entry.2 = m := by
  constructor
  · rintro ⟨hroot, hmul⟩
    obtain ⟨entry, hmem, hentry⟩ :=
      (check_map_roots_iff φ f unit entries h x).mp hroot
    refine ⟨entry, hmem, hentry, ?_⟩
    exact (check_map_rootMultiplicity φ f unit entries entry hmem h x
      hentry).symm.trans hmul
  · rintro ⟨entry, hmem, hentry, hm⟩
    exact ⟨(check_map_roots_iff φ f unit entries h x).mpr
      ⟨entry, hmem, hentry⟩,
      (check_map_rootMultiplicity φ f unit entries entry hmem h x
        hentry).trans hm⟩

/-- A real root of an accepted rational factor has its labelled multiplicity
in the original polynomial after embedding into ℝ. -/
theorem check_real_rootMultiplicity (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (entry : DensePoly Rat × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) (x : ℝ)
    (hroot : Polynomial.IsRoot
      ((HexPolyMathlib.toPolynomial entry.1).map (Rat.castHom ℝ)) x) :
    Polynomial.rootMultiplicity x
      ((HexPolyMathlib.toPolynomial f).map (Rat.castHom ℝ)) =
    entry.2 :=
  check_map_rootMultiplicity (Rat.castHom ℝ) f unit entries entry hmem h x hroot

/-- The producer proof composes with rational replay semantics using the
same field instances as the executable rational tests. -/
example (f : DensePoly Rat) (hdegree : 0 < f.natDegree)
    (hgcd : DensePoly.monicize
      (DensePoly.gcd f (DensePoly.derivativeImpl f)) = 1) :
    HexPolyMathlib.toPolynomial f =
      (#[(DensePoly.monicize f, 1)] : Array (DensePoly Rat × Nat)).toList.foldl
        (fun product entry => product *
          (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C f.leadingCoeff) := by
  apply check_product_polynomial
  rw [← decompose_squarefree f hdegree hgcd]
  exact check_decompose_squarefree f hdegree hgcd

end Hex.RealClosure.Yun

/-- info: 'Hex.RealClosure.Yun.toPolynomial_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.toPolynomial_reconstruct

/-- info: 'Hex.RealClosure.Yun.toPolynomial_reconstruct_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.toPolynomial_reconstruct_prod

/-- info: 'Hex.RealClosure.Yun.check_product_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Yun.check_product_polynomial
/-- info: 'Hex.RealClosure.Yun.check_factor_separable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Yun.check_factor_separable
/-- info: 'Hex.RealClosure.Yun.check_pairwise_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Yun.check_pairwise_coprime
/-- info: 'Hex.RealClosure.Yun.check_real_rootMultiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Yun.check_real_rootMultiplicity
/-- info: 'Hex.RealClosure.Yun.check_map_roots_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Yun.check_map_roots_label

/-- info: 'Hex.RealClosure.Yun.map_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Yun.map_packed
