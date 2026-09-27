/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosure.Yun
public import HexPolyMathlib.Euclid
public import Mathlib.FieldTheory.Separable

public section

/-!
# Mathematical interpretation of Yun replay

The executable replay's gcd checks imply separability of each emitted rational
factor. This does not assert that every result produced by the Yun recurrence
passes replay.
-/

namespace Hex.RealClosure.Yun

/-- Convert powers without assuming a Mathlib monoid instance on `DensePoly`. -/
private theorem toPolynomial_pow (p : DensePoly Rat) (n : Nat) :
    HexPolyMathlib.toPolynomial (p ^ n) =
      (HexPolyMathlib.toPolynomial p) ^ n := by
  induction n with
  | zero => simp only [Lean.Grind.Semiring.pow_zero,
      HexPolyMathlib.toPolynomial_one]
  | succ n ih =>
      rw [Lean.Grind.Semiring.pow_succ, HexPolyMathlib.toPolynomial_mul,
        ih, pow_succ]

/-- Executable reconstruction agrees with multiplication of rational
polynomials. -/
theorem toPolynomial_reconstruct (unit : Rat)
    (entries : Array (DensePoly Rat × Nat)) :
    HexPolyMathlib.toPolynomial (reconstruct unit entries) =
      entries.toList.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C unit) := by
  have hfold (l : List (DensePoly Rat × Nat)) (acc : DensePoly Rat) :
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

/-- A replay-accepted result has the same product in Mathlib polynomials. -/
theorem check_product_polynomial (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (h : check f (.factors unit entries) = true) :
    HexPolyMathlib.toPolynomial f =
      entries.toList.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C unit) := by
  rw [← toPolynomial_reconstruct,
    (check_reconstruct f unit entries h).1]

/-- An accepted product can be written as an ordinary polynomial list product. -/
theorem check_product_prod (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (h : check f (.factors unit entries) = true) :
    HexPolyMathlib.toPolynomial f = Polynomial.C unit *
      (entries.toList.map fun entry =>
        (HexPolyMathlib.toPolynomial entry.1) ^ entry.2).prod := by
  rw [check_product_polynomial f unit entries h]
  have hfold (l : List (DensePoly Rat × Nat)) (acc : Polynomial Rat) :
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

/-- Powers of a nonzero rational polynomial remain nonzero. -/
private theorem polynomial_pow_ne_zero (p : Polynomial Rat)
    (n : Nat) (hp : p ≠ 0) : p ^ n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact mul_ne_zero ih hp

/-- Root multiplicity of a power of a nonzero rational polynomial. -/
private theorem rootMultiplicity_pow (p : Polynomial Rat) (n : Nat)
    (x : Rat) (hp : p ≠ 0) :
    Polynomial.rootMultiplicity x (p ^ n) =
      n * Polynomial.rootMultiplicity x p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,
        Polynomial.rootMultiplicity_mul
          (mul_ne_zero (polynomial_pow_ne_zero p n hp) hp), ih]
      simp [Nat.succ_mul]

private theorem product_ne_zero (l : List (Polynomial Rat × Nat))
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
private theorem rootMultiplicity_product (l : List (Polynomial Rat × Nat))
    (x : Rat) :
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

/-- Accepted rational replay computes root multiplicity as the sum of the
labelled factor multiplicities at that rational root. -/
theorem check_rootMultiplicity_sum (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (h : check f (.factors unit entries) = true) (x : Rat) :
    Polynomial.rootMultiplicity x (HexPolyMathlib.toPolynomial f) =
      (entries.toList.map fun entry => entry.2 *
        Polynomial.rootMultiplicity x
          (HexPolyMathlib.toPolynomial entry.1)).sum := by
  let mapped := entries.toList.map fun entry =>
    (HexPolyMathlib.toPolynomial entry.1, entry.2)
  have hnonzero : ∀ entry ∈ entries.toList,
      HexPolyMathlib.toPolynomial entry.1 ≠ 0 := by
    intro entry hmem hzero
    have hsource : entry.1 = 0 := by
      have heq := congrArg HexPolyMathlib.ofPolynomial hzero
      simpa using heq
    have hdegree := (check_factor f unit entries entry
      (Array.mem_toList_iff.mp hmem) h).2.1
    rw [hsource] at hdegree
    simp at hdegree
  have hmapped : ∀ entry ∈ mapped, entry.1 ≠ 0 := by
    intro entry hmem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
    exact hnonzero source hsource
  have hproduct := check_product_prod f unit entries h
  rw [hproduct]
  have hmul : Polynomial.C unit *
      (mapped.map fun entry => entry.1 ^ entry.2).prod ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr (check_unit f unit entries h))
      (product_ne_zero mapped hmapped)
  have hmap : (mapped.map fun entry => entry.1 ^ entry.2).prod =
      (entries.toList.map fun entry =>
        (HexPolyMathlib.toPolynomial entry.1) ^ entry.2).prod := by
    simp only [mapped, List.map_map, Function.comp_def]
  rw [← hmap, Polynomial.rootMultiplicity_mul hmul]
  simpa only [Polynomial.rootMultiplicity_C, zero_add, mapped,
    List.map_map, Function.comp_def] using
    rootMultiplicity_product mapped x hmapped

/-- Coprime rational polynomials have no common rational root. -/
private theorem coprime_no_common_root (p q : Polynomial Rat)
    (hcoprime : IsCoprime p q) (x : Rat)
    (hp : Polynomial.IsRoot p x) : ¬Polynomial.IsRoot q x := by
  intro hq
  have h := hcoprime.map (Polynomial.evalRingHom x)
  have hzero : IsCoprime (0 : Rat) 0 := by
    simpa only [Polynomial.coe_evalRingHom, hp.eq_zero, hq.eq_zero] using h
  exact not_isCoprime_zero_zero hzero

/-- A root of a separable rational polynomial has multiplicity one. -/
private theorem separable_rootMultiplicity_one (p : Polynomial Rat)
    (x : Rat) (hsep : p.Separable) (hroot : Polynomial.IsRoot p x) :
    Polynomial.rootMultiplicity x p = 1 :=
  Nat.le_antisymm
    (Polynomial.rootMultiplicity_le_one_of_separable hsep x)
    ((Polynomial.rootMultiplicity_pos hsep.ne_zero).mpr hroot)

private theorem rootMultiplicity_label (l : List (Polynomial Rat × Nat))
    (selected : Polynomial Rat × Nat) (x : Rat) :
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

/-- A constant executable gcd maps to a unit gcd over `Rat`. -/
private theorem gcd_isUnit (p q : DensePoly Rat)
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

/-- A rational factor accepted by replay is separable. -/
theorem check_factor_separable (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (entry : DensePoly Rat × Nat) (hmem : entry ∈ entries)
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

/-- Every accepted rational factor is squarefree. -/
theorem check_factor_squarefree (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (entry : DensePoly Rat × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) :
    Squarefree (HexPolyMathlib.toPolynomial entry.1) :=
  (check_factor_separable f unit entries entry hmem h).squarefree

/-- Accepted replay factors are pairwise coprime as mathematical polynomials. -/
theorem check_pairwise_coprime (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
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

/-- A rational root of an accepted factor has its labelled multiplicity in
the original rational polynomial. -/
theorem check_rootMultiplicity (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (entry : DensePoly Rat × Nat) (hmem : entry ∈ entries)
    (h : check f (.factors unit entries) = true) (x : Rat)
    (hroot : Polynomial.IsRoot
      (HexPolyMathlib.toPolynomial entry.1) x) :
    Polynomial.rootMultiplicity x (HexPolyMathlib.toPolynomial f) =
      entry.2 := by
  let mapped := entries.toList.map fun item =>
    (HexPolyMathlib.toPolynomial item.1, item.2)
  have hpair : mapped.Pairwise (fun a b => IsCoprime a.1 b.1) := by
    apply (check_pairwise_coprime f unit entries h).map
      (fun item => (HexPolyMathlib.toPolynomial item.1, item.2))
    intro a b hab
    exact hab
  have hsep : ∀ item ∈ mapped, item.1.Separable := by
    intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact check_factor_separable f unit entries source
      (Array.mem_toList_iff.mp hsource) h
  have hmapped : (HexPolyMathlib.toPolynomial entry.1, entry.2) ∈ mapped := by
    apply List.mem_map.mpr
    exact ⟨entry, Array.mem_toList_iff.mpr hmem, rfl⟩
  rw [check_rootMultiplicity_sum f unit entries h x]
  simpa only [mapped, List.map_map, Function.comp_def] using
    rootMultiplicity_label mapped
      (HexPolyMathlib.toPolynomial entry.1, entry.2) x
      hpair hsep hmapped hroot

end Hex.RealClosure.Yun

/-- info: 'Hex.RealClosure.Yun.check_product_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_product_polynomial
/-- info: 'Hex.RealClosure.Yun.check_factor_separable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_factor_separable
/-- info: 'Hex.RealClosure.Yun.check_pairwise_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_pairwise_coprime
/-- info: 'Hex.RealClosure.Yun.check_rootMultiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.check_rootMultiplicity
