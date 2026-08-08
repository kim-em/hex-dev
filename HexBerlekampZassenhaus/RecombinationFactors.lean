/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.ModularPolynomial
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL
-- Kernel-reducible `Array`/`Vector` equality; see `HexBasic.ArrayDecEq`.
-- Drop once leanprover/lean4#14270 lands and the toolchain is bumped past it.
public import HexBasic.ArrayDecEq

public import HexBerlekampZassenhaus.FactorIrreducibility
public meta import HexBerlekampZassenhaus.FactorIrreducibility
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.FactorizationData
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.FactorizationResult
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.Factorization
import all HexBerlekampZassenhaus.FactorIrreducibility

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section
set_option backward.proofsInPublic true

/-!
This module collects correctness proofs for recombination, `bhksRecover*`, and
the factors of the square-free part.
-/
namespace Hex

private theorem normalizeForFactor_reassembles_signedContentScalar
    (f : ZPoly) (hf : f ≠ 0) :
    DensePoly.scale (signedContentScalar f)
      (DensePoly.shift (normalizeForFactor f).xPower
        ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) = f := by
  let xData := ZPoly.extractXPower (ZPoly.primitivePart f)
  rcases normalizeForFactor_reassembles_with_signed_unit f hf with ⟨ε, hε, heq⟩
  -- Step 1: `content f` is positive.
  have hcontent_ne : ZPoly.content f ≠ 0 := by
    intro hcontent
    apply hf
    have hreconstruct := ZPoly.content_mul_primitivePart f
    rw [hcontent] at hreconstruct
    have hzero : DensePoly.scale (0 : Int) (ZPoly.primitivePart f) = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (0 : Int) (ZPoly.primitivePart f) n
        (Int.zero_mul 0)]
      rw [DensePoly.coeff_zero]
      exact Int.zero_mul _
    rw [hzero] at hreconstruct
    exact hreconstruct.symm
  have hcontent_pos : 0 < ZPoly.content f := by
    have hnonneg : 0 ≤ ZPoly.content f := by
      show 0 ≤ DensePoly.content _
      rw [DensePoly.content]
      exact Int.natCast_nonneg _
    omega
  -- Step 2: the x-power core is nonzero.
  have hcore_primitive : ZPoly.Primitive xData.core := by
    simpa [xData] using extractXPower_core_primitive_of_ne_zero f hf
  have hcore_ne : xData.core ≠ 0 := by
    intro hzero
    have hcontent_core : ZPoly.content xData.core = 0 := by
      rw [hzero]
      simp [ZPoly.content, DensePoly.content_zero]
    have hone_eq_zero : (1 : Int) = 0 := by
      have := hcore_primitive
      rw [ZPoly.Primitive, hcontent_core] at this
      exact this.symm
    exact absurd hone_eq_zero (by decide)
  -- Step 3: `squareFreeCore * repeatedPart` has positive leading coefficient.
  have hA_pos :
      0 < DensePoly.leadingCoeff
        ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) := by
    have h :=
      ZPoly.primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_leadingCoeff_pos
        xData.core hcore_ne
    simpa [normalizeForFactor, xData] using h
  have hA_ne :
      (normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart ≠ 0 := by
    intro hzero
    rw [hzero] at hA_pos
    have hl0 : DensePoly.leadingCoeff (0 : ZPoly) = 0 := by simp
    rw [hl0] at hA_pos
    omega
  have hB_leading :
      DensePoly.leadingCoeff
          (DensePoly.shift (normalizeForFactor f).xPower
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) =
        DensePoly.leadingCoeff
          ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) :=
    ZPoly.leadingCoeff_shift_of_nonzero _ _ hA_ne
  have hcε_ne : ZPoly.content f * ε ≠ 0 := by
    intro hzero
    rcases Int.mul_eq_zero.mp hzero with h | h
    · exact hcontent_ne h
    · rcases hε with h1 | h1
      · rw [h1] at h; exact absurd h (by decide)
      · rw [h1] at h; exact absurd h (by decide)
  -- Step 4: extract the leading coefficient of `f` from `heq`.
  have h_f_leading :
      DensePoly.leadingCoeff f =
        (ZPoly.content f * ε) *
          DensePoly.leadingCoeff
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) := by
    have h_LHS :
        DensePoly.leadingCoeff
            (DensePoly.scale (ZPoly.content f * ε)
              (DensePoly.shift (normalizeForFactor f).xPower
                ((normalizeForFactor f).squareFreeCore *
                  (normalizeForFactor f).repeatedPart))) =
          (ZPoly.content f * ε) *
            DensePoly.leadingCoeff
              ((normalizeForFactor f).squareFreeCore *
                (normalizeForFactor f).repeatedPart) := by
      rw [ZPoly.leadingCoeff_scale_of_nonzero _ _ hcε_ne, hB_leading]
    rw [← h_LHS, heq]
  -- Step 5: identify `signedContentScalar f = content f * ε`.
  suffices h_sign_eq : signedContentScalar f = ZPoly.content f * ε by
    rw [h_sign_eq]; exact heq
  rcases hε with hε | hε
  · -- ε = 1
    have hf_pos : 0 < DensePoly.leadingCoeff f := by
      rw [h_f_leading, hε, Int.mul_one]
      exact Int.mul_pos hcontent_pos hA_pos
    have hf_not_neg : ¬ DensePoly.leadingCoeff f < 0 := by omega
    unfold signedContentScalar
    rw [if_neg hf, if_neg hf_not_neg, hε, Int.mul_one]
  · -- ε = -1
    have hcontent_neg : ZPoly.content f * (-1 : Int) < 0 := by
      have hrw : ZPoly.content f * (-1 : Int) = -(ZPoly.content f) := by
        exact Int.mul_neg_one _
      rw [hrw]; omega
    have hf_neg : DensePoly.leadingCoeff f < 0 := by
      rw [h_f_leading, hε]
      exact Int.mul_neg_of_neg_of_pos hcontent_neg hA_pos
    unfold signedContentScalar
    rw [if_neg hf, if_pos hf_neg, hε, Int.mul_neg_one]

private theorem shift_mul_left_zpoly (k : Nat) (a b : ZPoly) :
    DensePoly.shift k (a * b) = DensePoly.shift k a * b := by
  rw [← DensePoly.monomial_one_mul_poly_eq_shift k (a * b),
    ← DensePoly.monomial_one_mul_poly_eq_shift k a]
  exact (DensePoly.mul_assoc_poly (S := Int) _ _ _).symm

/-- Scaling an integer polynomial by one is a no-op. -/
theorem densePoly_int_scale_one (p : ZPoly) :
    DensePoly.scale (1 : Int) p = p := by
  apply DensePoly.ext_coeff
  intro n
  simp [DensePoly.coeff_scale (R := Int)]

/--
The full normalized reassembly: combining the array-product layout from
`polyProduct_reassemblePolynomialFactors` with the signed content reconstruction
recovers the original polynomial exactly. Handles `f = 0` separately because
`signedContentScalar 0 = 0` collapses the scalar prefix.
-/
theorem reassemblePolynomialFactors_product_eq_input
    (f : ZPoly) (coreFactors : Array ZPoly)
    (hcore : Array.polyProduct coreFactors =
      (normalizeForFactor f).squareFreeCore) :
    DensePoly.C (signedContentScalar f) *
      Array.polyProduct
        (reassemblePolynomialFactors (normalizeForFactor f) coreFactors) = f := by
  rw [polyProduct_reassemblePolynomialFactors, hcore]
  by_cases hf : f = 0
  · subst hf
    have hsig : signedContentScalar (0 : ZPoly) = 0 := by
      unfold signedContentScalar
      simp
    rw [hsig]
    have hC0 : DensePoly.C (0 : Int) = (0 : ZPoly) := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_C, DensePoly.coeff_zero]
      split <;> rfl
    rw [hC0]
    exact DensePoly.zero_mul _
  · rw [ZPoly.C_mul_eq_scale]
    have hrearrange :
        DensePoly.shift (normalizeForFactor f).xPower (normalizeForFactor f).repeatedPart *
            (normalizeForFactor f).squareFreeCore =
          DensePoly.shift (normalizeForFactor f).xPower
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart) := by
      rw [← shift_mul_left_zpoly]
      rw [DensePoly.mul_comm_poly (S := Int)
        (normalizeForFactor f).repeatedPart (normalizeForFactor f).squareFreeCore]
    rw [hrearrange]
    exact normalizeForFactor_reassembles_signedContentScalar f hf

private theorem firstSome_some
    {α β : Type} {xs : List α} {f : α → Option β} {y : β}
    (h : firstSome xs f = some y) :
    ∃ x, f x = some y := by
  induction xs with
  | nil =>
      simp [firstSome] at h
  | cons x xs ih =>
      unfold firstSome at h
      cases hx : f x with
      | none =>
          simp [hx] at h
          exact ih h
      | some y' =>
          simp [hx] at h
          cases h
          exact ⟨x, hx⟩

private theorem firstSome_eq_some_of_append
    {α β : Type} (pre suffix : List α) (x : α) (f : α → Option β) (y : β)
    (hprefix : ∀ z ∈ pre, f z = none)
    (hx : f x = some y) :
    firstSome (pre ++ x :: suffix) f = some y := by
  induction pre with
  | nil =>
      simp [firstSome, hx]
  | cons z zs ih =>
      change
        (match f z with
        | some y' => some y'
        | none => firstSome (zs ++ x :: suffix) f) = some y
      rw [hprefix z (by simp)]
      exact ih (fun w hw => hprefix w (by simp [hw]))

/-- A subset split extends to the corresponding split after adjoining a required head. -/
theorem subsetSplitsWithFirst_mem_cons
    {factor : ZPoly} {factors selected rest : List ZPoly}
    (hmem : (selected, rest) ∈ subsetSplits factors) :
    (factor :: selected, rest) ∈ subsetSplitsWithFirst (factor :: factors) := by
  simp [subsetSplitsWithFirst, hmem]

/-- Constructor for `subsetSplits` membership on the empty list: the only
partition of the empty list is `([], [])`. -/
theorem subsetSplits_nil_mem :
    (([], []) : List ZPoly × List ZPoly) ∈ subsetSplits [] := by
  simp [subsetSplits]

/-- Constructor for `subsetSplits` membership on a cons list, head selected:
prepending `factor` to the `selected` side preserves enumerability. -/
theorem subsetSplits_cons_left_mem
    {factor : ZPoly} {factors selected rest : List ZPoly}
    (h : (selected, rest) ∈ subsetSplits factors) :
    (factor :: selected, rest) ∈ subsetSplits (factor :: factors) := by
  unfold subsetSplits
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_map.mpr ⟨(selected, rest), h, rfl⟩

/-- Constructor for `subsetSplits` membership on a cons list, head unselected:
prepending `factor` to the `rest` side preserves enumerability. -/
theorem subsetSplits_cons_right_mem
    {factor : ZPoly} {factors selected rest : List ZPoly}
    (h : (selected, rest) ∈ subsetSplits factors) :
    (selected, factor :: rest) ∈ subsetSplits (factor :: factors) := by
  unfold subsetSplits
  refine List.mem_append.mpr (Or.inl ?_)
  exact List.mem_map.mpr ⟨(selected, rest), h, rfl⟩

/-- Existence companion to `firstSome_some`: if `f x = some y` for some `x ∈ xs`,
then `firstSome xs f` is itself `some _`.  Used to chain executable completeness
arguments: showing the search at the current step can succeed reduces to
exhibiting a single subset whose candidate works. -/
theorem firstSome_isSome_of_mem
    {α β : Type} {xs : List α} {f : α → Option β} {x : α} {y : β}
    (hmem : x ∈ xs) (hxy : f x = some y) :
    (firstSome xs f).isSome = true := by
  induction xs with
  | nil => simp at hmem
  | cons z zs ih =>
      unfold firstSome
      cases hfz : f z with
      | some _ => simp
      | none =>
          rcases List.mem_cons.mp hmem with hxz | hxzs
          · subst hxz
            rw [hfz] at hxy
            cases hxy
          · simpa [hfz] using ih hxzs

private theorem recombinationSearchAux_product
    (target : ZPoly) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchAux target localFactors fuel = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        cases hquot : exactQuotient? target (Array.polyProduct split.1.toArray) with
        | none =>
            simp [hquot] at hsplit
        | some quotient =>
            simp [hquot] at hsplit
            cases hrec : recombinationSearchAux quotient split.2 fuel with
            | none =>
                simp [hrec] at hsplit
            | some rest =>
                simp [hrec] at hsplit
                cases hsplit
                have hrest :
                    Array.polyProduct rest.toArray = quotient :=
                  ih quotient split.2 rest hrec
                have hquot_prod :
                    quotient * Array.polyProduct split.1.toArray = target :=
                  exactQuotient?_product hquot
                calc
                  Array.polyProduct (Array.polyProduct split.1.toArray :: rest).toArray =
                      Array.polyProduct split.1.toArray * Array.polyProduct rest.toArray := by
                    exact ZPoly.polyProduct_cons_toArray (Array.polyProduct split.1.toArray) rest
                  _ = Array.polyProduct split.1.toArray * quotient := by
                    rw [hrest]
                  _ = quotient * Array.polyProduct split.1.toArray := by
                    rw [DensePoly.mul_comm_poly (S := Int)]
                  _ = target := hquot_prod

/-- A successful exhaustive recombination search preserves the target product. -/
theorem recombinationSearch_product
    (f : ZPoly) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearch f localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact recombinationSearchAux_product f localFactors factors (localFactors.length + 1) hsearch

private theorem recombinationSearchModAux_product
    (target : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchModAux target modulus localFactors fuel = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec : recombinationSearchModAux quotient modulus split.2 fuel with
              | none =>
                  simp [hrec] at hsplit
              | some rest =>
                  simp [hrec] at hsplit
                  cases hsplit
                  have hrest :
                      Array.polyProduct rest.toArray = quotient :=
                    ih quotient split.2 rest hrec
                  have hquot_prod : quotient * candidate = target :=
                    exactQuotient?_product hquot
                  calc
                    Array.polyProduct (candidate :: rest).toArray =
                        candidate * Array.polyProduct rest.toArray := by
                      exact ZPoly.polyProduct_cons_toArray candidate rest
                    _ = candidate * quotient := by
                      rw [hrest]
                    _ = quotient * candidate := by
                      rw [DensePoly.mul_comm_poly (S := Int)]
                    _ = target := hquot_prod
        · simp [candidate, hrecord] at hsplit

private theorem recombinationSearchMod_product
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact recombinationSearchModAux_product
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombinationSearchModAux_normalizeFactorSign
    (target : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchModAux target modulus localFactors fuel = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec : recombinationSearchModAux quotient modulus split.2 fuel with
              | none =>
                  simp [hrec] at hsplit
              | some rest =>
                  simp [hrec] at hsplit
                  cases hsplit
                  intro factor hmem
                  simp at hmem
                  cases hmem with
                  | inl hfactor =>
                      rw [hfactor]
                      exact normalizeFactorSign_idem
                        (ZPoly.primitivePart <|
                          centeredLiftPoly (Array.polyProduct split.1.toArray) modulus)
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem recombinationSearchModAux_shouldRecord
    (target : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchModAux target modulus localFactors fuel = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec : recombinationSearchModAux quotient modulus split.2 fuel with
              | none =>
                  simp [hrec] at hsplit
              | some rest =>
                  simp [hrec] at hsplit
                  cases hsplit
                  intro factor hmem
                  simp at hmem
                  cases hmem with
                  | inl hfactor =>
                      rw [hfactor]
                      exact hrecord
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem recombinationSearchMod_normalizeFactorSign
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor :=
  recombinationSearchModAux_normalizeFactorSign
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombinationSearchMod_shouldRecord
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true :=
  recombinationSearchModAux_shouldRecord
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombineExhaustive_product
    (f : ZPoly) (d : LiftData) (factors : List ZPoly)
    (hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList =
        some factors) :
    Array.polyProduct (recombineExhaustive f d) = f := by
  unfold recombineExhaustive
  simp [hsearch, recombinationSearchMod_product f (liftModulus d)
    d.liftedFactors.toList factors hsearch]

private theorem recombineExhaustive_normalizeFactorSign
    (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineExhaustive f d).toList,
      normalizeFactorSign factor = factor := by
  unfold recombineExhaustive
  cases hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact recombinationSearchMod_normalizeFactorSign f (liftModulus d)
        d.liftedFactors.toList factors hsearch factor (by simpa using hmem)

private theorem recombineExhaustive_shouldRecord
    (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineExhaustive f d).toList,
      shouldRecordPolynomialFactor factor = true := by
  unfold recombineExhaustive
  cases hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact recombinationSearchMod_shouldRecord f (liftModulus d)
        d.liftedFactors.toList factors hsearch factor (by simpa using hmem)

/-- Base case for the exhaustive recombination search: when the running target
has already been reduced to `1`, the search terminates and returns the empty
factor list. -/
theorem recombinationSearchModAux_one
    (modulus : Nat) (localFactors : List ZPoly) (fuel : Nat) :
    recombinationSearchModAux 1 modulus localFactors (fuel + 1) = some [] := by
  unfold recombinationSearchModAux
  simp

/-- Executable completeness of `recombinationSearchModAux`: if a single
exhaustive-search step can pick the candidate produced by centred-lifting
`selected` (a subset of `localFactors` whose order-preserving partition has
`rest` as complement), and the recursive search on the residual `(quotient,
rest)` succeeds with the supplied fuel, then the search at the current step
also succeeds.

This is the Mathlib-free step lemma underpinning Group A coverage proofs: it
exposes that any subset of the lifted local factors with a working candidate
is enumerated by `subsetSplitsWithFirst`, and that the search descends through
that candidate to the residual problem. -/
theorem recombinationSearchModAux_isSome_of_step
    {target candidate quotient : ZPoly} {modulus fuel : Nat}
    {localFactors selected rest : List ZPoly}
    (htarget_ne_one : target ≠ 1)
    (hsplit : (selected, rest) ∈ subsetSplitsWithFirst localFactors)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      (recombinationSearchModAux quotient modulus rest fuel).isSome = true) :
    (recombinationSearchModAux target modulus localFactors (fuel + 1)).isSome = true := by
  obtain ⟨restFactors, hrest⟩ := Option.isSome_iff_exists.mp hsearch_rest
  unfold recombinationSearchModAux
  rw [if_neg htarget_ne_one]
  refine firstSome_isSome_of_mem (y := candidate :: restFactors) hsplit ?_
  show (let candidate' := normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus rest fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = some (candidate :: restFactors)
  rw [show (normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus) = candidate
        from hcandidate_def.symm]
  rw [if_pos hrecord]
  simp only [hquot, hrest]

/-- Companion to `recombinationSearchModAux_isSome_of_step` at the
`recombinationSearchMod` surface.  Hides the fuel parameter, requiring the
caller to supply the recursive isSome witness already specialised to fuel
`localFactors.length`.  Useful for downstream callers that want to chain
step lemmas with a fixed shared fuel budget. -/
theorem recombinationSearchMod_isSome_of_step
    {target candidate quotient : ZPoly} {modulus : Nat}
    {localFactors selected rest : List ZPoly}
    (htarget_ne_one : target ≠ 1)
    (hsplit : (selected, rest) ∈ subsetSplitsWithFirst localFactors)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      (recombinationSearchModAux quotient modulus rest localFactors.length).isSome = true) :
    (recombinationSearchMod target modulus localFactors).isSome = true := by
  unfold recombinationSearchMod
  exact recombinationSearchModAux_isSome_of_step (fuel := localFactors.length)
    htarget_ne_one hsplit hcandidate_def hrecord hquot hsearch_rest

/--
Exact-output version of `recombinationSearchModAux_isSome_of_step`.

The earlier completeness lemma is intentionally weak: it only proves that the
search succeeds when a particular split would work.  This theorem is the
concrete-output companion used by coverage proofs: if that split is positioned
after a prefix whose recombination attempts all fail, then the executable
`firstSome` traversal returns the candidate from this split as the head of the
resulting factor list.
-/
theorem recombinationSearchModAux_eq_some_of_step_of_prefix_none
    {target candidate quotient : ZPoly} {modulus fuel : Nat}
    {localFactors selected rest restFactors : List ZPoly}
    {pre suffix : List (List ZPoly × List ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hsplits :
      subsetSplitsWithFirst localFactors = pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus split.2 fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      recombinationSearchModAux quotient modulus rest fuel = some restFactors) :
    recombinationSearchModAux target modulus localFactors (fuel + 1) =
      some (candidate :: restFactors) := by
  unfold recombinationSearchModAux
  rw [if_neg htarget_ne_one, hsplits]
  refine firstSome_eq_some_of_append pre suffix (selected, rest) _ _ hprefix ?_
  show (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus rest fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = some (candidate :: restFactors)
  rw [show (normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct selected.toArray) modulus) = candidate
        from hcandidate_def.symm]
  rw [if_pos hrecord]
  simp only [hquot, hsearch_rest]

/--
Surface exact-output companion for `recombinationSearchMod`.

This hides the fuel parameter in the same way as
`recombinationSearchMod_isSome_of_step`, while retaining the returned factor
list when the selected split is the first successful split.
-/
theorem recombinationSearchMod_eq_some_of_step_of_prefix_none
    {target candidate quotient : ZPoly} {modulus : Nat}
    {localFactors selected rest restFactors : List ZPoly}
    {pre suffix : List (List ZPoly × List ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hsplits :
      subsetSplitsWithFirst localFactors = pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match recombinationSearchModAux quotient' modulus split.2 localFactors.length with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart (centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      recombinationSearchModAux quotient modulus rest localFactors.length = some restFactors) :
    recombinationSearchMod target modulus localFactors =
      some (candidate :: restFactors) := by
  unfold recombinationSearchMod
  exact
    recombinationSearchModAux_eq_some_of_step_of_prefix_none
      (fuel := localFactors.length) htarget_ne_one hsplits hprefix
      hcandidate_def hrecord hquot hsearch_rest

/-- When `recombinationSearchMod` succeeds on the lifted-factor list, the
`recombineExhaustive` wrapper returns exactly the array of recovered factors.
This is the equality lemma that lets downstream irreducibility proofs replace a
`recombineExhaustive` term with a concrete factor list once the search is
known to succeed. -/
theorem recombineExhaustive_eq_of_recombinationSearchMod_some
    {f : ZPoly} {d : LiftData} {factors : List ZPoly}
    (h : recombinationSearchMod f (liftModulus d) d.liftedFactors.toList = some factors) :
    recombineExhaustive f d = factors.toArray := by
  unfold recombineExhaustive
  rw [h]

private theorem bhksRecoverClassified_success_product
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    Array.polyProduct candidates = f := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    by_cases hdeg :
        bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows)) = true
    · simp [hdeg] at hrecover
    · simp only [hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows)) with
      | none => simp [hcand] at hrecover
      | some cands =>
          simp only [hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            simpa [beq_iff_eq] using hprod
          · simp [hprod] at hrecover
  · rw [dif_neg hrows] at hrecover
    simp at hrecover

private theorem bhksRecoverClassified_success_all_of_candidates
    (P : ZPoly → Prop)
    (hall :
      ∀ {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
        {candidates : Array ZPoly},
        bhksIndicatorCandidates? f d indicators = some candidates →
          ∀ factor ∈ candidates.toList, P factor)
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, P factor := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows
    let indicators := bhksEquivalenceClassIndicators projected
    by_cases hdeg : bhksDegenerateIndicatorPartition projected indicators = true
    · simp [projected, indicators, hdeg] at hrecover
    · simp only [projected, indicators, hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d indicators with
      | none => simp [projected, indicators, hcand] at hrecover
      | some cands =>
          simp only [projected, indicators, hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            exact hall hcand
          · simp [hprod] at hrecover
  · rw [dif_neg hrows] at hrecover
    simp at hrecover

private theorem bhksRecoverClassified_success_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (h : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, normalizeFactorSign factor = factor :=
  bhksRecoverClassified_success_all_of_candidates
    (fun factor => normalizeFactorSign factor = factor)
    (fun hcand => bhksIndicatorCandidates?_normalizeFactorSign hcand) h

private theorem bhksRecoverClassified_success_shouldRecord
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (h : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, shouldRecordPolynomialFactor factor = true :=
  bhksRecoverClassified_success_all_of_candidates
    (fun factor => shouldRecordPolynomialFactor factor = true)
    (fun hcand => bhksIndicatorCandidates?_shouldRecord hcand) h

/-- A successful BHKS recovery emits only candidates that divide `f`,
since each candidate has passed the executable exact-division check
inside `bhksIndicatorCandidate?`.  The dependence of the conclusion on
`f` prevents a one-liner via `bhksRecoverClassified_success_all_of_candidates`,
so we unfold `bhksRecoverClassified` directly. -/
private theorem bhksRecoverClassified_success_dvd
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    ∀ factor ∈ candidates.toList, factor ∣ f := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows
    let indicators := bhksEquivalenceClassIndicators projected
    by_cases hdeg : bhksDegenerateIndicatorPartition projected indicators = true
    · simp [projected, indicators, hdeg] at hrecover
    · simp only [projected, indicators, hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d indicators with
      | none => simp [projected, indicators, hcand] at hrecover
      | some cands =>
          simp only [projected, indicators, hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            exact bhksIndicatorCandidates?_dvd hcand
          · simp [hprod] at hrecover
  · rw [dif_neg hrows] at hrecover
    simp at hrecover

/-- A successful BHKS recovery call preserves the polynomial product: when
`bhksRecover? f d` returns `some candidates`, the candidates multiply back
to `f` because the executable runs a final `Array.polyProduct candidates == f`
check before reporting success. -/
private theorem bhksRecover?_product
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecover? f d = some candidates) :
    Array.polyProduct candidates = f := by
  rw [bhksRecover?] at hrecover
  cases hclass : bhksRecoverClassified f d with
  | success cands =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover
      cases hrecover
      exact bhksRecoverClassified_success_product hclass
  | degenerate =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover
  | candidateFailure =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover
  | productMismatch cands =>
      simp [BhksRecoveryResult.toOption, hclass] at hrecover

/-- A successful fixed-precision BHKS fast-recombination loop preserves the
polynomial product: every success branch comes from the classified BHKS
recovery success case, which already certifies `Array.polyProduct = core`. -/
theorem bhksRecoveryCoreWithBound_product
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    ∀ k fuel coreFactors,
      bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors →
        Array.polyProduct coreFactors = core := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro coreFactors hfast
      simp [bhksRecoveryCoreWithBound, bhksRecoveryLoop] at hfast
  | succ fuel ih =>
      intro coreFactors hfast
      rw [bhksRecoveryCoreWithBound_unfold] at hfast
      cases hclass : bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
      | success xs =>
          by_cases hfloor : k ≥ bhksRecoveryFloor core
          · simp [hclass, hfloor] at hfast
            cases hfast
            exact bhksRecoverClassified_success_product hclass
          · by_cases hk : k ≥ B
            · simp [hclass, hfloor, hk] at hfast
            · simp [hclass, hfloor, hk] at hfast
              exact ih _ coreFactors hfast
      | degenerate =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | candidateFailure =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | productMismatch cands =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast

/-- A successful classified recovery exposes the underlying indicator-candidate
reconstruction: there is a positive-dimension witness `hrows` for which the
equivalence-class indicator candidates reconstruct exactly to `candidates`, and
the chosen indicator partition is non-degenerate. Private because the conclusion
names `bhksRecoverClassified`; the public extractor
`bhksRecoveryCoreWithBound_some_indicatorCandidates` re-exposes this in
`bhksRecoverClassified`-free form. -/
private theorem bhksRecoverClassified_success_indicatorCandidates
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    ∃ hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
        (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth,
      bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
        some candidates ∧
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
        false := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    by_cases hdeg :
        bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows)) = true
    · simp [hdeg] at hrecover
    · simp only [hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows)) with
      | none => simp [hcand] at hrecover
      | some cands =>
          simp only [hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            exact ⟨hrows, hcand, by simpa using hdeg⟩
          · simp [hprod] at hrecover
  · rw [dif_neg hrows] at hrecover
    simp at hrecover

/-- A successful fast-recombination loop is witnessed by a concrete precision
schedule index `k'` at which the classified BHKS recovery succeeds. This retains
the successful `toMonicLiftData` precision that the per-factor success lemmas
(`bhksRecoveryCoreWithBound_some_dvd`, `_shouldRecord`, …) discard, so proof-facing
callers can reconstruct the underlying recovery data and indicator candidates.
Private because the conclusion names `bhksRecoverClassified`; the public extractor
`bhksRecoveryCoreWithBound_some_indicatorCandidates` re-exposes the recovery data in
`bhksRecoverClassified`-free form. -/
private theorem bhksRecoveryCoreWithBound_some_classifiedSuccess
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    ∀ k fuel coreFactors,
      bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors →
        ∃ k', bhksRecoverClassified core (ZPoly.directLiftData core k' primeData) =
          .success coreFactors ∧ bhksRecoveryFloor core ≤ k' := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro coreFactors hfast
      simp [bhksRecoveryCoreWithBound, bhksRecoveryLoop] at hfast
  | succ fuel ih =>
      intro coreFactors hfast
      rw [bhksRecoveryCoreWithBound_unfold] at hfast
      cases hclass : bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
      | success xs =>
          by_cases hfloor : k ≥ bhksRecoveryFloor core
          · simp [hclass, hfloor] at hfast
            cases hfast
            exact ⟨k, hclass, hfloor⟩
          · by_cases hk : k ≥ B
            · simp [hclass, hfloor, hk] at hfast
            · simp [hclass, hfloor, hk] at hfast
              exact ih _ coreFactors hfast
      | degenerate =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | candidateFailure =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | productMismatch cands =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast

/-- Proof-facing recovery-data extractor for the fast-recombination loop, stated
without reference to the private `bhksRecoverClassified`. A successful
`bhksRecoveryCoreWithBound` call is witnessed by a concrete precision-schedule index
`k'`: at the `toMonicLiftData` for that precision there is a positive-dimension
witness `hrows` whose equivalence-class indicator candidates reconstruct exactly
to `coreFactors`, the indicator partition is non-degenerate, and the candidates
multiply back to `core`. This is the correspondence-side entry point used to rebuild the
forward-recovery package (and hence the selected support/subset witnesses) that
the per-factor success lemmas discard. -/
theorem bhksRecoveryCoreWithBound_some_indicatorCandidates
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    ∃ k',
      ∃ hrows :
        1 ≤ (bhksLatticeBasis core
              (ZPoly.directLiftData core k' primeData).p
              (ZPoly.directLiftData core k' primeData).k
              (ZPoly.directLiftData core k' primeData).liftedFactors).factorCount +
            (bhksLatticeBasis core
              (ZPoly.directLiftData core k' primeData).p
              (ZPoly.directLiftData core k' primeData).k
              (ZPoly.directLiftData core k' primeData).liftedFactors).coeffWidth,
      bhksIndicatorCandidates? core (ZPoly.directLiftData core k' primeData)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis core
                (ZPoly.directLiftData core k' primeData).p
                (ZPoly.directLiftData core k' primeData).k
                (ZPoly.directLiftData core k' primeData).liftedFactors)
              hrows)) =
        some coreFactors ∧
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows
            (bhksLatticeBasis core
              (ZPoly.directLiftData core k' primeData).p
              (ZPoly.directLiftData core k' primeData).k
              (ZPoly.directLiftData core k' primeData).liftedFactors)
            hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis core
                (ZPoly.directLiftData core k' primeData).p
                (ZPoly.directLiftData core k' primeData).k
                (ZPoly.directLiftData core k' primeData).liftedFactors)
              hrows)) =
        false ∧
      Array.polyProduct coreFactors = core ∧ bhksRecoveryFloor core ≤ k' := by
  obtain ⟨k', hsuccess, hfloor⟩ :=
    bhksRecoveryCoreWithBound_some_classifiedSuccess core B primeData k fuel coreFactors h
  obtain ⟨hrows, hcand, hdeg⟩ :=
    bhksRecoverClassified_success_indicatorCandidates hsuccess
  exact ⟨k', hrows, hcand, hdeg, bhksRecoverClassified_success_product hsuccess, hfloor⟩

private theorem bhksRecoveryCoreWithBound_some_all_of_recovery
    (P : ZPoly → Prop)
    (hrecover :
      ∀ {core : ZPoly} {d : LiftData} {candidates : Array ZPoly},
        bhksRecoverClassified core d = .success candidates →
          ∀ factor ∈ candidates.toList, P factor)
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    ∀ k fuel coreFactors,
      bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors →
        ∀ factor ∈ coreFactors.toList, P factor := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro coreFactors hfast
      simp [bhksRecoveryCoreWithBound, bhksRecoveryLoop] at hfast
  | succ fuel ih =>
      intro coreFactors hfast
      rw [bhksRecoveryCoreWithBound_unfold] at hfast
      cases hclass : bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
      | success xs =>
          by_cases hfloor : k ≥ bhksRecoveryFloor core
          · simp [hclass, hfloor] at hfast
            cases hfast
            exact hrecover hclass
          · by_cases hk : k ≥ B
            · simp [hclass, hfloor, hk] at hfast
            · simp [hclass, hfloor, hk] at hfast
              exact ih _ coreFactors hfast
      | degenerate =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | candidateFailure =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | productMismatch cands =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast

/-- Successful lattice recovery returns factors with normalized signs. -/
theorem bhksRecoveryCoreWithBound_some_normalizeFactorSign
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, normalizeFactorSign factor = factor :=
  bhksRecoveryCoreWithBound_some_all_of_recovery
    (fun factor => normalizeFactorSign factor = factor)
    (fun hrecover => bhksRecoverClassified_success_normalizeFactorSign hrecover)
    core B primeData k fuel coreFactors h

/-- Successful lattice recovery returns only nonconstant polynomial factors. -/
theorem bhksRecoveryCoreWithBound_some_shouldRecord
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, shouldRecordPolynomialFactor factor = true :=
  bhksRecoveryCoreWithBound_some_all_of_recovery
    (fun factor => shouldRecordPolynomialFactor factor = true)
    (fun hrecover => bhksRecoverClassified_success_shouldRecord hrecover)
    core B primeData k fuel coreFactors h

/-- Every factor returned by successful lattice recovery has positive degree. -/
theorem bhksRecoveryCoreWithBound_some_degree_pos
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, 0 < factor.degree?.getD 0 :=
  bhksRecoveryCoreWithBound_some_all_of_recovery
    (fun factor => 0 < factor.degree?.getD 0)
    (fun hrecover =>
      bhksRecoverClassified_success_all_of_candidates
        (fun factor => 0 < factor.degree?.getD 0)
        (fun hcand => bhksIndicatorCandidates?_positive_degree hcand) hrecover)
    core B primeData k fuel coreFactors h

/-- Every factor emitted by the BHKS fast-recombination loop divides the
input polynomial. The success branch is the only branch that exits with
`some coreFactors`, and `bhksRecoverClassified_success_dvd` certifies
divisibility for each candidate at that exit. -/
theorem bhksRecoveryCoreWithBound_some_dvd
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    ∀ k fuel coreFactors,
      bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors →
        ∀ factor ∈ coreFactors.toList, factor ∣ core := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro coreFactors hfast
      simp [bhksRecoveryCoreWithBound, bhksRecoveryLoop] at hfast
  | succ fuel ih =>
      intro coreFactors hfast
      rw [bhksRecoveryCoreWithBound_unfold] at hfast
      cases hclass : bhksRecoverClassified core (ZPoly.directLiftData core k primeData) with
      | success xs =>
          by_cases hfloor : k ≥ bhksRecoveryFloor core
          · simp [hclass, hfloor] at hfast
            cases hfast
            exact bhksRecoverClassified_success_dvd hclass
          · by_cases hk : k ≥ B
            · simp [hclass, hfloor, hk] at hfast
            · simp [hclass, hfloor, hk] at hfast
              exact ih _ coreFactors hfast
      | degenerate =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | candidateFailure =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast
      | productMismatch cands =>
          by_cases hk : k ≥ B
          · simp [hclass, hk] at hfast
          · simp [hclass, hk] at hfast
            exact ih _ coreFactors hfast

/-- The leading coefficient of an `Array.polyProduct` over a list of polynomials
with strictly positive leading coefficients is strictly positive. Chains
`ZPoly.leadingCoeff_mul_pos_of_pos` through the foldl unfold given by
`ZPoly.polyProduct_cons_toArray`. -/
private theorem leadingCoeff_polyProduct_toArray_pos :
    ∀ (factors : List ZPoly),
      (∀ q ∈ factors, 0 < DensePoly.leadingCoeff q) →
      0 < DensePoly.leadingCoeff (Array.polyProduct factors.toArray) := by
  intro factors
  induction factors with
  | nil =>
      intro _
      change 0 < DensePoly.leadingCoeff (Array.polyProduct (#[] : Array ZPoly))
      change 0 < DensePoly.leadingCoeff (1 : ZPoly)
      decide
  | cons head rest ih =>
      intro hpos
      have hhead_pos : 0 < DensePoly.leadingCoeff head := hpos head List.mem_cons_self
      have hrest_pos : ∀ q ∈ rest, 0 < DensePoly.leadingCoeff q :=
        fun q hq => hpos q (List.mem_cons_of_mem _ hq)
      rw [ZPoly.polyProduct_cons_toArray]
      exact ZPoly.leadingCoeff_mul_pos_of_pos head _ hhead_pos (ih hrest_pos)

/-- If the executable `Array.polyProduct` of a list of polynomials is monic and
every entry has positive leading coefficient, then every entry is monic.

The product of positive integer leading coefficients equals the monic product's
leading coefficient `1`; since each factor is a positive integer, each must
itself be `1`. Used by the exhaustive-arm reassembly discharger to recover
monicness of emitted factors of the square-free part from monicness of the primitive square-free part. -/
private theorem polyProduct_toArray_monic_factors_monic_of_pos_lc :
    ∀ (factors : List ZPoly),
      DensePoly.Monic (Array.polyProduct factors.toArray) →
      (∀ q ∈ factors, 0 < DensePoly.leadingCoeff q) →
      ∀ q ∈ factors, DensePoly.Monic q := by
  intro factors
  induction factors with
  | nil =>
      intro _ _ q hq
      cases hq
  | cons head rest ih =>
      intro hmonic hpos q hq
      have hhead_pos : 0 < DensePoly.leadingCoeff head := hpos head List.mem_cons_self
      have hrest_pos : ∀ q' ∈ rest, 0 < DensePoly.leadingCoeff q' :=
        fun q' hq' => hpos q' (List.mem_cons_of_mem _ hq')
      have hhead_ne : head ≠ 0 := by
        intro h0
        rw [h0] at hhead_pos
        change (0 : Int) < DensePoly.leadingCoeff (0 : ZPoly) at hhead_pos
        have hzero : DensePoly.leadingCoeff (0 : ZPoly) = 0 := by simp
        rw [hzero] at hhead_pos
        exact absurd hhead_pos (by decide)
      have hrest_lc_pos : 0 < DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
        leadingCoeff_polyProduct_toArray_pos rest hrest_pos
      have hrest_prod_ne : Array.polyProduct rest.toArray ≠ 0 := by
        intro h0
        rw [h0] at hrest_lc_pos
        change (0 : Int) < DensePoly.leadingCoeff (0 : ZPoly) at hrest_lc_pos
        have hzero : DensePoly.leadingCoeff (0 : ZPoly) = 0 := by simp
        rw [hzero] at hrest_lc_pos
        exact absurd hrest_lc_pos (by decide)
      have hprod_eq :
          Array.polyProduct (head :: rest).toArray =
            head * Array.polyProduct rest.toArray :=
        ZPoly.polyProduct_cons_toArray head rest
      have hlc_mul :
          DensePoly.leadingCoeff (head * Array.polyProduct rest.toArray) =
            DensePoly.leadingCoeff head *
              DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
        ZPoly.leadingCoeff_mul_of_nonzero head _ hhead_ne hrest_prod_ne
      have hmonic_unfold :
          DensePoly.leadingCoeff (Array.polyProduct (head :: rest).toArray) = 1 :=
        hmonic
      have hone :
          DensePoly.leadingCoeff head *
              DensePoly.leadingCoeff (Array.polyProduct rest.toArray) = 1 := by
        rw [← hlc_mul, ← hprod_eq]
        exact hmonic_unfold
      have ha : 1 ≤ DensePoly.leadingCoeff head := hhead_pos
      have hb : 1 ≤ DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
        hrest_lc_pos
      -- From `a * b = 1` with `a ≥ 1`, `b ≥ 1`: `a * 1 ≤ a * b = 1`, so `a ≤ 1`.
      -- Combined with `a ≥ 1`, `a = 1`.
      have hhead_eq : DensePoly.leadingCoeff head = 1 := by
        have hupper :
            DensePoly.leadingCoeff head * 1 ≤
              DensePoly.leadingCoeff head *
                DensePoly.leadingCoeff (Array.polyProduct rest.toArray) :=
          Int.mul_le_mul (Int.le_refl _) hb (by decide : (0 : Int) ≤ 1)
            (by omega : (0 : Int) ≤ DensePoly.leadingCoeff head)
        rw [Int.mul_one, hone] at hupper
        omega
      have hrest_eq :
          DensePoly.leadingCoeff (Array.polyProduct rest.toArray) = 1 := by
        have hone' := hone
        rw [hhead_eq, Int.one_mul] at hone'
        exact hone'
      have hrest_monic : DensePoly.Monic (Array.polyProduct rest.toArray) := hrest_eq
      have hhead_monic : DensePoly.Monic head := hhead_eq
      rw [List.mem_cons] at hq
      rcases hq with hh | hr
      · rw [hh]; exact hhead_monic
      · exact ih hrest_monic hrest_pos q hr

/-- A primitive, sign-normalized `ZPoly` that passes `shouldRecordPolynomialFactor`
has positive `degree?`. A size-`1` such polynomial combines `Primitive q`
(forcing `|q.coeff 0| = 1`) with `normalizeFactorSign q = q` (forcing
`0 ≤ q.coeff 0`) to conclude `q = 1`, which `shouldRecord` excludes. -/
theorem degree_pos_of_primitive_norm_record
    (q : ZPoly)
    (hq_primitive : ZPoly.Primitive q)
    (hq_norm : normalizeFactorSign q = q)
    (hq_record : shouldRecordPolynomialFactor q = true) :
    0 < q.degree?.getD 0 := by
  rcases Nat.eq_zero_or_pos (q.degree?.getD 0) with hdeg_eq | hpos
  case inr => exact hpos
  case inl =>
    exfalso
    have hq_ne : q ≠ 0 := by
      unfold shouldRecordPolynomialFactor at hq_record
      simp at hq_record
      exact hq_record.1.1
    have hq_size_pos : 0 < q.size := ZPoly.size_pos_of_ne_zero q hq_ne
    have hdeg_unfold : q.degree?.getD 0 =
        (if q.size = 0 then 0 else q.size - 1) := by
      unfold DensePoly.degree?
      by_cases h : q.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hdeg_eq
    have hsize_eq : q.size = 1 := by
      by_cases h : q.size = 0
      · omega
      · split at hdeg_eq <;> omega
    have hq_eq_C : q = DensePoly.C (q.coeff 0) := ZPoly.eq_C_of_size_eq_one q hsize_eq
    have hq_lc : DensePoly.leadingCoeff q = q.coeff 0 := by
      rw [DensePoly.leadingCoeff_eq_coeff_last q hq_size_pos]
      congr 1; omega
    have hq_lc_nonneg : 0 ≤ DensePoly.leadingCoeff q := by
      rw [← hq_norm]
      exact normalizeFactorSign_leadingCoeff_nonneg q
    have hq_coeff0_nonneg : 0 ≤ q.coeff 0 := by rw [← hq_lc]; exact hq_lc_nonneg
    -- Primitive q + q = C (q.coeff 0) ⇒ |q.coeff 0| = 1, then ≥ 0 ⇒ = 1.
    have hcontent_q_eq : ZPoly.content q = Int.ofNat (q.coeff 0).natAbs :=
      (congrArg DensePoly.content hq_eq_C).trans (DensePoly.content_C (q.coeff 0))
    have hcontent_q_one : ZPoly.content q = 1 := hq_primitive
    have habs1 : (q.coeff 0).natAbs = 1 := by
      have hcast : (((q.coeff 0).natAbs : Int)) = (1 : Int) := by
        rw [← Int.ofNat_eq_natCast, ← hcontent_q_eq]; exact hcontent_q_one
      exact_mod_cast hcast
    have hq_coeff0_eq : q.coeff 0 = 1 := by
      rcases Int.natAbs_eq (q.coeff 0) with h | h
      · rw [h, habs1]; rfl
      · rw [h, habs1] at hq_coeff0_nonneg
        omega
    have hq_one : q = 1 := by
      rw [hq_eq_C, hq_coeff0_eq]
      rfl
    unfold shouldRecordPolynomialFactor at hq_record
    simp [hq_one] at hq_record

end Hex
