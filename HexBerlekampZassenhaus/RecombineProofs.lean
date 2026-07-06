/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.IrreducibleCore
public meta import HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.IrreducibleCore

public section
set_option backward.proofsInPublic true

/-!
This module collects the recombination and `bhksRecover*` correctness proofs and core-factors specifications.
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

/--
The full normalized reassembly: combining the array-product layout from
`polyProduct_reassemblePolynomialFactors` with the signed content reconstruction
recovers the original polynomial exactly. Handles `f = 0` separately because
`signedContentScalar 0 = 0` collapses the scalar prefix.
-/
private theorem reassemblePolynomialFactors_product_eq_input
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

private theorem scaledRecombinationSearchModAux_normalizeFactorSign
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              ZPoly.dilate coreLc <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
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
                          ZPoly.dilate coreLc <|
                            centeredLiftPoly
                              (Array.polyProduct split.1.toArray) modulus)
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem scaledRecombinationSearchModAux_shouldRecord
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              ZPoly.dilate coreLc <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
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

private theorem scaledRecombinationSearchModAux_primitive
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    ∀ factor ∈ factors, ZPoly.Primitive factor := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simp
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              ZPoly.dilate coreLc <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
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
                      -- The head emitted candidate is primitive: from
                      -- `hrecord` we get nonzeroness of the candidate, which
                      -- (via `normalizeFactorSign_ne_zero_of_ne_zero`)
                      -- propagates back through `primitivePart`'s
                      -- zero-condition (`primitivePart_eq_zero_of_content_eq_zero`)
                      -- to `content (centeredLift ...) ≠ 0`, hence
                      -- `Primitive (primitivePart (centeredLift ...))` by
                      -- `primitivePart_primitive`, and finally
                      -- `Primitive (normalizeFactorSign ...)` by deliverable 1.
                      have hcand_ne :
                          normalizeFactorSign (ZPoly.primitivePart
                              (ZPoly.dilate coreLc
                                (centeredLiftPoly
                                  (Array.polyProduct split.1.toArray) modulus))) ≠ 0 := by
                        unfold shouldRecordPolynomialFactor at hrecord
                        simp at hrecord
                        exact hrecord.1.1
                      have hpp_ne :
                          ZPoly.primitivePart
                              (ZPoly.dilate coreLc
                                (centeredLiftPoly
                                  (Array.polyProduct split.1.toArray) modulus)) ≠ 0 := by
                        intro hpp
                        apply hcand_ne
                        rw [hpp]
                        unfold normalizeFactorSign
                        rw [if_neg
                          (by simp : ¬ DensePoly.leadingCoeff (0 : ZPoly) < 0)]
                      have hcontent_ne :
                          ZPoly.content
                              (ZPoly.dilate coreLc
                                (centeredLiftPoly
                                  (Array.polyProduct split.1.toArray) modulus)) ≠ 0 := by
                        intro hcontent
                        apply hpp_ne
                        show DensePoly.primitivePart _ = 0
                        exact DensePoly.primitivePart_eq_zero_of_content_eq_zero _
                          (by simpa [ZPoly.content] using hcontent)
                      have hpp_primitive :
                          ZPoly.Primitive
                            (ZPoly.primitivePart
                              (ZPoly.dilate coreLc
                                (centeredLiftPoly
                                  (Array.polyProduct split.1.toArray) modulus))) :=
                        ZPoly.primitivePart_primitive _ hcontent_ne
                      exact normalizeFactorSign_primitive _ hpp_primitive
                  | inr hrest =>
                      exact ih quotient split.2 rest hrec factor hrest
        · simp [candidate, hrecord] at hsplit

private theorem scaledRecombinationSearchMod_normalizeFactorSign
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    ∀ factor ∈ factors, normalizeFactorSign factor = factor :=
  scaledRecombinationSearchModAux_normalizeFactorSign
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem scaledRecombinationSearchMod_primitive
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    ∀ factor ∈ factors, ZPoly.Primitive factor :=
  scaledRecombinationSearchModAux_primitive
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem scaledRecombinationSearchMod_shouldRecord
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    ∀ factor ∈ factors, shouldRecordPolynomialFactor factor = true :=
  scaledRecombinationSearchModAux_shouldRecord
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

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

private theorem recombineScaledExhaustive_normalizeFactorSign
    (coreLc : Int) (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineScaledExhaustive coreLc f d).toList,
      normalizeFactorSign factor = factor := by
  unfold recombineScaledExhaustive
  cases hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact scaledRecombinationSearchMod_normalizeFactorSign coreLc f
        (liftModulus d) d.liftedFactors.toList factors hsearch factor
        (by simpa using hmem)

private theorem recombineScaledExhaustive_primitive
    (coreLc : Int) (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineScaledExhaustive coreLc f d).toList,
      ZPoly.Primitive factor := by
  unfold recombineScaledExhaustive
  cases hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact scaledRecombinationSearchMod_primitive coreLc f
        (liftModulus d) d.liftedFactors.toList factors hsearch factor
        (by simpa using hmem)

private theorem recombineScaledExhaustive_shouldRecord
    (coreLc : Int) (f : ZPoly) (d : LiftData) :
    ∀ factor ∈ (recombineScaledExhaustive coreLc f d).toList,
      shouldRecordPolynomialFactor factor = true := by
  unfold recombineScaledExhaustive
  cases hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList with
  | none =>
      simp
  | some factors =>
      intro factor hmem
      exact scaledRecombinationSearchMod_shouldRecord coreLc f (liftModulus d)
        d.liftedFactors.toList factors hsearch factor (by simpa using hmem)

private theorem scaledRecombinationSearchModAux_product
    (coreLc : Int) (target : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch :
      scaledRecombinationSearchModAux coreLc target modulus localFactors fuel
        = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [scaledRecombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              ZPoly.dilate coreLc <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        by_cases hrecord : shouldRecordPolynomialFactor candidate = true
        · simp [candidate, hrecord] at hsplit
          cases hquot : exactQuotient? target candidate with
          | none =>
              simp [candidate, hquot] at hsplit
          | some quotient =>
              simp [candidate, hquot] at hsplit
              cases hrec :
                  scaledRecombinationSearchModAux coreLc quotient modulus
                    split.2 fuel with
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

private theorem scaledRecombinationSearchMod_product
    (coreLc : Int) (f : ZPoly) (modulus : Nat)
    (localFactors factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f modulus localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact scaledRecombinationSearchModAux_product
    coreLc f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombineScaledExhaustive_product
    (coreLc : Int) (f : ZPoly) (d : LiftData) (factors : List ZPoly)
    (hsearch :
      scaledRecombinationSearchMod coreLc f (liftModulus d) d.liftedFactors.toList =
        some factors) :
    Array.polyProduct (recombineScaledExhaustive coreLc f d) = f := by
  unfold recombineScaledExhaustive
  simp [hsearch, scaledRecombinationSearchMod_product coreLc f (liftModulus d)
    d.liftedFactors.toList factors hsearch]

/-- Pointwise: scaling a `ZPoly` by the integer `1` is a no-op. -/
theorem densePoly_int_scale_one (p : ZPoly) :
    DensePoly.scale (1 : Int) p = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) 1 p n (Int.mul_zero 1)]
  exact Int.one_mul (p.coeff n)

/-- `scaledRecombinationSearchModAux` at `coreLc = 1` collapses to the unscaled
`recombinationSearchModAux`: the only difference between the two routines is the
inner `ZPoly.dilate coreLc` applied to the centre-lifted lifted-factor product,
which is a no-op when `coreLc = 1`. -/
private theorem scaledRecombinationSearchModAux_eq_recombinationSearchModAux_of_one
    (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) (fuel : Nat) :
    scaledRecombinationSearchModAux 1 target modulus localFactors fuel =
      recombinationSearchModAux target modulus localFactors fuel := by
  induction fuel generalizing target localFactors with
  | zero => rfl
  | succ fuel ih =>
      unfold scaledRecombinationSearchModAux recombinationSearchModAux
      by_cases htarget : target = 1
      · simp [htarget]
      · simp only [htarget, if_false]
        congr 1
        funext split
        simp only [ZPoly.dilate_one]
        by_cases hrecord :
            shouldRecordPolynomialFactor (normalizeFactorSign <|
                ZPoly.primitivePart <|
                  centeredLiftPoly (Array.polyProduct split.1.toArray) modulus) = true
        · simp only [hrecord, if_true]
          cases hquot : exactQuotient? target (normalizeFactorSign <|
              ZPoly.primitivePart <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus) with
          | none => rfl
          | some quotient =>
              simp only [ih]
        · simp only [hrecord, Bool.false_eq_true, if_false]

/-- Surface-level collapse: `scaledRecombinationSearchMod 1 = recombinationSearchMod`. -/
private theorem scaledRecombinationSearchMod_eq_recombinationSearchMod_of_one
    (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    scaledRecombinationSearchMod 1 f modulus localFactors =
      recombinationSearchMod f modulus localFactors := by
  unfold scaledRecombinationSearchMod recombinationSearchMod
  exact scaledRecombinationSearchModAux_eq_recombinationSearchModAux_of_one
    f modulus localFactors (localFactors.length + 1)

/-- Executable collapse: `recombineScaledExhaustive 1 = recombineExhaustive`.

The scaled and unscaled exhaustive recombination wrappers agree when the
scaling coefficient is `1` (i.e., for monic cores), translating an unscaled
search witness into the scaled executable call site introduced by the swap. -/
theorem recombineScaledExhaustive_eq_recombineExhaustive_of_one
    (f : ZPoly) (d : LiftData) :
    recombineScaledExhaustive 1 f d = recombineExhaustive f d := by
  unfold recombineScaledExhaustive recombineExhaustive
  rw [scaledRecombinationSearchMod_eq_recombinationSearchMod_of_one]

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
Scaled-candidate counterpart of `recombinationSearchModAux_eq_some_of_step_of_prefix_none`.

Structurally identical to the unscaled step lemma, with the inner `let
candidate' := ...` expression in both the prefix-none hypothesis and the goal
applying `ZPoly.dilate coreLc` (the substitution `X ↦ coreLc · X`) to the
centre-lifted lifted-factor product.  This is the step driver the primitive
recursive coverage proof in #4647 will use, where the candidate is recovered
from the integer factor via `scaledRecombinationCandidate_eq_factor_of_recovery`.
-/
theorem scaledRecombinationSearchModAux_eq_some_of_step_of_prefix_none
    {coreLc : Int} {target candidate quotient : ZPoly} {modulus fuel : Nat}
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
              ZPoly.dilate coreLc <|
                centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match scaledRecombinationSearchModAux coreLc quotient' modulus
                  split.2 fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = normalizeFactorSign
        (ZPoly.primitivePart
          (ZPoly.dilate coreLc
            (centeredLiftPoly (Array.polyProduct selected.toArray) modulus))))
    (hrecord : shouldRecordPolynomialFactor candidate = true)
    (hquot : exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      scaledRecombinationSearchModAux coreLc quotient modulus rest fuel =
        some restFactors) :
    scaledRecombinationSearchModAux coreLc target modulus localFactors
        (fuel + 1) =
      some (candidate :: restFactors) := by
  unfold scaledRecombinationSearchModAux
  rw [if_neg htarget_ne_one, hsplits]
  refine firstSome_eq_some_of_append pre suffix (selected, rest) _ _ hprefix ?_
  show (let candidate' :=
          normalizeFactorSign <|
            ZPoly.primitivePart <|
              ZPoly.dilate coreLc <|
                centeredLiftPoly (Array.polyProduct selected.toArray) modulus
        if shouldRecordPolynomialFactor candidate' then
          match exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match scaledRecombinationSearchModAux coreLc quotient' modulus
                  rest fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = some (candidate :: restFactors)
  rw [show (normalizeFactorSign <|
            ZPoly.primitivePart <|
              ZPoly.dilate coreLc <|
                centeredLiftPoly (Array.polyProduct selected.toArray) modulus)
              = candidate
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

/-- Scaled-candidate counterpart of
`recombineExhaustive_eq_of_recombinationSearchMod_some`: when the scaled
search succeeds on the lifted-factor list, `recombineScaledExhaustive`
returns exactly the array of recovered factors. -/
theorem recombineScaledExhaustive_eq_of_scaledRecombinationSearchMod_some
    {coreLc : Int} {f : ZPoly} {d : LiftData} {factors : List ZPoly}
    (h : scaledRecombinationSearchMod coreLc f (liftModulus d)
        d.liftedFactors.toList = some factors) :
    recombineScaledExhaustive coreLc f d = factors.toArray := by
  unfold recombineScaledExhaustive
  rw [h]

private theorem bhksRecoverClassified_success_product
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassified f d = .success candidates) :
    Array.polyProduct candidates = f := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    by_cases hdeg :
        bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors)
              hrows)) = true
    · simp [hdeg] at hrecover
    · simp only [hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors)
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
  by_cases hrows : 1 ≤ (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows
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
  by_cases hrows : 1 ≤ (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows
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
      cases hclass : bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
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
    ∃ hrows : 1 ≤ (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).factorCount +
        (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).coeffWidth,
      bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)) =
        some candidates ∧
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)) =
        false := by
  rw [bhksRecoverClassified] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    by_cases hdeg :
        bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors)
              hrows)) = true
    · simp [hdeg] at hrecover
    · simp only [hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidates? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis (ZPoly.toMonic f).monic d.p d.k d.liftedFactors)
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

private theorem bhksRecoverClassifiedCore_success_product
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassifiedCore f d = .success candidates) :
    Array.polyProduct candidates = f := by
  rw [bhksRecoverClassifiedCore] at hrecover
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
      cases hcand : bhksIndicatorCandidatesCore? f d
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

private theorem bhksRecoverClassifiedCore_success_all_of_candidates
    (P : ZPoly → Prop)
    (hall :
      ∀ {f : ZPoly} {d : LiftData} {indicators : Array (Array Int)}
        {candidates : Array ZPoly},
        bhksIndicatorCandidatesCore? f d indicators = some candidates →
          ∀ factor ∈ candidates.toList, P factor)
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassifiedCore f d = .success candidates) :
    ∀ factor ∈ candidates.toList, P factor := by
  rw [bhksRecoverClassifiedCore] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows
    let indicators := bhksEquivalenceClassIndicators projected
    by_cases hdeg : bhksDegenerateIndicatorPartition projected indicators = true
    · simp [projected, indicators, hdeg] at hrecover
    · simp only [projected, indicators, hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidatesCore? f d indicators with
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

private theorem bhksRecoverClassifiedCore_success_normalizeFactorSign
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (h : bhksRecoverClassifiedCore f d = .success candidates) :
    ∀ factor ∈ candidates.toList, normalizeFactorSign factor = factor :=
  bhksRecoverClassifiedCore_success_all_of_candidates
    (fun factor => normalizeFactorSign factor = factor)
    (fun hcand => bhksIndicatorCandidatesCore?_normalizeFactorSign hcand) h

private theorem bhksRecoverClassifiedCore_success_shouldRecord
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (h : bhksRecoverClassifiedCore f d = .success candidates) :
    ∀ factor ∈ candidates.toList, shouldRecordPolynomialFactor factor = true :=
  bhksRecoverClassifiedCore_success_all_of_candidates
    (fun factor => shouldRecordPolynomialFactor factor = true)
    (fun hcand => bhksIndicatorCandidatesCore?_shouldRecord hcand) h

/-- A successful Core recovery emits only candidates that divide `f`, since each
candidate has passed the executable exact-division check inside
`bhksIndicatorCandidateCore?`.  The dependence of the conclusion on `f` prevents
a one-liner via `bhksRecoverClassifiedCore_success_all_of_candidates`, so we
unfold `bhksRecoverClassifiedCore` directly. -/
private theorem bhksRecoverClassifiedCore_success_dvd
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassifiedCore f d = .success candidates) :
    ∀ factor ∈ candidates.toList, factor ∣ f := by
  rw [bhksRecoverClassifiedCore] at hrecover
  by_cases hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth
  · rw [dif_pos hrows] at hrecover
    let projected :=
      bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows
    let indicators := bhksEquivalenceClassIndicators projected
    by_cases hdeg : bhksDegenerateIndicatorPartition projected indicators = true
    · simp [projected, indicators, hdeg] at hrecover
    · simp only [projected, indicators, hdeg, Bool.false_eq_true, if_false] at hrecover
      cases hcand : bhksIndicatorCandidatesCore? f d indicators with
      | none => simp [projected, indicators, hcand] at hrecover
      | some cands =>
          simp only [projected, indicators, hcand] at hrecover
          by_cases hprod : Array.polyProduct cands == f
          · simp only [hprod, if_true] at hrecover
            cases hrecover
            exact bhksIndicatorCandidatesCore?_dvd hcand
          · simp [hprod] at hrecover
  · rw [dif_neg hrows] at hrecover
    simp at hrecover

/-- A successful Core classified recovery exposes the underlying
indicator-candidate reconstruction: there is a positive-dimension witness
`hrows` for which the equivalence-class indicator candidates reconstruct exactly
to `candidates`, and the chosen indicator partition is non-degenerate.  The
Core-coordinate analogue of `bhksRecoverClassified_success_indicatorCandidates`. -/
private theorem bhksRecoverClassifiedCore_success_indicatorCandidates
    {f : ZPoly} {d : LiftData} {candidates : Array ZPoly}
    (hrecover : bhksRecoverClassifiedCore f d = .success candidates) :
    ∃ hrows : 1 ≤ (bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
        (bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth,
      bhksIndicatorCandidatesCore? f d
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
        some candidates ∧
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows (bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
        false := by
  rw [bhksRecoverClassifiedCore] at hrecover
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
      cases hcand : bhksIndicatorCandidatesCore? f d
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
        ∃ k', bhksRecoverClassified core (ZPoly.toMonicLiftData core k' primeData) =
          .success coreFactors ∧ bhksRecoveryFloor core ≤ k' := by
  intro k fuel
  induction fuel generalizing k with
  | zero =>
      intro coreFactors hfast
      simp [bhksRecoveryCoreWithBound, bhksRecoveryLoop] at hfast
  | succ fuel ih =>
      intro coreFactors hfast
      rw [bhksRecoveryCoreWithBound_unfold] at hfast
      cases hclass : bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
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
multiply back to `core`. This is the bridge-side entry point used to rebuild the
forward-recovery package (and hence the selected support/subset witnesses) that
the per-factor success lemmas discard. -/
theorem bhksRecoveryCoreWithBound_some_indicatorCandidates
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    ∃ k',
      ∃ hrows :
        1 ≤ (bhksLatticeBasis (ZPoly.toMonic core).monic
              (ZPoly.toMonicLiftData core k' primeData).p
              (ZPoly.toMonicLiftData core k' primeData).k
              (ZPoly.toMonicLiftData core k' primeData).liftedFactors).factorCount +
            (bhksLatticeBasis (ZPoly.toMonic core).monic
              (ZPoly.toMonicLiftData core k' primeData).p
              (ZPoly.toMonicLiftData core k' primeData).k
              (ZPoly.toMonicLiftData core k' primeData).liftedFactors).coeffWidth,
      bhksIndicatorCandidates? core (ZPoly.toMonicLiftData core k' primeData)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis (ZPoly.toMonic core).monic
                (ZPoly.toMonicLiftData core k' primeData).p
                (ZPoly.toMonicLiftData core k' primeData).k
                (ZPoly.toMonicLiftData core k' primeData).liftedFactors)
              hrows)) =
        some coreFactors ∧
      bhksDegenerateIndicatorPartition
          (bhksProjectedRows
            (bhksLatticeBasis (ZPoly.toMonic core).monic
              (ZPoly.toMonicLiftData core k' primeData).p
              (ZPoly.toMonicLiftData core k' primeData).k
              (ZPoly.toMonicLiftData core k' primeData).liftedFactors)
            hrows)
          (bhksEquivalenceClassIndicators
            (bhksProjectedRows
              (bhksLatticeBasis (ZPoly.toMonic core).monic
                (ZPoly.toMonicLiftData core k' primeData).p
                (ZPoly.toMonicLiftData core k' primeData).k
                (ZPoly.toMonicLiftData core k' primeData).liftedFactors)
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
      cases hclass : bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
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

theorem bhksRecoveryCoreWithBound_some_normalizeFactorSign
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, normalizeFactorSign factor = factor :=
  bhksRecoveryCoreWithBound_some_all_of_recovery
    (fun factor => normalizeFactorSign factor = factor)
    (fun hrecover => bhksRecoverClassified_success_normalizeFactorSign hrecover)
    core B primeData k fuel coreFactors h

theorem bhksRecoveryCoreWithBound_some_shouldRecord
    {core : ZPoly} {B : Nat} {primeData : PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array ZPoly}
    (h : bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    ∀ factor ∈ coreFactors.toList, shouldRecordPolynomialFactor factor = true :=
  bhksRecoveryCoreWithBound_some_all_of_recovery
    (fun factor => shouldRecordPolynomialFactor factor = true)
    (fun hrecover => bhksRecoverClassified_success_shouldRecord hrecover)
    core B primeData k fuel coreFactors h

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
input core. The success branch is the only branch that exits with
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
      cases hclass : bhksRecoverClassified core (ZPoly.toMonicLiftData core k primeData) with
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
monicness of emitted core factors from monicness of the squarefree core. -/
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

/-- Structural case-split for the size-ordered classical recombination core.
Every `some cf` result of `classicalCoreFactorsWithBound` is either the
short-circuit singleton `#[core]` (the `B = 0`, budget-`none`, and empty-result
arms all return `#[core]`) or the array of a nonempty recombination result, in
which case the product reconstructs `core` and each factor is
`normalizeFactorSign`-fixed, primitive, and recorded. The trio
`classicalCoreFactorsWithBound_{polyProduct,normalizeFactorSign,degree_pos}`
below are thin consumers, mirroring the exhaustive-tier structural trio. -/
private theorem classicalCoreFactorsWithBound_spec
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {cf : Array ZPoly}
    (h : classicalCoreFactorsWithBound core B primeData = some cf) :
    cf = #[core] ∨
      (Array.polyProduct cf = core ∧
        (∀ g ∈ cf.toList, normalizeFactorSign g = g) ∧
        (∀ g ∈ cf.toList, ZPoly.Primitive g) ∧
        (∀ g ∈ cf.toList, shouldRecordPolynomialFactor g = true)) := by
  by_cases hB : B = 0
  · left
    rw [classicalCoreFactorsWithBound, if_pos hB] at h
    exact (Option.some.inj h).symm
  · rw [classicalCoreFactorsWithBound, if_neg hB] at h
    simp only [scaledRecombinationSmart] at h
    generalize hld : ZPoly.toMonicLiftData core (ZPoly.exhaustiveLiftBound core B) primeData
      = liftData at h
    cases haux : scaledRecombinationSmartAux (DensePoly.leadingCoeff core) core
        (liftModulus liftData) liftData.liftedFactors.toList
        (levelAwareSubsetBudget liftData.liftedFactors.toList.length defaultSubsetBudget)
        (levelAwareSubsetBudget liftData.liftedFactors.toList.length defaultSubsetBudget +
          (liftData.liftedFactors.toList.length + 1) *
          (2 * liftData.liftedFactors.toList.length + 3)) with
    | mk res remaining =>
      rw [haux] at h
      cases res with
      | none =>
        left
        by_cases hrem : remaining = 0
        · subst hrem; simp at h
        · simp only [Option.isNone_none, Bool.true_and] at h
          rw [if_neg (by simp [hrem])] at h
          exact (Option.some.inj h).symm
      | some factors =>
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, if_false] at h
        by_cases hemp : factors.isEmpty = true
        · left
          rw [if_pos hemp] at h
          exact (Option.some.inj h).symm
        · right
          rw [if_neg hemp] at h
          obtain rfl := (Option.some.inj h).symm
          refine ⟨scaledRecombinationSmartAux_product _ _ _ _ _ _ _ _ haux, ?_, ?_, ?_⟩
          · intro g hg
            rw [List.toList_toArray] at hg
            exact scaledRecombinationSmartAux_normalizeFactorSign _ _ _ _ _ _ _ _ haux g hg
          · intro g hg
            rw [List.toList_toArray] at hg
            exact scaledRecombinationSmartAux_primitive _ _ _ _ _ _ _ _ haux g hg
          · intro g hg
            rw [List.toList_toArray] at hg
            exact scaledRecombinationSmartAux_shouldRecord _ _ _ _ _ _ _ _ haux g hg

/-- PolyProduct identity for the size-ordered classical recombination core:
every emitted factor array multiplies back to `core`. Mirror of
`exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct`; the `B = 0`,
budget-`none`, and empty-result arms return the singleton `#[core]` (product
`core`), and the nonempty recombination arm reuses
`scaledRecombinationSmartAux_product`. -/
theorem classicalCoreFactorsWithBound_polyProduct
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {cf : Array ZPoly}
    (h : classicalCoreFactorsWithBound core B primeData = some cf) :
    Array.polyProduct cf = core := by
  rcases classicalCoreFactorsWithBound_spec core B primeData h with hsing | ⟨hprod, _⟩
  · rw [hsing]; exact ZPoly.polyProduct_singleton core
  · exact hprod

/-- Each factor emitted by the size-ordered classical recombination core is
fixed by `normalizeFactorSign`, provided `core` has positive leading
coefficient. Mirror of
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign`: the smart
candidates are `normalizeFactorSign …` by construction (so fixed), and the
singleton short-circuit is `core`, fixed by its positive leading coefficient. -/
theorem classicalCoreFactorsWithBound_normalizeFactorSign
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    {cf : Array ZPoly}
    (h : classicalCoreFactorsWithBound core B primeData = some cf) :
    ∀ factor ∈ cf.toList, normalizeFactorSign factor = factor := by
  rcases classicalCoreFactorsWithBound_spec core B primeData h with hsing | ⟨_, hnorm, _⟩
  · intro factor hmem
    rw [hsing] at hmem
    have hfactor : factor = core := by simpa using hmem
    rw [hfactor]
    exact normalizeFactorSign_eq_self_of_leadingCoeff_nonneg core (by omega)
  · exact hnorm

end Hex
