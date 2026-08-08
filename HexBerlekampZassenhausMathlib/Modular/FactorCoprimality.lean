/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Modular.FactorProduct
import all HexBerlekampZassenhausMathlib.ModularPolynomial
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate

public section
set_option backward.proofsInPublic true

/-!
Coprimality and irreducibility of the modular factor family.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- The Berlekamp factor product is multiplicative over list concatenation.
Local restatement of the (private) `Hex.Berlekamp.factorProduct_append`, needed
to relate the balanced-split halves `L`, `R` back to the whole list. -/
private theorem factorProduct_append
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    (xs ys : List (Hex.FpPoly p)) :
    Hex.Berlekamp.factorProduct (xs ++ ys) =
      Hex.Berlekamp.factorProduct xs * Hex.Berlekamp.factorProduct ys := by
  induction xs with
  | nil =>
      rw [List.nil_append, Hex.Berlekamp.factorProduct_nil, Hex.FpPoly.one_mul]
  | cons x rest ih =>
      rw [List.cons_append, Hex.Berlekamp.factorProduct_cons,
        Hex.Berlekamp.factorProduct_cons, ih]
      exact (Hex.DensePoly.mul_assoc_poly x _ _).symm

/-- Generalized inductive helper for the `factorsModP_coprime` discharger.

For any list of factors in `FpPoly p` whose `factorProduct` divides a
nonzero polynomial `X` with no positive-degree squared divisor, the
recursive predicate `Hex.ZPoly.QuadraticMultifactorCoprimeSplits` holds.

The recursion follows the guarded product tree: at each non-singleton node the
list splits into `L := take split` and `R := drop split`, using the same
`balancedSplitIndex` as the executable, and
* `xgcd.gcd = 1` follows from the coprime view of `factorProduct L` against
  `factorProduct R`, identified via `modP_polyProduct_liftToZ_eq_factorProduct`:
  their `DensePoly.gcd` squares into `factorProduct (L ++ R) = factorProduct xs`,
  hence into `X`, so the no-squared invariant forces it constant;
* each side satisfies the same divisibility-into-`X` invariant via
  `factorProduct L ∣ factorProduct xs ∣ X` (and symmetrically for `R`),
  using `factorProduct_append`. -/
theorem quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    [Lean.Grind.Field (Hex.ZMod64 p)]
    (X : Hex.FpPoly p)
    (hX_ne : X ≠ 0)
    (h_no_squared : ∀ d : Hex.FpPoly p,
        d * d ∣ X → ¬ (0 < d.degree?.getD 0))
    (xs : List (Hex.FpPoly p))
    (h_dvd : Hex.Berlekamp.factorProduct xs ∣ X) :
    Hex.ZPoly.QuadraticMultifactorCoprimeSplits p xs := by
  revert h_dvd
  induction xs using Hex.ZPoly.QuadraticMultifactorCoprimeSplits.induct (p := p) with
  | case1 => intro _; simp only [Hex.ZPoly.QuadraticMultifactorCoprimeSplits]
  | case2 _g => intro _; simp only [Hex.ZPoly.QuadraticMultifactorCoprimeSplits]
  | case3 g₀ g₁ rest gs split L R ihL ihR =>
      intro h_dvd
      -- Balanced split of `g₀ :: g₁ :: rest` into `L ++ R` (the induct binders).
      have happend : L ++ R = g₀ :: g₁ :: rest := List.take_append_drop split gs
      have hfp_split :
          Hex.Berlekamp.factorProduct (g₀ :: g₁ :: rest) =
            Hex.Berlekamp.factorProduct L * Hex.Berlekamp.factorProduct R := by
        conv_lhs => rw [← happend]
        rw [factorProduct_append]
      -- Each half's product divides `factorProduct (g₀ :: g₁ :: rest)`, hence `X`.
      have hprod_dvd_X :
          Hex.Berlekamp.factorProduct L * Hex.Berlekamp.factorProduct R ∣ X := by
        rw [← hfp_split]; exact h_dvd
      have hL_dvd_X : Hex.Berlekamp.factorProduct L ∣ X :=
        fpPoly_dvd_trans ⟨Hex.Berlekamp.factorProduct R, hfp_split⟩ h_dvd
      have hR_dvd_X : Hex.Berlekamp.factorProduct R ∣ X :=
        fpPoly_dvd_trans
          ⟨Hex.Berlekamp.factorProduct L,
            by rw [hfp_split]; exact Hex.DensePoly.mul_comm_poly _ _⟩
          h_dvd
      -- Both `modP`-arguments of the split reduce to `factorProduct` shape.
      have hmodP_L :
          Hex.ZPoly.modP p (Array.polyProduct ((L.map Hex.FpPoly.liftToZ).toArray)) =
            Hex.Berlekamp.factorProduct L :=
        modP_polyProduct_liftToZ_eq_factorProduct L
      have hmodP_R :
          Hex.ZPoly.modP p (Array.polyProduct ((R.map Hex.FpPoly.liftToZ).toArray)) =
            Hex.Berlekamp.factorProduct R :=
        modP_polyProduct_liftToZ_eq_factorProduct R
      -- The split gcd is `1`: proved for abstract `a`, `b` reducing mod `p` to
      -- `factorProduct L`, `factorProduct R`, so `exact` matches by defeq.
      have hgcd :
          ∀ a b : Hex.ZPoly,
            Hex.ZPoly.modP p a = Hex.Berlekamp.factorProduct L →
            Hex.ZPoly.modP p b = Hex.Berlekamp.factorProduct R →
            (Hex.ZPoly.normalizedXGCD p a b).gcd = (1 : Hex.FpPoly p) := by
        intro a b hma hmb
        -- The raw EEA gcd is `DensePoly.gcd (factorProduct L) (factorProduct R)`.
        set rawGcd : Hex.FpPoly p :=
          Hex.DensePoly.gcd (Hex.Berlekamp.factorProduct L) (Hex.Berlekamp.factorProduct R)
          with hrawGcd_def
        -- `normalizedXGCD.gcd = scale (lc⁻¹) rawGcd`.
        have hnorm_def :
            (Hex.ZPoly.normalizedXGCD p a b).gcd =
              Hex.DensePoly.scale
                (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ rawGcd := by
          show Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.DensePoly.xgcd
                  (Hex.ZPoly.modP p a) (Hex.ZPoly.modP p b)).gcd)⁻¹
              (Hex.DensePoly.xgcd
                (Hex.ZPoly.modP p a) (Hex.ZPoly.modP p b)).gcd =
            Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ rawGcd
          rw [hma, hmb, hrawGcd_def, Hex.DensePoly.gcd_eq_xgcd_gcd]
        rw [hnorm_def]
        -- The rest: show `scale (lc rawGcd)⁻¹ rawGcd = 1`.  This needs
        -- `rawGcd` to be a nonzero constant in `FpPoly p`.
        -- Step 1: `rawGcd² ∣ X`.
        have hrawGcd_dvd_L : rawGcd ∣ Hex.Berlekamp.factorProduct L :=
          Hex.DensePoly.gcd_dvd_left _ _
        have hrawGcd_dvd_R : rawGcd ∣ Hex.Berlekamp.factorProduct R :=
          Hex.DensePoly.gcd_dvd_right _ _
        have hrawGcd_sq_dvd_prod :
            rawGcd * rawGcd ∣
              Hex.Berlekamp.factorProduct L * Hex.Berlekamp.factorProduct R :=
          fpPoly_mul_dvd_mul hrawGcd_dvd_L hrawGcd_dvd_R
        have hrawGcd_sq_dvd_X : rawGcd * rawGcd ∣ X :=
          fpPoly_dvd_trans hrawGcd_sq_dvd_prod hprod_dvd_X
        -- Step 2: rawGcd has degree ≤ 0 by no-squared on X.
        have hrawGcd_not_pos :
            ¬ (0 < rawGcd.degree?.getD 0) :=
          h_no_squared rawGcd hrawGcd_sq_dvd_X
        -- Step 3: rawGcd ≠ 0 (via `rawGcd * rawGcd ∣ X` with `X ≠ 0`).
        have hrawGcd_ne : rawGcd ≠ 0 := by
          intro hraw
          apply hX_ne
          rcases hrawGcd_sq_dvd_X with ⟨k, hk⟩
          rw [hraw, Hex.FpPoly.zero_mul, Hex.FpPoly.zero_mul] at hk
          exact hk
        -- Step 4: rawGcd.size = 1.
        have hrawGcd_size_pos : 0 < rawGcd.size := by
          apply Nat.pos_of_ne_zero
          intro hsize
          apply hrawGcd_ne
          apply Hex.DensePoly.ext_coeff
          intro i
          rw [Hex.DensePoly.coeff_zero]
          exact Hex.DensePoly.coeff_eq_zero_of_size_le rawGcd (by omega)
        have hrawGcd_size_one : rawGcd.size = 1 := by
          by_contra hsize_ne
          apply hrawGcd_not_pos
          have hsize_ge_two : 2 ≤ rawGcd.size := by omega
          have hdeg_form : rawGcd.degree? = some (rawGcd.size - 1) := by
            unfold Hex.DensePoly.degree?
            have hne : rawGcd.size ≠ 0 := Nat.pos_iff_ne_zero.mp hrawGcd_size_pos
            simp [hne]
          rw [hdeg_form]; simp; omega
        -- Step 5: lc rawGcd ≠ 0.
        have hlc_ne :
            Hex.DensePoly.leadingCoeff rawGcd ≠ (0 : Hex.ZMod64 p) :=
          fpPoly_leadingCoeff_ne_zero_of_size_pos rawGcd hrawGcd_size_pos
        -- Step 6: rawGcd.coeff 0 = lc rawGcd.
        have hrawGcd_coeff_zero :
            rawGcd.coeff 0 = Hex.DensePoly.leadingCoeff rawGcd := by
          rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred rawGcd hrawGcd_size_pos]
          congr 1; omega
        -- Step 7: scale lc⁻¹ rawGcd = 1.
        apply Hex.DensePoly.ext_coeff
        intro n
        have hzero_mul :
            (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ * (0 : Hex.ZMod64 p) = 0 :=
          Lean.Grind.Semiring.mul_zero _
        rw [Hex.DensePoly.coeff_scale
          (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ rawGcd n hzero_mul]
        change (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ * rawGcd.coeff n =
          (Hex.DensePoly.C (1 : Hex.ZMod64 p)).coeff n
        rw [Hex.DensePoly.coeff_C]
        cases n with
        | zero =>
            rw [hrawGcd_coeff_zero]
            simp
            exact Hex.ZMod64.inv_mul_eq_one_of_prime
              (Hex.ZMod64.PrimeModulus.prime (p := p)) hlc_ne
        | succ k =>
            have hcoeff_zero : rawGcd.coeff (k + 1) = (0 : Hex.ZMod64 p) :=
              Hex.DensePoly.coeff_eq_zero_of_size_le rawGcd (by omega)
            rw [hcoeff_zero, if_neg (Nat.succ_ne_zero k)]
            exact hzero_mul
      rw [Hex.ZPoly.QuadraticMultifactorCoprimeSplits]
      exact ⟨hgcd _ _ hmodP_L hmodP_R, ihL hL_dvd_X, ihR hR_dvd_X⟩

/-- Discharge of the coprime-splits boundary premise on
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData`: given the
`factorsModPBerlekampForm` invariant (which records that `primeData.factorsModP`
is the Berlekamp factor array of the monic modular image of the input)
together with a successful `isGoodPrime` check, the recursive balanced-split
coprime predicate `QuadraticMultifactorCoprimeSplits` holds on the stored
factor list.

Proof: extract the Berlekamp witnesses from `hform`; transport modular
squarefreeness from `isGoodPrime` through `monicModularImage`; apply the
generalized `quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared`
helper with `X := monicModularImage (modP p core)` to walk the list.  The
no-squared invariant on the modular image is the local Mathlib-side form
of `gcd_monicModularImage_derivative_isUnit_local`, instantiated through
`Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd`.

This is the third in the chain of `factorsModP`-side dischargers
(`factorsModP_nodup_of_factorsModPBerlekampForm`,
`factorsModP_natDegree_pos_of_factorsModPBerlekampForm`, this one), each
mapping the abstract `factorsModPBerlekampForm` invariant plus an
`isGoodPrime` certificate to a piece of the four-tuple
`(hfactors_monic, hproduct_mod_p, hcoprime, hnonempty)` that the umbrella
`QuadraticMultifactorLiftInvariant_of_choosePrimeData` consumes.

The Option-3 wrap of `berlekampFactorsModP` (apply `monicModularImage` per
factor) lifts the helper application from the raw Berlekamp factor list to
the mapped list via the multiplicativity lemma
`factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct`. -/
theorem factorsModP_coprime_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true) :
    letI := primeData.bounds
    Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
      primeData.factorsModP.toList := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  -- The modular image is square-free under `isGoodPrime`.
  have hsf_common :
      ∀ d : Hex.FpPoly primeData.p,
        d ∣ Hex.ZPoly.modP primeData.p core →
        d ∣ Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core) →
        Hex.Berlekamp.isUnitPolynomial d = true :=
    squareFree_common_of_squareFreeModP core
      (Hex.isGoodPrime_squareFreeModP core primeData.p hgood)
  -- `monicModularImage` divides `modP p core`, so the no-squared invariant
  -- transports through the unit scaling.
  have hmonicImage_dvd :
      Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) ∣
        Hex.ZPoly.modP primeData.p core :=
    monicModularImage_dvd_self_of_isZero_false hprime hzero
  -- The no-squared invariant on the monic modular image.
  have h_no_squared :
      ∀ d : Hex.FpPoly primeData.p,
        d * d ∣ Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) →
          ¬ (0 < d.degree?.getD 0) := by
    intro d hdd hpos
    have hd_dvd_mod : d * d ∣ Hex.ZPoly.modP primeData.p core :=
      fpPoly_dvd_trans hdd hmonicImage_dvd
    have hunit : Hex.Berlekamp.isUnitPolynomial d = true :=
      Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd hsf_common
        hd_dvd_mod
    have hdeg : Hex.DensePoly.degree? d = some 0 := by
      unfold Hex.Berlekamp.isUnitPolynomial at hunit
      cases hd : Hex.DensePoly.degree? d with
      | none => rw [hd] at hunit; simp at hunit
      | some k =>
          rw [hd] at hunit
          cases k with
          | zero => rfl
          | succ _ => simp at hunit
    rw [hdeg] at hpos
    simp at hpos
  -- Monic image is monic (consumed by Berlekamp's signature and idempotence).
  have hmonicImage_monic :
      Hex.DensePoly.Monic (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  -- Raw Berlekamp factor list: under the Option-3 wrap, `primeData.factorsModP`
  -- is `raw.map monicModularImage` (then `.toArray`), so the helper must be
  -- applied at the mapped list.
  let raw :=
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        hmonicImage_monic hfield).factors
  -- The Berlekamp factor list has product equal to the monic modular image.
  have h_factorProduct :
      Hex.Berlekamp.factorProduct raw =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) :=
    Hex.Berlekamp.factorProduct_berlekampFactor _ _
  -- Monic modular image is nonzero (it's a nonzero scalar of a nonzero poly).
  have hmonicImage_ne :
      Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) ≠ 0 := by
    apply Hex.monicModularImage_ne_zero_of_ne_zero hprime
    intro hmod_zero
    rw [hmod_zero] at hzero
    have hzero_true : (0 : Hex.FpPoly primeData.p).isZero = true := rfl
    rw [hzero_true] at hzero
    exact Bool.noConfusion hzero
  -- Each raw Berlekamp factor is nonzero (positive degree typically, singleton
  -- [monicImg] in the degenerate size-≤-1 case).
  have hraw_ne : ∀ g ∈ raw, g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic
  -- Push `monicModularImage` through `factorProduct`: the mapped product
  -- equals `monicModularImage (factorProduct raw) = monicModularImage (monicImg)
  -- = monicImg` (the last step uses that `monicImg` is already monic).
  have hprod_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [Hex.factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct
        hprime raw hraw_ne]
    rw [h_factorProduct]
    exact Hex.monicModularImage_eq_self_of_monic hprime _ hmonicImage_monic
  -- Apply the generalized helper at the mapped list.
  have h_dvd_X_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) ∣
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [hprod_mapped]
    exact Hex.DensePoly.dvd_refl_poly _
  have hcps :
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        (raw.map Hex.monicModularImage) :=
    quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_ne h_no_squared _ h_dvd_X_mapped
  -- Transport to the `factorsModP.toList` view.
  rw [heq]
  simpa using hcps

/-- Discharge of the per-modular-factor monicness premise on
`henselLiftData_liftedFactor_monic_of_choosePrimeData` (and the two other
umbrellas at lines 5136 and 5200) from the `factorsModPBerlekampForm` invariant
alone.

`primeData.factorsModP` is, under the Option-3 wrap in `berlekampFactorsModP`,
exactly `((berlekampFactor monicImg).factors.map monicModularImage).toArray`.
Every entry is therefore the `monicModularImage` of some raw Berlekamp factor,
which is monic by `monicModularImage_monic` provided the raw factor is nonzero.
The raw-factor nonzeroness is `berlekampFactor_factors_ne_zero` (positive-degree
case via `berlekampFactor_factors_pos_degree`, degenerate `[monicImg]` case
because `monicImg` is monic).

No `hgood` or `hcore_monic` premise is needed: the discharge follows from the
shape of `factorsModPBerlekampForm` and Berlekamp-output structural facts
alone.  This is the fourth and last of the
`QuadraticMultifactorLiftInvariant` boundary dischargers (together with
`factorsModP_ne_nil_*`, `factorsModP_polyProduct_congr_*`, and
`factorsModP_coprime_*`) that the umbrellas consume via
`QuadraticMultifactorLiftInvariant_of_choosePrimeData`. -/
theorem factorsModP_monic_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData) :
    letI := primeData.bounds
    ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hmonicImage_monic :
      Hex.DensePoly.Monic (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  -- Each entry of `factorsModP` is `monicModularImage g'` for some `g'` in the
  -- raw Berlekamp output, and each such `g'` is nonzero.
  intro g hg
  rw [heq] at hg
  rw [List.mem_toArray, List.mem_map] at hg
  obtain ⟨g', hg'_mem, hg'_eq⟩ := hg
  have hg'_ne : g' ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic g' hg'_mem
  rw [← hg'_eq]
  exact Hex.monicModularImage_monic hprime g' (Hex.isZero_false_of_ne_zero hg'_ne)

/- Square-freeness of a nonzero `FpPoly` transfers to its monic representative.

Local copy of the IntReductionMod helper of the same name (the canonical
version lives at `HexBerlekampZassenhausMathlib/IntReductionMod.lean:307`).
Duplicated here because `IntReductionMod` imports `Basic`; the proof routes
through `IsCoprime` in `Polynomial (ZMod p)` using
`toMathlibPolynomial_squareFree_coprime` and the `toMathlibPolynomial_scale`
identification for the unit scalar `(leadingCoeff f)⁻¹`. -/
/-- A transported executable polynomial that transports to a unit has executable
size one, hence passes the `gcdIsUnit` size check when used as a gcd. -/
private theorem size_eq_one_of_toMathlibPolynomial_isUnit_local
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    {g : Hex.FpPoly p}
    (h : IsUnit (HexBerlekampMathlib.toMathlibPolynomial g)) :
    g.size = 1 := by
  rcases Nat.lt_or_ge g.size 1 with hlt | hge
  · exfalso
    have hsize_zero : g.size = 0 := by omega
    have hzero : HexBerlekampMathlib.toMathlibPolynomial g = 0 := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_zero, HexBerlekampMathlib.coeff_toMathlibPolynomial,
        Hex.DensePoly.coeff_eq_zero_of_size_le _ (show g.size ≤ n by omega)]
      exact HexModArithMathlib.ZMod64.toZMod_zero
    exact not_isUnit_zero (hzero ▸ h)
  · by_contra hne
    have hpos : 0 < g.size := by omega
    have hge2 : 2 ≤ g.size := by omega
    have hcoeff_ne : g.coeff (g.size - 1) ≠ 0 :=
      Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hpos
    have hcoeff_zmod_ne :
        HexModArithMathlib.ZMod64.toZMod (g.coeff (g.size - 1)) ≠ 0 := by
      intro hzero
      apply hcoeff_ne
      have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
      apply hinj
      simpa using hzero.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
    have hcoeff_poly_ne :
        (HexBerlekampMathlib.toMathlibPolynomial g).coeff (g.size - 1) ≠ 0 := by
      rw [HexBerlekampMathlib.coeff_toMathlibPolynomial]
      exact hcoeff_zmod_ne
    have hpos_natDeg :
        0 < (HexBerlekampMathlib.toMathlibPolynomial g).natDegree := by
      have hle := Polynomial.le_natDegree_of_ne_zero hcoeff_poly_ne
      omega
    exact Polynomial.not_isUnit_of_natDegree_pos _ hpos_natDeg h

/-- The Zassenhaus `gcdIsUnit` size check implies Berlekamp's nonzero-constant
unit-polynomial predicate. -/
private theorem isUnitPolynomial_of_gcdIsUnit_local
    {p : Nat} [Hex.ZMod64.Bounds p] {g : Hex.FpPoly p}
    (h : Hex.gcdIsUnit g = true) :
    Hex.Berlekamp.isUnitPolynomial g = true := by
  unfold Hex.gcdIsUnit at h
  change (g.size == 1) = true at h
  have hsize : g.size = 1 := beq_iff_eq.mp h
  unfold Hex.Berlekamp.isUnitPolynomial
  have hpos : 0 < g.size := by omega
  rw [Hex.DensePoly.degree?_eq_some_of_pos_size g hpos, hsize]
  rfl

private theorem gcd_monicModularImage_derivative_isUnit_local
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p) (hzero : f.isZero = false)
    (hsquareFree :
      Hex.gcdIsUnit (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = true) :
    Hex.gcdIsUnit
      (Hex.DensePoly.gcd (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f))) = true := by
  let u : Hex.ZMod64 p := (Hex.DensePoly.leadingCoeff f)⁻¹
  have hmonic_eq : Hex.monicModularImage f = Hex.DensePoly.scale u f := by
    simpa [u] using
      monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hzero
  have hcop :
      IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))) := by
    have hcop_f :
        IsCoprime
          (HexBerlekampMathlib.toMathlibPolynomial f)
          (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f)) :=
      HexBerlekampMathlib.toMathlibPolynomial_squareFree_coprime f
        (isUnitPolynomial_of_gcdIsUnit_local hsquareFree)
    have hu_ne : HexModArithMathlib.ZMod64.toZMod u ≠ 0 := by
      have hp_hex : Hex.Nat.Prime p := by
        constructor
        · exact (Fact.out : Nat.Prime p).two_le
        · intro m hmdvd
          rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmdvd with h | h
          · exact Or.inl h
          · exact Or.inr h
      have hlead_ne : Hex.DensePoly.leadingCoeff f ≠ 0 :=
        fpPoly_leadingCoeff_ne_zero_of_size_pos f
          ((Hex.DensePoly.isZero_eq_false_iff _).mp hzero)
      intro hu_zero
      have hone_hex : u * Hex.DensePoly.leadingCoeff f = (1 : Hex.ZMod64 p) := by
        show (Hex.DensePoly.leadingCoeff f)⁻¹ * Hex.DensePoly.leadingCoeff f = (1 : Hex.ZMod64 p)
        exact Hex.ZMod64.inv_mul_eq_one_of_prime hp_hex hlead_ne
      have hone_z :
          HexModArithMathlib.ZMod64.toZMod u *
              HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff f) =
            (1 : ZMod p) := by
        rw [← HexModArithMathlib.ZMod64.toZMod_mul, hone_hex,
          HexModArithMathlib.ZMod64.toZMod_one]
      rw [hu_zero, zero_mul] at hone_z
      exact zero_ne_one hone_z
    have hC_unit :
        IsUnit (Polynomial.C (HexModArithMathlib.ZMod64.toZMod u)) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu_ne)
    rw [hmonic_eq, toMathlibPolynomial_scale, Polynomial.derivative_C_mul]
    exact (isCoprime_mul_unit_left hC_unit
      (HexBerlekampMathlib.toMathlibPolynomial f)
      (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f))).mpr hcop_f
  let g : Hex.FpPoly p :=
    Hex.DensePoly.gcd (Hex.monicModularImage f)
      (Hex.DensePoly.derivative (Hex.monicModularImage f))
  have hunit_math :
      IsUnit
        (gcd
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
          (Polynomial.derivative
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) :=
    gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
  have hunit_transport :
      IsUnit (HexBerlekampMathlib.toMathlibPolynomial g) := by
    rw [← HexBerlekampMathlib.toMathlibPolynomial_derivative] at hunit_math
    exact
      (HexBerlekampMathlib.toMathlibPolynomial_gcd_associated
        (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f))).symm.isUnit
        hunit_math
  have hg_size : g.size = 1 :=
    size_eq_one_of_toMathlibPolynomial_isUnit_local hunit_transport
  unfold Hex.gcdIsUnit
  change (g.size == 1) = true
  exact beq_iff_eq.mpr hg_size

private theorem derivative_scale_local
    {p : Nat} [Hex.ZMod64.Bounds p]
    (c : Hex.ZMod64 p) (f : Hex.FpPoly p) :
    Hex.DensePoly.derivative (Hex.DensePoly.scale c f) =
      Hex.DensePoly.scale c (Hex.DensePoly.derivative f) := by
  apply Hex.DensePoly.ext_coeff
  intro n
  have hzero_d : ((n + 1 : Nat) : Hex.ZMod64 p) *
      (Zero.zero : Hex.ZMod64 p) = (Zero.zero : Hex.ZMod64 p) :=
    Lean.Grind.Semiring.mul_zero _
  have hzero_s : c * (Zero.zero : Hex.ZMod64 p) =
      (Zero.zero : Hex.ZMod64 p) :=
    Lean.Grind.Semiring.mul_zero _
  rw [Hex.DensePoly.coeff_derivative _ _ hzero_d,
      Hex.DensePoly.coeff_scale c (Hex.DensePoly.derivative f) n hzero_s,
      Hex.DensePoly.coeff_derivative _ _ hzero_d,
      Hex.DensePoly.coeff_scale c f (n + 1) hzero_s]
  grind

private theorem dvd_trans_FpPoly_local
    {p : Nat} [Hex.ZMod64.Bounds p] {a b c : Hex.FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc c
      = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := Hex.DensePoly.mul_assoc_poly a x y

/-- `factorsModPBerlekampForm`-shaped discharge for per-modular-factor
irreducibility after the Mathlib-side transport.

Given the `factorsModPBerlekampForm` invariant (recording that
`primeData.factorsModP` is the post-`monicModularImage` Berlekamp factor
array of the monic modular image of the input) together with a successful
`isGoodPrime` check (which certifies the modular image is square-free),
the transported Mathlib polynomial of every stored modular factor is
irreducible.

Proof: each entry of `primeData.factorsModP` is `monicModularImage g` for
some raw Berlekamp factor `g`.  `irreducible_of_mem_berlekampFactor` gives
`Irreducible (toMathlibPolynomial g)`.  The transfer to
`monicModularImage g` uses `toMathlibPolynomial_scale`: since
`monicModularImage g = scale (lc g)⁻¹ g`, the Mathlib image equals
`C ((lc g)⁻¹.toZMod) * toMathlibPolynomial g`, a unit multiple of the
original, and `Associated.irreducible` transfers the irreducibility.

The square-freeness premise of `irreducible_of_mem_berlekampFactor` is
discharged via `gcd_monicModularImage_derivative_isUnit_local` applied to
the modular square-freeness from `Hex.isGoodPrime_squareFreeModP`.

This is the per-index irreducibility component consumed by the
`ModPSubsetPartitionHypotheses` constructor.  The sibling existence /
uniqueness component is `existsUnique_modPFactorSubset_of_choosePrimeData`;
the constructor wrapper itself is
`modPSubsetPartitionHypotheses_of_choosePrimeData`. -/
theorem factors_irreducible_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true)
    (hcore_pos : 0 < core.degree?.getD 0) :
    ∀ i : ModPFactorIndex primeData,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hmonicImage_pos :
      0 < (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)).degree?.getD 0 :=
    monicModularImage_modP_degree?_pos_of_factorsModPBerlekampForm
      core primeData hform hgood hcore_pos
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime_root⟩
  have hsf_common :
      ∀ d : Hex.FpPoly primeData.p,
        d ∣ Hex.ZPoly.modP primeData.p core →
        d ∣ Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core) →
        Hex.Berlekamp.isUnitPolynomial d = true :=
    squareFree_common_of_squareFreeModP core
      (Hex.isGoodPrime_squareFreeModP core primeData.p hgood)
  have hsf_common_monic :
      ∀ d : Hex.FpPoly primeData.p,
        d ∣ Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) →
        d ∣ Hex.DensePoly.derivative
            (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) →
        Hex.Berlekamp.isUnitPolynomial d = true := by
    intro d hd_monic hd_deriv_monic
    let u : Hex.ZMod64 primeData.p :=
      (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹
    have hmmi_eq :
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) =
          Hex.DensePoly.scale u (Hex.ZPoly.modP primeData.p core) := by
      simpa [u] using
        monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hzero
    have hlead_ne : Hex.DensePoly.leadingCoeff
        (Hex.ZPoly.modP primeData.p core) ≠ 0 :=
      fpPoly_leadingCoeff_ne_zero_of_size_pos (Hex.ZPoly.modP primeData.p core)
        ((Hex.DensePoly.isZero_eq_false_iff _).mp hzero)
    have hu_ne : u ≠ 0 := by
      simpa [u] using Hex.ZMod64.inv_ne_zero_of_prime hprime hlead_ne
    rw [hmmi_eq] at hd_monic
    rw [hmmi_eq, derivative_scale_local] at hd_deriv_monic
    have hscale_dvd_mod :
        Hex.DensePoly.scale u (Hex.ZPoly.modP primeData.p core) ∣
          Hex.ZPoly.modP primeData.p core :=
      Hex.FpPoly.dvd_scale_self_of_ne_zero hu_ne (Hex.ZPoly.modP primeData.p core)
    have hscale_dvd_deriv :
        Hex.DensePoly.scale u
            (Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core)) ∣
          Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core) :=
      Hex.FpPoly.dvd_scale_self_of_ne_zero hu_ne
        (Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core))
    exact hsf_common d
      (dvd_trans_FpPoly_local hd_monic hscale_dvd_mod)
      (dvd_trans_FpPoly_local hd_deriv_monic hscale_dvd_deriv)
  have hmonicImage_monic :
      Hex.DensePoly.Monic
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  letI := hfield
  have hraw_irr :
      ∀ g ∈ (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
          hmonicImage_monic hfield).factors,
        Irreducible (HexBerlekampMathlib.toMathlibPolynomial g) :=
    HexBerlekampMathlib.irreducible_of_mem_berlekampFactor
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic hmonicImage_pos hsf_common_monic
  have hraw_ne :
      ∀ g ∈ (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
          hmonicImage_monic hfield).factors,
        g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic
  intro i
  have hi_mem : modPFactor primeData i ∈ primeData.factorsModP := by
    unfold modPFactor
    exact Array.getElem_mem i.isLt
  rw [heq] at hi_mem
  rw [List.mem_toArray, List.mem_map] at hi_mem
  obtain ⟨g', hg'_mem, hg'_eq⟩ := hi_mem
  have hirr_g' : Irreducible (HexBerlekampMathlib.toMathlibPolynomial g') :=
    hraw_irr g' hg'_mem
  have hg'_ne : g' ≠ 0 := hraw_ne g' hg'_mem
  have hg'_isZero : g'.isZero = false := Hex.isZero_false_of_ne_zero hg'_ne
  have hg'_size_pos : 0 < g'.size :=
    (Hex.DensePoly.isZero_eq_false_iff _).mp hg'_isZero
  have hg'_lead_ne :
      Hex.DensePoly.leadingCoeff g' ≠ (0 : Hex.ZMod64 primeData.p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos g' hg'_size_pos
  have hg'_inv_ne :
      (Hex.DensePoly.leadingCoeff g')⁻¹ ≠ (0 : Hex.ZMod64 primeData.p) := by
    intro hinv
    have hone := Hex.ZMod64.inv_mul_eq_one_of_prime hprime hg'_lead_ne
    have hinv' :
        Hex.ZMod64.inv (Hex.DensePoly.leadingCoeff g') =
          (0 : Hex.ZMod64 primeData.p) := hinv
    rw [hinv'] at hone
    have hzeromul :
        (0 : Hex.ZMod64 primeData.p) * Hex.DensePoly.leadingCoeff g' =
          (0 : Hex.ZMod64 primeData.p) :=
      Lean.Grind.Semiring.zero_mul _
    rw [hzeromul] at hone
    have h_one_ne_zero : (1 : Hex.ZMod64 primeData.p) ≠ 0 :=
      fun h => Hex.ZMod64.one_ne_zero_of_prime hprime h
    exact h_one_ne_zero hone.symm
  have hinv_zmod_ne :
      HexModArithMathlib.ZMod64.toZMod
        (Hex.DensePoly.leadingCoeff g')⁻¹ ≠ (0 : ZMod primeData.p) := by
    intro h
    apply hg'_inv_ne
    have hinj := (HexModArithMathlib.ZMod64.equiv (p := primeData.p)).injective
    apply hinj
    simpa using h.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
  have hC_unit :
      IsUnit (Polynomial.C
        (HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff g')⁻¹)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hinv_zmod_ne)
  have hmonic_eq :
      Hex.monicModularImage g' =
        Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g')⁻¹ g' :=
    monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hg'_isZero
  have hmath_eq :
      HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage g') =
        Polynomial.C
            (HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff g')⁻¹) *
          HexBerlekampMathlib.toMathlibPolynomial g' := by
    rw [hmonic_eq, toMathlibPolynomial_scale]
  have hassoc :
      Associated
        (HexBerlekampMathlib.toMathlibPolynomial g')
        (Polynomial.C
            (HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff g')⁻¹) *
          HexBerlekampMathlib.toMathlibPolynomial g') :=
    ((associated_isUnit_mul_left_iff hC_unit).mpr (Associated.refl _)).symm
  rw [← hg'_eq, hmath_eq]
  exact hassoc.irreducible hirr_g'

/-- Per-modular-factor irreducibility specialised to the
`Hex.choosePrimeData? core = some primeData` branch.

In this branch, the `factorsModPBerlekampForm` invariant and the `isGoodPrime`
hypothesis are both supplied automatically by
`Hex.choosePrimeData?_factorsModP_berlekamp_form` and
`Hex.choosePrimeData?_isGoodPrime` respectively; the `none` branch is
excluded by the explicit-witness premise `hselected`.  The constructor
wrapper will compose this with the sibling
`existsUnique_modPFactorSubset_of_choosePrimeData` and the
trivial `fModP_eq` / `admissible_prime` / `square_free_reduction` fields. -/
theorem factors_irreducible_of_choosePrimeData_of_some
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hcore_pos : 0 < core.degree?.getD 0) :
    ∀ i : ModPFactorIndex primeData,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hform : Hex.factorsModPBerlekampForm core primeData := by
    obtain ⟨hzero, hfactors_eq⟩ :=
      Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hselected
    exact ⟨Hex.choosePrimeData?_prime core primeData hselected, hzero, hfactors_eq⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  exact factors_irreducible_of_factorsModPBerlekampForm core primeData hform hgood hcore_pos
end

end HexBerlekampZassenhausMathlib
