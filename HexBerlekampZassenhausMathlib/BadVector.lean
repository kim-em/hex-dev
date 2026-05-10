import HexBerlekampZassenhaus.Basic
import HexBerlekampZassenhausMathlib.Resultant

/-!
Abstract resultant/divisibility layer for the BHKS bad-vector argument.

The executable CLD/lattice objects are deliberately absent from this module.
Later BHKS termination work can instantiate `BadVectorResultantData` with the
polynomial associated to a lattice vector, then use the packaged lower and
upper bounds without reopening the resultant API.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/--
Proof-facing data carried by the BHKS bad-vector route.

`f` is the input polynomial and `H` is the auxiliary polynomial extracted from
the bad vector.  The hypotheses say that the transported pair is coprime over
`ℚ` and that the modular construction forces a `p^(a*d)` divisibility of the
integer resultant.
-/
structure BadVectorResultantData where
  f : Polynomial ℤ
  H : Polynomial ℤ
  p : Nat
  a : Nat
  d : Nat
  p_pos : 0 < p
  d_pos : 0 < d
  coprime_over_rat :
    IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ))
  resultant_divisible :
    ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H

namespace BadVectorResultantData

/-- The integer resultant attached to bad-vector proof data. -/
def resultant (D : BadVectorResultantData) : ℤ :=
  Polynomial.resultant D.f D.H

/-- The modular lower-bound divisor attached to bad-vector proof data. -/
def divisor (D : BadVectorResultantData) : Nat :=
  D.p ^ (D.a * D.d)

theorem resultant_ne_zero (D : BadVectorResultantData) :
    D.resultant ≠ 0 := by
  exact int_resultant_ne_zero_of_coprime_over_rat D.f D.H D.coprime_over_rat

theorem divisor_pos (D : BadVectorResultantData) :
    0 < D.divisor := by
  exact pow_pos D.p_pos _

/--
The modular divisibility hypothesis gives the arithmetic lower bound on the
absolute value of the nonzero integer resultant.
-/
theorem divisor_le_resultant_natAbs (D : BadVectorResultantData) :
    D.divisor ≤ Int.natAbs D.resultant := by
  have hdiv : ((D.divisor : Nat) : ℤ) ∣ D.resultant := by
    simpa [divisor, resultant] using D.resultant_divisible
  have hnonzero : D.resultant ≠ 0 := D.resultant_ne_zero
  simpa [divisor] using Int.natAbs_le_of_dvd_ne_zero hdiv hnonzero

/--
Real-valued lower bound used when comparing the BHKS modular divisibility
against Hadamard's resultant upper bound.
-/
theorem divisor_real_le_abs_resultant (D : BadVectorResultantData) :
    (D.divisor : ℝ) ≤ |((D.resultant : ℤ) : ℝ)| := by
  have h : (D.divisor : ℝ) ≤ (Int.natAbs D.resultant : ℝ) := by
    exact_mod_cast D.divisor_le_resultant_natAbs
  simpa [Nat.cast_natAbs] using h

/-- Existing Sylvester/Hadamard bound specialized to bad-vector data. -/
theorem abs_resultant_le_l2norm_pow (D : BadVectorResultantData) :
    |((D.resultant : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
        (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree := by
  simpa [resultant] using
    HexBerlekampZassenhausMathlib.abs_resultant_le_l2norm_pow D.f D.H

/--
Combined BHKS bad-vector resultant comparison: the modular lower bound is at
most the Hadamard/l2norm upper bound.
-/
theorem divisor_real_le_l2norm_pow (D : BadVectorResultantData) :
    (D.divisor : ℝ) ≤
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
        (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree :=
  le_trans D.divisor_real_le_abs_resultant D.abs_resultant_le_l2norm_pow

/--
If the Hadamard/l2norm upper bound is strictly below the modular divisor, the
packaged bad-vector resultant data is contradictory.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor
    (D : BadVectorResultantData)
    (hlt :
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
          (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree <
        (D.divisor : ℝ)) :
    False :=
  (not_lt_of_ge D.divisor_real_le_l2norm_pow) hlt

/--
Parameter-style wrapper for later callers that do not want to construct the
record explicitly in theorem statements.
-/
theorem badVector_resultant_bounds
    (f H : Polynomial ℤ) (p a d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)))
    (hdiv : ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H) :
    (p ^ (a * d) : ℝ) ≤
      |((Polynomial.resultant f H : ℤ) : ℝ)| ∧
    |((Polynomial.resultant f H : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm f) ^ H.natDegree *
        (HexPolyZMathlib.l2norm H) ^ f.natDegree := by
  let D : BadVectorResultantData :=
    { f := f
      H := H
      p := p
      a := a
      d := d
      p_pos := hp
      d_pos := hd
      coprime_over_rat := hcoprime
      resultant_divisible := hdiv }
  exact ⟨by simpa [D, divisor, resultant] using D.divisor_real_le_abs_resultant,
    by simpa [D, resultant] using D.abs_resultant_le_l2norm_pow⟩

/--
Parameter-style contradiction wrapper for callers that have the raw bad-vector
resultant hypotheses rather than a `BadVectorResultantData` record.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor_params
    (f H : Polynomial ℤ) (p a d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)))
    (hdiv : ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H)
    (hlt :
      (HexPolyZMathlib.l2norm f) ^ H.natDegree *
          (HexPolyZMathlib.l2norm H) ^ f.natDegree <
        (p ^ (a * d) : ℝ)) :
    False := by
  let D : BadVectorResultantData :=
    { f := f
      H := H
      p := p
      a := a
      d := d
      p_pos := hp
      d_pos := hd
      coprime_over_rat := hcoprime
      resultant_divisible := hdiv }
  exact D.no_badVector_of_l2norm_upper_lt_divisor (by
    simpa [D, divisor] using hlt)

end BadVectorResultantData

/--
Proof-facing witness tying an executable BHKS bad vector back to the abstract
integer-resultant data used by the termination proof.

The executable fields name the original `ZPoly`, the Hensel lift data, the
all-coefficients CLD lattice, the projected `L'` rows, and the selected local
factor index/degree.  The auxiliary polynomial is stored as a `Hex.ZPoly`; the
Mathlib-facing polynomial used in resultants is `auxiliaryPolynomial`.
-/
structure ExecutableBadVectorWitness where
  input : Hex.ZPoly
  liftData : Hex.LiftData
  lattice : Hex.BhksLatticeBasis
  projectedRows : Hex.BhksProjectedRows
  localFactorIndex : Nat
  localFactorDegree : Nat
  H : Hex.ZPoly
  lattice_matches_lift :
    lattice =
      Hex.bhksLatticeBasis input liftData.p liftData.k liftData.liftedFactors
  projected_factor_count :
    projectedRows.factorCount = lattice.factorCount

namespace ExecutableBadVectorWitness

/-- The input polynomial transported to Mathlib's `Polynomial ℤ`. -/
def inputPolynomial (W : ExecutableBadVectorWitness) : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial W.input

/-- The auxiliary bad-vector polynomial transported to Mathlib's `Polynomial ℤ`. -/
def auxiliaryPolynomial (W : ExecutableBadVectorWitness) : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial W.H

/-- The selected lifted factor, if the executable array contains the index. -/
def selectedLiftedFactor (W : ExecutableBadVectorWitness) : Hex.ZPoly :=
  W.liftData.liftedFactors.getD W.localFactorIndex 0

/--
Package an executable bad-vector witness and the remaining BHKS local
coprimality/divisibility hypotheses as abstract resultant data.
-/
def toResultantData
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    BadVectorResultantData where
  f := W.inputPolynomial
  H := W.auxiliaryPolynomial
  p := W.liftData.p
  a := W.liftData.k
  d := W.localFactorDegree
  p_pos := hp
  d_pos := hd
  coprime_over_rat := hcoprime
  resultant_divisible := hdiv

/--
Executable bad-vector packaging theorem: once later BHKS work supplies the
local coprimality and modular-divisibility hypotheses, the existing resultant
lower/upper-bound theorem applies to the transported executable data.
-/
theorem badVector_resultant_bounds
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) ≤
      |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ∧
    |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree := by
  simpa [inputPolynomial, auxiliaryPolynomial] using
    BadVectorResultantData.badVector_resultant_bounds
      W.inputPolynomial W.auxiliaryPolynomial
      W.liftData.p W.liftData.k W.localFactorDegree
      hp hd hcoprime hdiv

/--
Executable bad-vector contradiction wrapper: the transported witness cannot
exist when its Hadamard/l2norm upper bound is already below the modular divisor.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
          (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree <
        (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    False := by
  simpa [inputPolynomial, auxiliaryPolynomial] using
    BadVectorResultantData.no_badVector_of_l2norm_upper_lt_divisor_params
      W.inputPolynomial W.auxiliaryPolynomial
      W.liftData.p W.liftData.k W.localFactorDegree
      hp hd hcoprime hdiv hlt

end ExecutableBadVectorWitness

end

end HexBerlekampZassenhausMathlib
