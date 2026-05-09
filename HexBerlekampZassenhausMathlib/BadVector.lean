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

end BadVectorResultantData

end

end HexBerlekampZassenhausMathlib
