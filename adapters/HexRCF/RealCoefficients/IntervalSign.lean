/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnTheory.Real
public import HexPolyTheory.Interpret

public section

namespace Hex.RCF.RealCoefficients.IntervalSign

open Hex Hex.OrderedFn.Oracle HexPolyTheory HexPolyTheory.Interpret

/-- Exact Horner signs on a fixed rational enclosure. Singleton zero is
accepted; other zero-containing bounds decline. No refinement search runs. -/
@[expose] def sign? (p : DensePoly Rat) (lower upper : Rat) : Option Int :=
  if ordered : lower ≤ upper then
    let bounds : Bounds := ⟨lower, upper, ordered⟩
    (Hex.OrderedFn.Real.enclose (.ofConstant fun _ => bounds) p 1).exactSign?
  else none

/-- Successful enclosure evaluation identifies the sign of the same
coordinate polynomial at every real point in the recorded interval. -/
theorem sign_spec (p : DensePoly Rat) (lower upper : Rat) (x : ℝ)
    (hl : (lower : ℝ) ≤ x) (hu : x ≤ (upper : ℝ))
    (value : Int) (accepted : sign? p lower upper = some value) :
    value = (SignType.sign ((interpret (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) p).eval x) : Int) := by
  unfold sign? at accepted
  split at accepted
  · next ordered =>
      let bounds : Bounds := ⟨lower, upper, ordered⟩
      have correct : ApproximationCorrect (Rat.castHom ℝ) x
          (.ofConstant fun _ => bounds) :=
        ApproximationCorrect.ofConstant (fun _ => bounds) x (fun _ _ => ⟨hl, hu⟩)
      have contained := Hex.OrderedFn.Real.enclose_sound correct p 1 (by norm_num)
      have result := contained.exactSign accepted
      have polynomial : interpret (fun q : Rat => (q : ℝ))
          (fun _ => Rat.cast_eq_zero) p = (toPolynomial p).map (Rat.castHom ℝ) := by
        ext i
        simp only [coeff_interpret, Polynomial.coeff_map, coeff_toPolynomial]
        rfl
      simpa only [polynomial, Polynomial.eval_map, sgn] using result
  · contradiction

end Hex.RCF.RealCoefficients.IntervalSign
