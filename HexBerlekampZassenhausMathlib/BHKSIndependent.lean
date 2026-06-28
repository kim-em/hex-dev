/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import HexLLLMathlib.Independent

/-!
BHKS lattice-basis independence theorems.

The Berlekamp-Zassenhaus BHKS lattice basis is upper-triangular with positive
diagonal entries.  Discharging linear independence therefore goes through
`Matrix.independent_of_upperTriangular_pos_diag`, which is a Mathlib-side
theorem (its proof factors through the determinant/Bareiss correspondence).
These wrappers therefore live in the Mathlib-side library, not in the
Mathlib-free `HexBerlekampZassenhaus/Basic.lean` core.
-/

namespace Hex

/-- Constructor-produced BHKS `[ I_r | A_tilde ; 0 | diag(p^(a-l_j)) ]`
lattice bases are linearly independent over `Int` for positive `p`. -/
theorem bhksLatticeBasis_independent
    (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) (hp : 0 < p) :
    (bhksLatticeBasis f p a liftedFactors).basis.independent := by
  change
    (Matrix.ofFn
      (bhksLatticeEntry liftedFactors.size (f.degree?.getD 0) p a
        (bhksCutThresholds f p)
        (liftedFactors.map (fun g => cldCoeffs f p a g)))).independent
  apply Matrix.independent_of_upperTriangular_pos_diag
  · intro i j hji
    by_cases hi : i.val < liftedFactors.size
    · have hj : j.val < liftedFactors.size := by omega
      simp [Matrix.ofFn, bhksLatticeEntry, hi, hj]
      omega
    · have hi' : liftedFactors.size ≤ i.val := by omega
      by_cases hj : j.val < liftedFactors.size
      · simp [Matrix.ofFn, bhksLatticeEntry, hi, hj]
      · have hj' : liftedFactors.size ≤ j.val := by omega
        have hneq : j.val - liftedFactors.size ≠ i.val - liftedFactors.size := by omega
        simp [Matrix.ofFn, bhksLatticeEntry, hi, hj, hneq]
  · intro i
    by_cases hi : i.val < liftedFactors.size
    · simp [Matrix.ofFn, bhksLatticeEntry, hi]
    · have hi' : liftedFactors.size ≤ i.val := by omega
      have hpos : 0 < p ^ (a - (bhksCutThresholds f p).getD (i.val - liftedFactors.size) 0) :=
        Nat.pow_pos hp
      simpa [Matrix.ofFn, bhksLatticeEntry, hi] using Int.ofNat_lt.mpr hpos

/-- `bhksLatticeBasis_independent` packaged at a `LiftData` record. -/
theorem bhksLiftData_latticeBasis_independent (f : ZPoly) (d : LiftData) :
    (bhksLatticeBasis f d.p d.k d.liftedFactors).basis.independent :=
  bhksLatticeBasis_independent f d.p d.k d.liftedFactors d.p_pos

end Hex
