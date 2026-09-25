/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.IsolationBuild
public import HexRCF.RealCoefficients.Isolations
public import HexRealAlgebraicMathlib.Order

public section

/-! The canonical real-algebraic producer feeds the generic checked-root
semantics. Its only admitted mathematical input is the shared #10389 root-sum
bridge consumed by `IsolationReplay.check_roots`. -/

namespace Hex.RCF.RealCoefficients

open HexRealRootsMathlib HexPolyMathlib.Interpret

private theorem algebraic_sign (a : RealAlgebraicNumber) :
    a.sign = (SignType.sign a.toReal : Int) := by
  rw [RealAlgebraicNumber.sign_eq]
  rcases lt_trichotomy a.toReal 0 with h | h | h
  · simp [h, _root_.sign_neg h]
  · simp [h]
  · simp [not_lt_of_ge h.le, ne_of_gt h, _root_.sign_pos h]

/-- The canonical real interpretation reflects zero. -/
theorem algebraic_zero (a : RealAlgebraicNumber) :
    a.toReal = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply RealAlgebraicNumber.toReal_injective
    simpa only [RealAlgebraicNumber.zero_toReal] using h
  · rintro rfl
    exact RealAlgebraicNumber.zero_toReal

/-- A successful canonical-algebraic isolation covers every real root of the
interpreted head and places one in each returned interval. -/
theorem isolateAt_roots [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber) (precision : Nat)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (h : isolateAt context head precision = some cert) :
    ∃ root : Fin cert.isolations.intervals.size → ℝ,
      (∀ i, (interpret RealAlgebraicNumber.toReal algebraic_zero head).IsRoot (root i) ∧
        HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper) ∧
      StrictMono root ∧
      (∀ x, (interpret RealAlgebraicNumber.toReal algebraic_zero head).IsRoot x ↔
        ∃ i, root i = x) ∧
      (∀ cut, Cell.Region root (.open cut)
        (HexRealRootsMathlib.Dyadic.toReal (cert.isolations.openPoint cut))) := by
  exact cert.check_roots RealAlgebraicNumber.toReal
    algebraic_zero
    RealAlgebraicNumber.one_toReal RealAlgebraicNumber.add_toReal
    RealAlgebraicNumber.sub_toReal RealAlgebraicNumber.mul_toReal
    (fun n => by change RealAlgebraicNumber.toRealHom (n : RealAlgebraicNumber) = (n : ℝ); simp)
    RealAlgebraicNumber.sign algebraic_sign
    (fun d => RealAlgebraicNumber.ofRat d.toRat)
    (fun d => by simp [HexRealRootsMathlib.toReal_eq_cast_toRat])
    context head (isolateAt_checked context head precision cert h)

end Hex.RCF.RealCoefficients
