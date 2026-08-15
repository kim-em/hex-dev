/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Interval

@[expose] public section

/-!
# Exact semantics of checked outward regularization

Finite lower cuts use Core `Dyadic.roundDown`; finite upper cuts use
`Dyadic.roundUp`. A moved endpoint is strict, while an unchanged endpoint
inherits source attainment. The proofs establish outward containment and
idempotence of the computed raw cuts. They deliberately do not claim a
globally tight grid enclosure because Core does not yet provide the converse
rounding optimality lemmas.
-/

namespace Hex.Interval

private theorem toReal_le {left right : Dyadic} (h : left ≤ right) :
    toReal left ≤ toReal right := by
  exact (Rat.cast_le (K := ℝ)).2 (Dyadic.toRat_le_toRat_iff.2 h)

private theorem lowerContains_regularize (lower : Lower)
    (precision : Precision) (x : ℝ) :
    lower.Contains x →
      (Raw.regularizeLowerUnchecked precision lower).Contains x := by
  cases lower with
  | unbounded => simp [Lower.Contains, Raw.regularizeLowerUnchecked]
  | finite value strict =>
      intro member
      by_cases same : value.roundDown precision = value
      · simpa [Raw.regularizeLowerUnchecked, same, Lower.Contains] using member
      · have lowerBound : toReal (value.roundDown precision) ≤ toReal value :=
          toReal_le Dyadic.roundDown_le
        have moved : toReal (value.roundDown precision) < toReal value :=
          lt_of_le_of_ne lowerBound fun equal => same (toReal_inj.mp equal)
        cases strict <;>
          simp [Raw.regularizeLowerUnchecked, same, Lower.Contains] at member ⊢ <;>
          linarith

private theorem upperContains_regularize (upper : Upper)
    (precision : Precision) (x : ℝ) :
    upper.Contains x →
      (Raw.regularizeUpperUnchecked precision upper).Contains x := by
  cases upper with
  | unbounded => simp [Upper.Contains, Raw.regularizeUpperUnchecked]
  | finite value strict =>
      intro member
      by_cases same : value.roundUp precision = value
      · simpa [Raw.regularizeUpperUnchecked, same, Upper.Contains] using member
      · have upperBound : toReal value ≤ toReal (value.roundUp precision) :=
          toReal_le Dyadic.le_roundUp
        have moved : toReal value < toReal (value.roundUp precision) :=
          lt_of_le_of_ne upperBound fun equal => same (toReal_inj.mp equal.symm)
        cases strict <;>
          simp [Raw.regularizeUpperUnchecked, same, Upper.Contains] at member ⊢ <;>
          linarith

/-- Every member of raw cuts remains in their outward-regularized view. -/
theorem contains_regularizeUnchecked (raw : Raw) (precision : Precision)
    (x : ℝ) :
    raw.Contains x → (raw.regularizeUnchecked precision).Contains x := by
  cases raw with
  | empty => simp [Raw.Contains]
  | bounds lower upper =>
      rintro ⟨lowerMember, upperMember⟩
      exact ⟨lowerContains_regularize lower precision x lowerMember,
        upperContains_regularize upper precision x upperMember⟩

/-- A successful checked regularization has exactly the normalized direct
rounded-cut membership predicate. -/
theorem contains_regularizeWithin {limits : Arithmetic.PrecisionLimits}
    {input result : Hex.Interval} {precision : Precision}
    (checked : regularizeWithin limits precision input = .ready result)
    (x : ℝ) :
    result.Contains x ↔
      (input.view.regularizeUnchecked precision).Contains x := by
  simp only [Contains]
  rw [view_regularizeWithin_ready checked, contains_normalize]

/-- Every source member remains in every successful outward regularization. -/
theorem mem_regularizeWithin {limits : Arithmetic.PrecisionLimits}
    {input result : Hex.Interval} {precision : Precision} {x : ℝ}
    (checked : regularizeWithin limits precision input = .ready result)
    (member : input.Contains x) : result.Contains x :=
  (contains_regularizeWithin checked x).2
    (contains_regularizeUnchecked input.view precision x member)

private theorem roundDown_idem (value : Dyadic) (precision : Precision) :
    (value.roundDown precision).roundDown precision =
      value.roundDown precision :=
  Dyadic.roundDown_eq_self_of_le Dyadic.precision_roundDown

private theorem roundUp_eq_self_of_le {value : Dyadic} {precision : Precision}
    (h : value.precision ≤ some precision) : value.roundUp precision = value := by
  rw [Dyadic.roundUp_eq_neg_roundDown_neg,
    Dyadic.roundDown_eq_self_of_le (by simpa using h)]
  apply Dyadic.toRat_inj.mp
  rw [Dyadic.toRat_neg, Dyadic.toRat_neg]
  exact neg_neg _

private theorem roundUp_idem (value : Dyadic) (precision : Precision) :
    (value.roundUp precision).roundUp precision = value.roundUp precision :=
  roundUp_eq_self_of_le Dyadic.precision_roundUp

/-- Repeating the same directed rounding leaves every computed raw cut
unchanged. This is cut idempotence, not a global grid-optimality claim. -/
theorem regularizeUnchecked_idem (raw : Raw) (precision : Precision) :
    (raw.regularizeUnchecked precision).regularizeUnchecked precision =
      raw.regularizeUnchecked precision := by
  cases raw with
  | empty => rfl
  | bounds lower upper =>
      cases lower <;> cases upper <;>
        simp [Raw.regularizeUnchecked, Raw.regularizeLowerUnchecked,
          Raw.regularizeUpperUnchecked, roundDown_idem, roundUp_idem]

end Hex.Interval
