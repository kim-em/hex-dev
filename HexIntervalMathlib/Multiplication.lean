/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Subtraction
public import HexInterval.Multiplication

@[expose] public section

/-!
# Enclosure semantics of public interval multiplication

This module relates the checked executable multiplication to its computed raw
candidate and proves that every product of source members belongs to it.
-/

namespace Hex.Interval

@[simp]
theorem toReal_mul (left right : Dyadic) :
    toReal (left * right) = toReal left * toReal right := by
  simp [toReal]

@[simp]
theorem toReal_zero : toReal 0 = 0 := by
  simp [toReal]

/-- Computed cut predicate for exact raw multiplication. Empty is absorbing.
For two bounded-cut inputs it is the conjunction of the selected lower and
upper candidate cuts. This characterizes the algorithm's computed enclosure;
it does not claim a separate set-image tightness converse. -/
def Raw.MulContains : Raw → Raw → ℝ → Prop
  | .empty, _, _ | _, .empty, _ => False
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper, x =>
      match Raw.Mul.candidatesUnchecked
          leftLower leftUpper rightLower rightUpper with
      | [] => False
      | first :: rest =>
          (Raw.Mul.lowerCut (Raw.Mul.minimum first rest)).Contains x ∧
            (Raw.Mul.upperCut (Raw.Mul.maximum first rest)).Contains x

private theorem rawContains_mulUnchecked (left right : Raw) (x : ℝ) :
    (left.mulUnchecked right).Contains x ↔ left.MulContains right x := by
  cases left with
  | empty => simp [Raw.mulUnchecked, Raw.Contains, Raw.MulContains]
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.mulUnchecked, Raw.Contains, Raw.MulContains]
      | bounds rightLower rightUpper =>
          simp only [Raw.mulUnchecked, Raw.MulContains]
          generalize candidatesEq : Raw.Mul.candidatesUnchecked
            leftLower leftUpper rightLower rightUpper = candidates
          cases candidates <;> simp [Raw.Mul.result, Raw.Contains]

private def Raw.Mul.Candidate.LowerBounds : Raw.Mul.Candidate → ℝ → Prop
  | .negInf, _ => True
  | .finite value attained, x =>
      toReal value ≤ x ∧ (toReal value = x → attained = true)
  | .posInf, _ => False

private def Raw.Mul.Candidate.UpperBounds : Raw.Mul.Candidate → ℝ → Prop
  | .negInf, _ => False
  | .finite value attained, x =>
      x ≤ toReal value ∧ (x = toReal value → attained = true)
  | .posInf, _ => True

private def Lower.Bounds : Lower → ℝ → Prop
  | .unbounded, _ => True
  | .finite value strict, x =>
      toReal value ≤ x ∧ (toReal value = x → strict = false)

private def Upper.Bounds : Upper → ℝ → Prop
  | .finite value strict, x =>
      x ≤ toReal value ∧ (x = toReal value → strict = false)
  | .unbounded, _ => True

private theorem le_ne_iff_lt {a b : ℝ} : a ≤ b ∧ ¬a = b ↔ a < b := by
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨h.le, h.ne⟩⟩

private theorem Lower.contains_iff_bounds (lower : Lower) (x : ℝ) :
    lower.Contains x ↔ lower.Bounds x := by
  cases lower with
  | unbounded => simp [Lower.Contains, Lower.Bounds]
  | finite value strict =>
      cases strict <;> simp [Lower.Contains, Lower.Bounds, le_ne_iff_lt]

private theorem Upper.contains_iff_bounds (upper : Upper) (x : ℝ) :
    upper.Contains x ↔ upper.Bounds x := by
  cases upper with
  | unbounded => simp [Upper.Contains, Upper.Bounds]
  | finite value strict =>
      cases strict <;> simp [Upper.Contains, Upper.Bounds, le_ne_iff_lt]

private theorem Raw.Mul.Candidate.lower_min (left right : Raw.Mul.Candidate)
    {x : ℝ} (bound : left.LowerBounds x ∨ right.LowerBounds x) :
    (Raw.Mul.minUnchecked left right).LowerBounds x := by
  cases left <;> cases right <;>
    simp_all [LowerBounds, Raw.Mul.minUnchecked]
  next leftValue leftAttained rightValue rightAttained =>
    by_cases less : leftValue < rightValue
    · have realLess := toReal_lt less
      cases leftAttained <;> cases rightAttained <;>
        simp [Raw.Mul.minUnchecked, less, LowerBounds, le_ne_iff_lt] at bound ⊢ <;>
        rcases bound with bound | bound <;> linarith
    · by_cases equal : leftValue = rightValue
      · subst rightValue
        cases leftAttained <;> cases rightAttained <;>
          simp [Raw.Mul.minUnchecked, less, LowerBounds, le_ne_iff_lt] at bound ⊢ <;>
          aesop <;> linarith
      · have realNotLess : ¬toReal leftValue < toReal rightValue := by
          simpa only [toReal_lt_iff] using less
        have realNotEqual : toReal leftValue ≠ toReal rightValue := by
          intro same
          exact equal (toReal_inj.mp same)
        have realGreater : toReal rightValue < toReal leftValue :=
          lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
        cases leftAttained <;> cases rightAttained <;>
          simp [Raw.Mul.minUnchecked, less, equal, LowerBounds, le_ne_iff_lt] at bound ⊢ <;>
          rcases bound with bound | bound <;> linarith

private theorem Raw.Mul.Candidate.upper_max (left right : Raw.Mul.Candidate)
    {x : ℝ} (bound : left.UpperBounds x ∨ right.UpperBounds x) :
    (Raw.Mul.maxUnchecked left right).UpperBounds x := by
  cases left <;> cases right <;>
    simp_all [UpperBounds, Raw.Mul.maxUnchecked]
  next leftValue leftAttained rightValue rightAttained =>
    by_cases less : leftValue < rightValue
    · have realLess := toReal_lt less
      cases leftAttained <;> cases rightAttained <;>
        simp [Raw.Mul.maxUnchecked, less, UpperBounds, le_ne_iff_lt] at bound ⊢ <;>
        rcases bound with bound | bound <;> linarith
    · by_cases equal : leftValue = rightValue
      · subst rightValue
        cases leftAttained <;> cases rightAttained <;>
          simp [Raw.Mul.maxUnchecked, less, UpperBounds, le_ne_iff_lt] at bound ⊢ <;>
          aesop <;> linarith
      · have realNotLess : ¬toReal leftValue < toReal rightValue := by
          simpa only [toReal_lt_iff] using less
        have realNotEqual : toReal leftValue ≠ toReal rightValue := by
          intro same
          exact equal (toReal_inj.mp same)
        have realGreater : toReal rightValue < toReal leftValue :=
          lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
        cases leftAttained <;> cases rightAttained <;>
          simp [Raw.Mul.maxUnchecked, less, equal, UpperBounds, le_ne_iff_lt] at bound ⊢ <;>
          rcases bound with bound | bound <;> linarith

private theorem Raw.Mul.Candidate.lower_minimum (first : Raw.Mul.Candidate)
    (rest : List Raw.Mul.Candidate) {x : ℝ}
    (bound : first.LowerBounds x ∨
      ∃ candidate ∈ rest, candidate.LowerBounds x) :
    (Raw.Mul.minimum first rest).LowerBounds x := by
  induction rest generalizing first with
  | nil => simpa [Raw.Mul.minimum] using bound
  | cons next rest ih =>
      rw [Raw.Mul.minimum]
      apply ih
      rcases bound with firstBound | ⟨candidate, member, candidateBound⟩
      · exact Or.inl (Raw.Mul.Candidate.lower_min first next (Or.inl firstBound))
      · simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst candidate
          exact Or.inl (Raw.Mul.Candidate.lower_min first next (Or.inr candidateBound))
        · exact Or.inr ⟨candidate, member, candidateBound⟩

private theorem Raw.Mul.Candidate.upper_maximum (first : Raw.Mul.Candidate)
    (rest : List Raw.Mul.Candidate) {x : ℝ}
    (bound : first.UpperBounds x ∨
      ∃ candidate ∈ rest, candidate.UpperBounds x) :
    (Raw.Mul.maximum first rest).UpperBounds x := by
  induction rest generalizing first with
  | nil => simpa [Raw.Mul.maximum] using bound
  | cons next rest ih =>
      rw [Raw.Mul.maximum]
      apply ih
      rcases bound with firstBound | ⟨candidate, member, candidateBound⟩
      · exact Or.inl (Raw.Mul.Candidate.upper_max first next (Or.inl firstBound))
      · simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst candidate
          exact Or.inl (Raw.Mul.Candidate.upper_max first next (Or.inr candidateBound))
        · exact Or.inr ⟨candidate, member, candidateBound⟩

private theorem Raw.Mul.Candidate.lowerCut_contains
    (candidate : Raw.Mul.Candidate) {x : ℝ}
    (bound : candidate.LowerBounds x) :
    (Raw.Mul.lowerCut candidate).Contains x := by
  cases candidate <;>
    simp [Raw.Mul.lowerCut, Lower.Contains, LowerBounds, le_ne_iff_lt] at bound ⊢
  next value attained =>
    cases attained <;>
      simp [Raw.Mul.lowerCut, Lower.Contains, LowerBounds, le_ne_iff_lt] at bound ⊢ <;>
      exact bound

private theorem Raw.Mul.Candidate.upperCut_contains
    (candidate : Raw.Mul.Candidate) {x : ℝ}
    (bound : candidate.UpperBounds x) :
    (Raw.Mul.upperCut candidate).Contains x := by
  cases candidate <;>
    simp [Raw.Mul.upperCut, Upper.Contains, UpperBounds, le_ne_iff_lt] at bound ⊢
  next value attained =>
    cases attained <;>
      simp [Raw.Mul.upperCut, Upper.Contains, UpperBounds, le_ne_iff_lt] at bound ⊢ <;>
      exact bound

private theorem Raw.Mul.result_mem {candidates : List Raw.Mul.Candidate} {x : ℝ}
    (lower : ∃ candidate ∈ candidates, candidate.LowerBounds x)
    (upper : ∃ candidate ∈ candidates, candidate.UpperBounds x) :
    (Raw.Mul.result candidates).Contains x := by
  cases candidates with
  | nil => simp at lower
  | cons first rest =>
      simp only [Raw.Mul.result, Raw.Contains]
      constructor
      · apply Raw.Mul.Candidate.lowerCut_contains
        apply Raw.Mul.Candidate.lower_minimum
        rcases lower with ⟨candidate, member, bound⟩
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst candidate
          exact Or.inl bound
        · exact Or.inr ⟨candidate, member, bound⟩
      · apply Raw.Mul.Candidate.upperCut_contains
        apply Raw.Mul.Candidate.upper_maximum
        rcases upper with ⟨candidate, member, bound⟩
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst candidate
          exact Or.inl bound
        · exact Or.inr ⟨candidate, member, bound⟩

private theorem Raw.Mul.lowerAllowsZeroUnchecked_of_mem
    (lower : Lower) (member : lower.Contains 0) :
    Raw.Mul.lowerAllowsZeroUnchecked lower = true := by
  cases lower with
  | unbounded => rfl
  | finite value strict =>
      cases strict <;>
        simp [Lower.Contains] at member
      all_goals
        by_cases less : toReal value < 0
        · simp [Raw.Mul.lowerAllowsZeroUnchecked, Raw.Mul.signUnchecked,
            ← toReal_lt_iff, ← toReal_inj, less]
        · by_cases equal : toReal value = 0
          · simp [Raw.Mul.lowerAllowsZeroUnchecked, Raw.Mul.signUnchecked,
              ← toReal_lt_iff, ← toReal_inj, less, equal] <;> linarith
          · exfalso
            have : 0 < toReal value := lt_of_le_of_ne (le_of_not_gt less) (Ne.symm equal)
            linarith

private theorem Raw.Mul.upperAllowsZeroUnchecked_of_mem
    (upper : Upper) (member : upper.Contains 0) :
    Raw.Mul.upperAllowsZeroUnchecked upper = true := by
  cases upper with
  | unbounded => rfl
  | finite value strict =>
      cases strict <;>
        simp [Upper.Contains] at member
      all_goals
        by_cases less : toReal value < 0
        · exfalso
          linarith
        · by_cases equal : toReal value = 0
          · simp [Raw.Mul.upperAllowsZeroUnchecked, Raw.Mul.signUnchecked,
              ← toReal_lt_iff, ← toReal_inj, less, equal] <;> linarith
          · simp [Raw.Mul.upperAllowsZeroUnchecked, Raw.Mul.signUnchecked,
              ← toReal_lt_iff, ← toReal_inj, less, equal]

private theorem Raw.Mul.containsZeroUnchecked_of_mem
    (lower : Lower) (upper : Upper) {x : ℝ}
    (member : lower.Contains x ∧ upper.Contains x) (zero : x = 0) :
    Raw.Mul.containsZeroUnchecked lower upper = true := by
  subst x
  simp [Raw.Mul.containsZeroUnchecked,
    Raw.Mul.lowerAllowsZeroUnchecked_of_mem lower member.1,
    Raw.Mul.upperAllowsZeroUnchecked_of_mem upper member.2]

private theorem mul_lower_eq {a x c y : ℝ} (aNonneg : 0 ≤ a) (aLe : a ≤ x)
    (cNonneg : 0 ≤ c) (cLe : c ≤ y) (productNonzero : x * y ≠ 0)
    (equal : x * y = a * c) : x = a ∧ y = c := by
  have aNonzero : a ≠ 0 := by
    intro aZero
    apply productNonzero
    rw [equal, aZero, zero_mul]
  have cNonzero : c ≠ 0 := by
    intro cZero
    apply productNonzero
    rw [equal, cZero, mul_zero]
  have aPos : 0 < a := lt_of_le_of_ne aNonneg (Ne.symm aNonzero)
  have cPos : 0 < c := lt_of_le_of_ne cNonneg (Ne.symm cNonzero)
  have xPos : 0 < x := aPos.trans_le aLe
  have xEq : x = a := by
    by_contra notEqual
    have aLt : a < x := lt_of_le_of_ne aLe (Ne.symm notEqual)
    have first : a * c < x * c := mul_lt_mul_of_pos_right aLt cPos
    have second : x * c ≤ x * y := mul_le_mul_of_nonneg_left cLe xPos.le
    linarith
  subst x
  exact ⟨rfl, mul_left_cancel₀ aNonzero equal⟩

private theorem mul_upper_eq {x b y d : ℝ} (xPos : 0 < x) (xLe : x ≤ b)
    (yPos : 0 < y) (yLe : y ≤ d) (equal : x * y = b * d) :
    x = b ∧ y = d := by
  have bPos : 0 < b := xPos.trans_le xLe
  have dPos : 0 < d := yPos.trans_le yLe
  have xEq : x = b := by
    by_contra notEqual
    have xLt : x < b := lt_of_le_of_ne xLe notEqual
    have first : x * y ≤ x * d := mul_le_mul_of_nonneg_left yLe xPos.le
    have second : x * d < b * d := mul_lt_mul_of_pos_right xLt dPos
    linarith
  subst x
  exact ⟨rfl, mul_left_cancel₀ bPos.ne' equal⟩

private theorem upper_nonpos_of_neg_not_zero
    (lower : Lower) (upper : Dyadic) (upperStrict : Bool) {x : ℝ}
    (member : lower.Contains x ∧ (Upper.finite upper upperStrict).Contains x)
    (xNeg : x < 0)
    (notZero : Raw.Mul.containsZeroUnchecked lower (.finite upper upperStrict) = false) :
    toReal upper ≤ 0 := by
  by_contra notNonpos
  have upperPos : 0 < toReal upper := lt_of_not_ge notNonpos
  have zeroMember : lower.Contains 0 ∧ (Upper.finite upper upperStrict).Contains 0 := by
    constructor
    · cases lower with
      | unbounded => simp [Lower.Contains]
      | finite value strict =>
          cases strict <;> simp [Lower.Contains] at member ⊢ <;> linarith
    · cases upperStrict <;> simp [Upper.Contains] <;> linarith
  have yes := Raw.Mul.containsZeroUnchecked_of_mem
    lower (.finite upper upperStrict) zeroMember rfl
  simp [notZero] at yes

private theorem lower_nonneg_of_pos_not_zero
    (lower : Dyadic) (lowerStrict : Bool) (upper : Upper) {x : ℝ}
    (member : (Lower.finite lower lowerStrict).Contains x ∧ upper.Contains x)
    (xPos : 0 < x)
    (notZero : Raw.Mul.containsZeroUnchecked (.finite lower lowerStrict) upper = false) :
    0 ≤ toReal lower := by
  by_contra notNonneg
  have lowerNeg : toReal lower < 0 := lt_of_not_ge notNonneg
  have zeroMember : (Lower.finite lower lowerStrict).Contains 0 ∧ upper.Contains 0 := by
    constructor
    · cases lowerStrict <;> simp [Lower.Contains] <;> linarith
    · cases upper with
      | unbounded => simp [Upper.Contains]
      | finite value strict =>
          cases strict <;> simp [Upper.Contains] at member ⊢ <;> linarith
  have yes := Raw.Mul.containsZeroUnchecked_of_mem
    (.finite lower lowerStrict) upper zeroMember rfl
  simp [notZero] at yes

private def Raw.Mul.HasBounds (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) (x y : ℝ) : Prop :=
  (∃ candidate ∈ Raw.Mul.candidatesUnchecked leftLower leftUpper rightLower rightUpper,
      candidate.LowerBounds (x * y)) ∧
    (∃ candidate ∈ Raw.Mul.candidatesUnchecked leftLower leftUpper rightLower rightUpper,
      candidate.UpperBounds (x * y))

private theorem Raw.Mul.mem_evaluate {pairs : List (Raw.Mul.Edge × Raw.Mul.Edge)}
    {pair : Raw.Mul.Edge × Raw.Mul.Edge} {candidate : Raw.Mul.Candidate}
    (pairMem : pair ∈ pairs)
    (evaluates : Raw.Mul.productUnchecked pair.1 pair.2 = some candidate) :
    candidate ∈ Raw.Mul.evaluate pairs := by
  induction pairs with
  | nil => simp at pairMem
  | cons first rest ih =>
      simp only [List.mem_cons] at pairMem
      rcases pairMem with equal | member
      · subst pair
        simp [Raw.Mul.evaluate, evaluates]
      · simp only [Raw.Mul.evaluate]
        split
        · exact ih member
        · simp only [List.mem_cons]
          exact Or.inr (ih member)

private theorem Raw.Mul.mem_cornerLL {leftLower : Lower} {leftUpper : Upper}
    {rightLower : Lower} {rightUpper : Upper} {candidate : Raw.Mul.Candidate}
    (evaluates : Raw.Mul.productUnchecked (Raw.Mul.lowerEdge leftLower)
      (Raw.Mul.lowerEdge rightLower) = some candidate) :
    candidate ∈ Raw.Mul.candidatesUnchecked
      leftLower leftUpper rightLower rightUpper := by
  have member := Raw.Mul.mem_evaluate
    (pairs := Raw.Mul.corners leftLower leftUpper rightLower rightUpper)
    (pair := (Raw.Mul.lowerEdge leftLower, Raw.Mul.lowerEdge rightLower))
    (by simp [Raw.Mul.corners]) evaluates
  unfold Raw.Mul.candidatesUnchecked Raw.Mul.withZeroUnchecked
  split <;> simp [member]

private theorem Raw.Mul.mem_cornerLU {leftLower : Lower} {leftUpper : Upper}
    {rightLower : Lower} {rightUpper : Upper} {candidate : Raw.Mul.Candidate}
    (evaluates : Raw.Mul.productUnchecked (Raw.Mul.lowerEdge leftLower)
      (Raw.Mul.upperEdge rightUpper) = some candidate) :
    candidate ∈ Raw.Mul.candidatesUnchecked
      leftLower leftUpper rightLower rightUpper := by
  have member := Raw.Mul.mem_evaluate
    (pairs := Raw.Mul.corners leftLower leftUpper rightLower rightUpper)
    (pair := (Raw.Mul.lowerEdge leftLower, Raw.Mul.upperEdge rightUpper))
    (by simp [Raw.Mul.corners]) evaluates
  unfold Raw.Mul.candidatesUnchecked Raw.Mul.withZeroUnchecked
  split <;> simp [member]

private theorem Raw.Mul.mem_cornerUL {leftLower : Lower} {leftUpper : Upper}
    {rightLower : Lower} {rightUpper : Upper} {candidate : Raw.Mul.Candidate}
    (evaluates : Raw.Mul.productUnchecked (Raw.Mul.upperEdge leftUpper)
      (Raw.Mul.lowerEdge rightLower) = some candidate) :
    candidate ∈ Raw.Mul.candidatesUnchecked
      leftLower leftUpper rightLower rightUpper := by
  have member := Raw.Mul.mem_evaluate
    (pairs := Raw.Mul.corners leftLower leftUpper rightLower rightUpper)
    (pair := (Raw.Mul.upperEdge leftUpper, Raw.Mul.lowerEdge rightLower))
    (by simp [Raw.Mul.corners]) evaluates
  unfold Raw.Mul.candidatesUnchecked Raw.Mul.withZeroUnchecked
  split <;> simp [member]

private theorem Raw.Mul.mem_cornerUU {leftLower : Lower} {leftUpper : Upper}
    {rightLower : Lower} {rightUpper : Upper} {candidate : Raw.Mul.Candidate}
    (evaluates : Raw.Mul.productUnchecked (Raw.Mul.upperEdge leftUpper)
      (Raw.Mul.upperEdge rightUpper) = some candidate) :
    candidate ∈ Raw.Mul.candidatesUnchecked
      leftLower leftUpper rightLower rightUpper := by
  have member := Raw.Mul.mem_evaluate
    (pairs := Raw.Mul.corners leftLower leftUpper rightLower rightUpper)
    (pair := (Raw.Mul.upperEdge leftUpper, Raw.Mul.upperEdge rightUpper))
    (by simp [Raw.Mul.corners]) evaluates
  unfold Raw.Mul.candidatesUnchecked Raw.Mul.withZeroUnchecked
  split <;> simp [member]

private theorem Raw.Mul.mem_zero {leftLower : Lower} {leftUpper : Upper}
    {rightLower : Lower} {rightUpper : Upper}
    (contains : Raw.Mul.containsZeroUnchecked leftLower leftUpper ||
      Raw.Mul.containsZeroUnchecked rightLower rightUpper) :
    Raw.Mul.Candidate.finite 0 true ∈ Raw.Mul.candidatesUnchecked
      leftLower leftUpper rightLower rightUpper := by
  simp [Raw.Mul.candidatesUnchecked, Raw.Mul.withZeroUnchecked, contains]

private theorem Raw.Mul.corner_bounds_neg_neg
    (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) {x y : ℝ}
    (leftMember : leftLower.Contains x ∧ leftUpper.Contains x)
    (rightMember : rightLower.Contains y ∧ rightUpper.Contains y)
    (hx : x < 0) (hy : y < 0) :
    Raw.Mul.HasBounds leftLower leftUpper rightLower rightUpper x y := by
  unfold Raw.Mul.HasBounds
  constructor
  · by_cases zero : Raw.Mul.containsZeroUnchecked leftLower leftUpper ||
        Raw.Mul.containsZeroUnchecked rightLower rightUpper
    · exact ⟨.finite 0 true, Raw.Mul.mem_zero zero,
        by simp [Raw.Mul.Candidate.LowerBounds, (mul_pos_of_neg_of_neg hx hy).le]⟩
    · have noZero := Bool.eq_false_of_not_eq_true zero
      have sides := Bool.or_eq_false_iff.mp noZero
      cases leftUpper with
      | unbounded =>
          have zeroMember : leftLower.Contains 0 ∧ Upper.unbounded.Contains 0 := by
            constructor
            · cases leftLower with
              | unbounded => simp [Lower.Contains]
              | finite value strict =>
                  cases strict <;> simp [Lower.Contains] at leftMember ⊢ <;> linarith
            · simp [Upper.Contains]
          have yes := Raw.Mul.containsZeroUnchecked_of_mem
            leftLower .unbounded zeroMember rfl
          simp [sides.1] at yes
      | finite leftValue leftStrict =>
          have leftNonpos := upper_nonpos_of_neg_not_zero leftLower leftValue leftStrict
            leftMember hx sides.1
          cases rightUpper with
          | unbounded =>
              have zeroMember : rightLower.Contains 0 ∧ Upper.unbounded.Contains 0 := by
                constructor
                · cases rightLower with
                  | unbounded => simp [Lower.Contains]
                  | finite value strict =>
                      cases strict <;> simp [Lower.Contains] at rightMember ⊢ <;> linarith
                · simp [Upper.Contains]
              have yes := Raw.Mul.containsZeroUnchecked_of_mem
                rightLower .unbounded zeroMember rfl
              simp [sides.2] at yes
          | finite rightValue rightStrict =>
              have rightNonpos := upper_nonpos_of_neg_not_zero rightLower rightValue
                rightStrict rightMember hy sides.2
              refine ⟨.finite (leftValue * rightValue) (!leftStrict && !rightStrict),
                Raw.Mul.mem_cornerUU rfl, ?_⟩
              simp only [Raw.Mul.Candidate.LowerBounds, toReal_mul]
              constructor
              · have leftLe := ((Upper.contains_iff_bounds _ _).1 leftMember.2).1
                  |> neg_le_neg
                have rightLe := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
                  |> neg_le_neg
                have first := mul_le_mul_of_nonneg_right leftLe
                  (neg_nonneg.mpr rightNonpos)
                have second := mul_le_mul_of_nonneg_left rightLe (neg_pos.mpr hx).le
                nlinarith
              · intro equal
                have leftLe := ((Upper.contains_iff_bounds _ _).1 leftMember.2).1
                have rightLe := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
                have ends := mul_lower_eq (neg_nonneg.mpr leftNonpos)
                  (neg_le_neg leftLe) (neg_nonneg.mpr rightNonpos)
                  (neg_le_neg rightLe)
                  (mul_ne_zero (neg_ne_zero.mpr (ne_of_lt hx))
                    (neg_ne_zero.mpr (ne_of_lt hy))) (by nlinarith)
                have leftClosed := ((Upper.contains_iff_bounds _ _).1 leftMember.2).2
                  (by nlinarith [ends.1])
                have rightClosed := ((Upper.contains_iff_bounds _ _).1 rightMember.2).2
                  (by nlinarith [ends.2])
                simp [leftClosed, rightClosed]
  · cases leftLower with
    | unbounded =>
        cases rightLower with
        | unbounded => exact ⟨.posInf, Raw.Mul.mem_cornerLL rfl, by simp
            [Raw.Mul.Candidate.UpperBounds]⟩
        | finite rightValue rightStrict =>
            have rightNeg : toReal rightValue < 0 := by
              have bound := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
              linarith
            refine ⟨.posInf, Raw.Mul.mem_cornerLL ?_, by simp
              [Raw.Mul.Candidate.UpperBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.lowerEdge, Raw.Mul.signUnchecked,
              ← toReal_lt_iff, rightNeg]
    | finite leftValue leftStrict =>
        have leftLe := ((Lower.contains_iff_bounds _ _).1 leftMember.1).1
        have leftNeg : toReal leftValue < 0 := leftLe.trans_lt hx
        cases rightLower with
        | unbounded =>
            refine ⟨.posInf, Raw.Mul.mem_cornerLL ?_, by simp
              [Raw.Mul.Candidate.UpperBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.lowerEdge, Raw.Mul.signUnchecked,
              ← toReal_lt_iff, leftNeg]
        | finite rightValue rightStrict =>
            have rightLe := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
            have rightNeg : toReal rightValue < 0 := rightLe.trans_lt hy
            refine ⟨.finite (leftValue * rightValue)
                (!leftStrict && !rightStrict), Raw.Mul.mem_cornerLL rfl, ?_⟩
            simp only [Raw.Mul.Candidate.UpperBounds, toReal_mul]
            constructor
            · have first := mul_le_mul_of_nonneg_right (neg_le_neg leftLe)
                (neg_pos.mpr hy).le
              have second := mul_le_mul_of_nonneg_left (neg_le_neg rightLe)
                (neg_nonneg.mpr leftNeg.le)
              nlinarith
            · intro equal
              have ends := mul_upper_eq (neg_pos.mpr hx) (neg_le_neg leftLe)
                (neg_pos.mpr hy) (neg_le_neg rightLe) (by nlinarith)
              have leftClosed := ((Lower.contains_iff_bounds _ _).1 leftMember.1).2
                (by nlinarith [ends.1])
              have rightClosed := ((Lower.contains_iff_bounds _ _).1 rightMember.1).2
                (by nlinarith [ends.2])
              simp [leftClosed, rightClosed]

private theorem Raw.Mul.corner_bounds_neg_pos
    (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) {x y : ℝ}
    (leftMember : leftLower.Contains x ∧ leftUpper.Contains x)
    (rightMember : rightLower.Contains y ∧ rightUpper.Contains y)
    (hx : x < 0) (hy : 0 < y) :
    Raw.Mul.HasBounds leftLower leftUpper rightLower rightUpper x y := by
  unfold Raw.Mul.HasBounds
  constructor
  · cases leftLower with
    | unbounded =>
        cases rightUpper with
        | unbounded => exact ⟨.negInf, Raw.Mul.mem_cornerLU rfl, by simp
            [Raw.Mul.Candidate.LowerBounds]⟩
        | finite rightValue rightStrict =>
            have rightPos : 0 < toReal rightValue := by
              have bound := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
              exact hy.trans_le bound
            refine ⟨.negInf, Raw.Mul.mem_cornerLU ?_, by simp
              [Raw.Mul.Candidate.LowerBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.lowerEdge, Raw.Mul.upperEdge,
              Raw.Mul.signUnchecked, ← toReal_lt_iff, ← toReal_inj,
              not_lt_of_ge rightPos.le, rightPos.ne']
    | finite leftValue leftStrict =>
        have leftLe := ((Lower.contains_iff_bounds _ _).1 leftMember.1).1
        have leftNeg : toReal leftValue < 0 := leftLe.trans_lt hx
        cases rightUpper with
        | unbounded =>
            refine ⟨.negInf, Raw.Mul.mem_cornerLU ?_, by simp
              [Raw.Mul.Candidate.LowerBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.lowerEdge, Raw.Mul.upperEdge,
              Raw.Mul.signUnchecked, ← toReal_lt_iff, leftNeg]
        | finite rightValue rightStrict =>
            have rightLe := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
            have rightPos : 0 < toReal rightValue := hy.trans_le rightLe
            refine ⟨.finite (leftValue * rightValue)
                (!leftStrict && !rightStrict), Raw.Mul.mem_cornerLU rfl, ?_⟩
            simp only [Raw.Mul.Candidate.LowerBounds, toReal_mul]
            constructor
            · have first := mul_le_mul_of_nonneg_right (neg_le_neg leftLe) hy.le
              have second := mul_le_mul_of_nonneg_left rightLe (neg_pos.mpr hx).le
              nlinarith
            · intro equal
              have ends := mul_upper_eq (neg_pos.mpr hx) (neg_le_neg leftLe)
                hy rightLe (by nlinarith)
              have leftClosed := ((Lower.contains_iff_bounds _ _).1 leftMember.1).2
                (by nlinarith [ends.1])
              have rightClosed := ((Upper.contains_iff_bounds _ _).1 rightMember.2).2
                ends.2
              simp [leftClosed, rightClosed]
  · by_cases zero : Raw.Mul.containsZeroUnchecked leftLower leftUpper ||
        Raw.Mul.containsZeroUnchecked rightLower rightUpper
    · exact ⟨.finite 0 true, Raw.Mul.mem_zero zero,
        by simp [Raw.Mul.Candidate.UpperBounds, (mul_neg_of_neg_of_pos hx hy).le]⟩
    · have noZero := Bool.eq_false_of_not_eq_true zero
      have sides := Bool.or_eq_false_iff.mp noZero
      cases leftUpper with
      | unbounded =>
          have zeroMember : leftLower.Contains 0 ∧ Upper.unbounded.Contains 0 := by
            constructor
            · cases leftLower with
              | unbounded => simp [Lower.Contains]
              | finite value strict =>
                  cases strict <;> simp [Lower.Contains] at leftMember ⊢ <;> linarith
            · simp [Upper.Contains]
          have yes := Raw.Mul.containsZeroUnchecked_of_mem
            leftLower .unbounded zeroMember rfl
          simp [sides.1] at yes
      | finite leftValue leftStrict =>
          have leftNonpos := upper_nonpos_of_neg_not_zero leftLower leftValue leftStrict
            leftMember hx sides.1
          cases rightLower with
          | unbounded =>
              have zeroMember : Lower.unbounded.Contains 0 ∧ rightUpper.Contains 0 := by
                constructor
                · simp [Lower.Contains]
                · cases rightUpper with
                  | unbounded => simp [Upper.Contains]
                  | finite value strict =>
                      cases strict <;> simp [Upper.Contains] at rightMember ⊢ <;> linarith
              have yes := Raw.Mul.containsZeroUnchecked_of_mem
                .unbounded rightUpper zeroMember rfl
              simp [sides.2] at yes
          | finite rightValue rightStrict =>
              have rightNonneg := lower_nonneg_of_pos_not_zero rightValue rightStrict
                rightUpper rightMember hy sides.2
              refine ⟨.finite (leftValue * rightValue)
                  (!leftStrict && !rightStrict), Raw.Mul.mem_cornerUL rfl, ?_⟩
              simp only [Raw.Mul.Candidate.UpperBounds, toReal_mul]
              constructor
              · have leftLe := ((Upper.contains_iff_bounds _ _).1 leftMember.2).1
                  |> neg_le_neg
                have rightLe := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
                have first := mul_le_mul_of_nonneg_right leftLe rightNonneg
                have second := mul_le_mul_of_nonneg_left rightLe (neg_pos.mpr hx).le
                nlinarith
              · intro equal
                have leftLe := ((Upper.contains_iff_bounds _ _).1 leftMember.2).1
                have rightLe := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
                have ends := mul_lower_eq (neg_nonneg.mpr leftNonpos)
                  (neg_le_neg leftLe) rightNonneg rightLe
                  (mul_ne_zero (neg_ne_zero.mpr (ne_of_lt hx)) (ne_of_gt hy))
                  (by nlinarith)
                have leftClosed := ((Upper.contains_iff_bounds _ _).1 leftMember.2).2
                  (by nlinarith [ends.1])
                have rightClosed := ((Lower.contains_iff_bounds _ _).1 rightMember.1).2
                  ends.2.symm
                simp [leftClosed, rightClosed]

private theorem Raw.Mul.corner_bounds_pos_neg
    (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) {x y : ℝ}
    (leftMember : leftLower.Contains x ∧ leftUpper.Contains x)
    (rightMember : rightLower.Contains y ∧ rightUpper.Contains y)
    (hx : 0 < x) (hy : y < 0) :
    Raw.Mul.HasBounds leftLower leftUpper rightLower rightUpper x y := by
  unfold Raw.Mul.HasBounds
  constructor
  · cases leftUpper with
    | unbounded =>
        cases rightLower with
        | unbounded => exact ⟨.negInf, Raw.Mul.mem_cornerUL rfl, by simp
            [Raw.Mul.Candidate.LowerBounds]⟩
        | finite rightValue rightStrict =>
            have rightLe := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
            have rightNeg : toReal rightValue < 0 := rightLe.trans_lt hy
            refine ⟨.negInf, Raw.Mul.mem_cornerUL ?_, by simp
              [Raw.Mul.Candidate.LowerBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.lowerEdge, Raw.Mul.upperEdge,
              Raw.Mul.signUnchecked, ← toReal_lt_iff, rightNeg]
    | finite leftValue leftStrict =>
        have leftLe := ((Upper.contains_iff_bounds _ _).1 leftMember.2).1
        have leftPos : 0 < toReal leftValue := hx.trans_le leftLe
        cases rightLower with
        | unbounded =>
            refine ⟨.negInf, Raw.Mul.mem_cornerUL ?_, by simp
              [Raw.Mul.Candidate.LowerBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.lowerEdge, Raw.Mul.upperEdge,
              Raw.Mul.signUnchecked, ← toReal_lt_iff, ← toReal_inj,
              not_lt_of_ge leftPos.le, leftPos.ne']
        | finite rightValue rightStrict =>
            have rightLe := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
            have rightNeg : toReal rightValue < 0 := rightLe.trans_lt hy
            refine ⟨.finite (leftValue * rightValue)
                (!leftStrict && !rightStrict), Raw.Mul.mem_cornerUL rfl, ?_⟩
            simp only [Raw.Mul.Candidate.LowerBounds, toReal_mul]
            constructor
            · have first := mul_le_mul_of_nonneg_right leftLe (neg_pos.mpr hy).le
              have second := mul_le_mul_of_nonneg_left (neg_le_neg rightLe) hx.le
              nlinarith
            · intro equal
              have ends := mul_upper_eq hx leftLe (neg_pos.mpr hy)
                (neg_le_neg rightLe) (by nlinarith)
              have leftClosed := ((Upper.contains_iff_bounds _ _).1 leftMember.2).2
                ends.1
              have rightClosed := ((Lower.contains_iff_bounds _ _).1 rightMember.1).2
                (by nlinarith [ends.2])
              simp [leftClosed, rightClosed]
  · by_cases zero : Raw.Mul.containsZeroUnchecked leftLower leftUpper ||
        Raw.Mul.containsZeroUnchecked rightLower rightUpper
    · exact ⟨.finite 0 true, Raw.Mul.mem_zero zero,
        by simp [Raw.Mul.Candidate.UpperBounds, (mul_neg_of_pos_of_neg hx hy).le]⟩
    · have noZero := Bool.eq_false_of_not_eq_true zero
      have sides := Bool.or_eq_false_iff.mp noZero
      cases leftLower with
      | unbounded =>
          have zeroMember : Lower.unbounded.Contains 0 ∧ leftUpper.Contains 0 := by
            constructor
            · simp [Lower.Contains]
            · cases leftUpper with
              | unbounded => simp [Upper.Contains]
              | finite value strict =>
                  cases strict <;> simp [Upper.Contains] at leftMember ⊢ <;> linarith
          have yes := Raw.Mul.containsZeroUnchecked_of_mem
            .unbounded leftUpper zeroMember rfl
          simp [sides.1] at yes
      | finite leftValue leftStrict =>
          have leftNonneg := lower_nonneg_of_pos_not_zero leftValue leftStrict
            leftUpper leftMember hx sides.1
          cases rightUpper with
          | unbounded =>
              have zeroMember : rightLower.Contains 0 ∧ Upper.unbounded.Contains 0 := by
                constructor
                · cases rightLower with
                  | unbounded => simp [Lower.Contains]
                  | finite value strict =>
                      cases strict <;> simp [Lower.Contains] at rightMember ⊢ <;> linarith
                · simp [Upper.Contains]
              have yes := Raw.Mul.containsZeroUnchecked_of_mem
                rightLower .unbounded zeroMember rfl
              simp [sides.2] at yes
          | finite rightValue rightStrict =>
              have rightNonpos := upper_nonpos_of_neg_not_zero rightLower rightValue
                rightStrict rightMember hy sides.2
              refine ⟨.finite (leftValue * rightValue)
                  (!leftStrict && !rightStrict), Raw.Mul.mem_cornerLU rfl, ?_⟩
              simp only [Raw.Mul.Candidate.UpperBounds, toReal_mul]
              constructor
              · have leftLe := ((Lower.contains_iff_bounds _ _).1 leftMember.1).1
                have rightLe := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
                  |> neg_le_neg
                have first := mul_le_mul_of_nonneg_right leftLe
                  (neg_nonneg.mpr rightNonpos)
                have second := mul_le_mul_of_nonneg_left rightLe hx.le
                nlinarith
              · intro equal
                have leftLe := ((Lower.contains_iff_bounds _ _).1 leftMember.1).1
                have rightLe := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
                have ends := mul_lower_eq leftNonneg leftLe
                  (neg_nonneg.mpr rightNonpos) (neg_le_neg rightLe)
                  (mul_ne_zero (ne_of_gt hx) (neg_ne_zero.mpr (ne_of_lt hy)))
                  (by nlinarith)
                have leftClosed := ((Lower.contains_iff_bounds _ _).1 leftMember.1).2
                  ends.1.symm
                have rightClosed := ((Upper.contains_iff_bounds _ _).1 rightMember.2).2
                  (by nlinarith [ends.2])
                simp [leftClosed, rightClosed]

private theorem Raw.Mul.corner_bounds_pos_pos
    (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) {x y : ℝ}
    (leftMember : leftLower.Contains x ∧ leftUpper.Contains x)
    (rightMember : rightLower.Contains y ∧ rightUpper.Contains y)
    (hx : 0 < x) (hy : 0 < y) :
    Raw.Mul.HasBounds leftLower leftUpper rightLower rightUpper x y := by
  unfold Raw.Mul.HasBounds
  constructor
  · by_cases zero : Raw.Mul.containsZeroUnchecked leftLower leftUpper ||
        Raw.Mul.containsZeroUnchecked rightLower rightUpper
    · exact ⟨.finite 0 true, Raw.Mul.mem_zero zero,
        by simp [Raw.Mul.Candidate.LowerBounds, (mul_pos hx hy).le]⟩
    · have noZero := Bool.eq_false_of_not_eq_true zero
      have sides := Bool.or_eq_false_iff.mp noZero
      cases leftLower with
      | unbounded =>
          have zeroMember : Lower.unbounded.Contains 0 ∧ leftUpper.Contains 0 := by
            constructor
            · simp [Lower.Contains]
            · cases leftUpper with
              | unbounded => simp [Upper.Contains]
              | finite value strict =>
                  cases strict <;> simp [Upper.Contains] at leftMember ⊢ <;> linarith
          have yes := Raw.Mul.containsZeroUnchecked_of_mem
            .unbounded leftUpper zeroMember rfl
          simp [sides.1] at yes
      | finite leftValue leftStrict =>
          have leftNonneg := lower_nonneg_of_pos_not_zero leftValue leftStrict
            leftUpper leftMember hx sides.1
          cases rightLower with
          | unbounded =>
              have zeroMember : Lower.unbounded.Contains 0 ∧ rightUpper.Contains 0 := by
                constructor
                · simp [Lower.Contains]
                · cases rightUpper with
                  | unbounded => simp [Upper.Contains]
                  | finite value strict =>
                      cases strict <;> simp [Upper.Contains] at rightMember ⊢ <;> linarith
              have yes := Raw.Mul.containsZeroUnchecked_of_mem
                .unbounded rightUpper zeroMember rfl
              simp [sides.2] at yes
          | finite rightValue rightStrict =>
              have rightNonneg := lower_nonneg_of_pos_not_zero rightValue rightStrict
                rightUpper rightMember hy sides.2
              refine ⟨.finite (leftValue * rightValue)
                  (!leftStrict && !rightStrict), Raw.Mul.mem_cornerLL rfl, ?_⟩
              simp only [Raw.Mul.Candidate.LowerBounds, toReal_mul]
              constructor
              · have leftLe := ((Lower.contains_iff_bounds _ _).1 leftMember.1).1
                have rightLe := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
                exact mul_le_mul leftLe rightLe rightNonneg hx.le
              · intro equal
                have leftLe := ((Lower.contains_iff_bounds _ _).1 leftMember.1).1
                have rightLe := ((Lower.contains_iff_bounds _ _).1 rightMember.1).1
                have ends := mul_lower_eq leftNonneg leftLe rightNonneg rightLe
                  (mul_ne_zero (ne_of_gt hx) (ne_of_gt hy)) equal.symm
                have leftClosed := ((Lower.contains_iff_bounds _ _).1 leftMember.1).2
                  ends.1.symm
                have rightClosed := ((Lower.contains_iff_bounds _ _).1 rightMember.1).2
                  ends.2.symm
                simp [leftClosed, rightClosed]
  · cases leftUpper with
    | unbounded =>
        cases rightUpper with
        | unbounded => exact ⟨.posInf, Raw.Mul.mem_cornerUU rfl, by simp
            [Raw.Mul.Candidate.UpperBounds]⟩
        | finite rightValue rightStrict =>
            have rightPos : 0 < toReal rightValue := by
              have bound := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
              exact hy.trans_le bound
            refine ⟨.posInf, Raw.Mul.mem_cornerUU ?_, by simp
              [Raw.Mul.Candidate.UpperBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.upperEdge, Raw.Mul.signUnchecked,
              ← toReal_lt_iff, ← toReal_inj, not_lt_of_ge rightPos.le,
              rightPos.ne']
    | finite leftValue leftStrict =>
        have leftLe := ((Upper.contains_iff_bounds _ _).1 leftMember.2).1
        have leftPos : 0 < toReal leftValue := hx.trans_le leftLe
        cases rightUpper with
        | unbounded =>
            refine ⟨.posInf, Raw.Mul.mem_cornerUU ?_, by simp
              [Raw.Mul.Candidate.UpperBounds]⟩
            simp [Raw.Mul.productUnchecked, Raw.Mul.upperEdge, Raw.Mul.signUnchecked,
              ← toReal_lt_iff, ← toReal_inj, not_lt_of_ge leftPos.le,
              leftPos.ne']
        | finite rightValue rightStrict =>
            have rightLe := ((Upper.contains_iff_bounds _ _).1 rightMember.2).1
            have rightPos : 0 < toReal rightValue := hy.trans_le rightLe
            refine ⟨.finite (leftValue * rightValue)
                (!leftStrict && !rightStrict), Raw.Mul.mem_cornerUU rfl, ?_⟩
            simp only [Raw.Mul.Candidate.UpperBounds, toReal_mul]
            constructor
            · exact mul_le_mul leftLe rightLe hy.le (hx.le.trans leftLe)
            · intro equal
              have ends := mul_upper_eq hx leftLe hy rightLe equal
              have leftClosed := ((Upper.contains_iff_bounds _ _).1 leftMember.2).2
                ends.1
              have rightClosed := ((Upper.contains_iff_bounds _ _).1 rightMember.2).2
                ends.2
              simp [leftClosed, rightClosed]

private theorem Raw.Mul.corner_bounds
    (leftLower : Lower) (leftUpper : Upper)
    (rightLower : Lower) (rightUpper : Upper) {x y : ℝ}
    (leftMember : leftLower.Contains x ∧ leftUpper.Contains x)
    (rightMember : rightLower.Contains y ∧ rightUpper.Contains y) :
    Raw.Mul.HasBounds leftLower leftUpper rightLower rightUpper x y := by
  by_cases productZero : x * y = 0
  · rcases mul_eq_zero.mp productZero with xZero | yZero
    · have containsZero := Raw.Mul.containsZeroUnchecked_of_mem
        leftLower leftUpper leftMember xZero
      refine ⟨⟨.finite 0 true, ?_, ?_⟩, ⟨.finite 0 true, ?_, ?_⟩⟩
      all_goals simp [Raw.Mul.HasBounds, Raw.Mul.candidatesUnchecked,
        Raw.Mul.withZeroUnchecked, containsZero, productZero,
        Raw.Mul.Candidate.LowerBounds, Raw.Mul.Candidate.UpperBounds]
    · have containsZero := Raw.Mul.containsZeroUnchecked_of_mem
        rightLower rightUpper rightMember yZero
      refine ⟨⟨.finite 0 true, ?_, ?_⟩, ⟨.finite 0 true, ?_, ?_⟩⟩
      all_goals simp [Raw.Mul.HasBounds, Raw.Mul.candidatesUnchecked,
        Raw.Mul.withZeroUnchecked, containsZero, productZero,
        Raw.Mul.Candidate.LowerBounds, Raw.Mul.Candidate.UpperBounds]
  have xNonzero : x ≠ 0 := fun equal => productZero (by simp [equal])
  have yNonzero : y ≠ 0 := fun equal => productZero (by simp [equal])
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · exact Raw.Mul.corner_bounds_neg_neg _ _ _ _ leftMember rightMember hx hy
    · exact Raw.Mul.corner_bounds_neg_pos _ _ _ _ leftMember rightMember hx
        (lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm yNonzero))
  · by_cases hy : y < 0
    · exact Raw.Mul.corner_bounds_pos_neg _ _ _ _ leftMember rightMember
        (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm xNonzero)) hy
    · exact Raw.Mul.corner_bounds_pos_pos _ _ _ _ leftMember rightMember
        (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm xNonzero))
        (lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm yNonzero))

private theorem raw_mul_mem (left right : Raw) {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    (left.mulUnchecked right).Contains (x * y) := by
  cases left with
  | empty => simp [Raw.Contains] at leftMember
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.Contains] at rightMember
      | bounds rightLower rightUpper =>
          apply Raw.Mul.result_mem
          · exact (Raw.Mul.corner_bounds leftLower leftUpper rightLower rightUpper
              leftMember rightMember).1
          · exact (Raw.Mul.corner_bounds leftLower leftUpper rightLower rightUpper
              leftMember rightMember).2

/-- A successful multiplication has exactly its normalized computed-cut
predicate. -/
theorem contains_mulWithin {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : mulWithin limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.view.MulContains right.view x := by
  simp only [Contains]
  rw [view_mulWithin_ready checked, contains_normalize]
  exact rawContains_mulUnchecked left.view right.view x

/-- Multiplication maps every pair of source members into the successful
computed interval. -/
theorem mul_mem_mulWithin {limit : EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : mulWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (x * y) :=
  (contains_mulWithin checked (x * y)).2
    ((rawContains_mulUnchecked left.view right.view (x * y)).1
      (raw_mul_mem left.view right.view leftMember rightMember))

end Hex.Interval
