/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Division
public import HexPolyFast.Karatsuba

public section

/-!
Recursive half-gcd with certified quotient prediction.

High halves predict a batch of Euclidean quotients.  Applying a prediction to
the full operands is cheap: `a - q*b` uses the selected multiplication plan.
The prediction is accepted only when that remainder is strictly smaller than
`b`; Euclidean uniqueness then proves that it is exactly the quotient returned
by `DensePoly.divMod`.  A failed prediction falls back to plan-driven Newton
division.  Thus approximation affects cost but never semantics.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {F : Type u} [DecidableEq F] [Lean.Grind.Field F]

/-- A two-by-two polynomial transformation, kept local to fast gcd rather
than introducing a dependency on the matrix library. -/
structure GcdStep (F : Type u) [Zero F] [DecidableEq F] where
  a00 : DensePoly F
  a01 : DensePoly F
  a10 : DensePoly F
  a11 : DensePoly F

namespace GcdStep

/-- Identity transformation. -/
def one : GcdStep F :=
  { a00 := 1, a01 := 0, a10 := 0, a11 := 1 }

/-- One Euclidean transformation `(a,b) ↦ (b,a-q*b)`. -/
def euclid (q : DensePoly F) : GcdStep F :=
  { a00 := 0, a01 := 1, a10 := 1, a11 := -q }

/-- Matrix composition; `compose m n` applies `n` first and then `m`. -/
def compose (m n : GcdStep F) : GcdStep F :=
  { a00 := m.a00 * n.a00 + m.a01 * n.a10
    a01 := m.a00 * n.a01 + m.a01 * n.a11
    a10 := m.a10 * n.a00 + m.a11 * n.a10
    a11 := m.a10 * n.a01 + m.a11 * n.a11 }

/-- Plan-driven matrix composition.  Half-gcd builds transformations at half
the active degree and composes them before touching the full operands. -/
def composeWith (plan : MulPlan F) (m n : GcdStep F) : GcdStep F :=
  { a00 := mulWith plan m.a00 n.a00 + mulWith plan m.a01 n.a10
    a01 := mulWith plan m.a00 n.a01 + mulWith plan m.a01 n.a11
    a10 := mulWith plan m.a10 n.a00 + mulWith plan m.a11 n.a10
    a11 := mulWith plan m.a10 n.a01 + mulWith plan m.a11 n.a11 }

/-- Compose one Euclidean row update with an existing transformation.  The
elementary matrix contains only zero, one, and `-q`, so this specialization
uses two planned products instead of the eight used by generic composition. -/
def euclidComposeWith (plan : MulPlan F) (q : DensePoly F)
    (m : GcdStep F) : GcdStep F :=
  { a00 := m.a10
    a01 := m.a11
    a10 := m.a00 + mulWith plan (-q) m.a10
    a11 := m.a01 + mulWith plan (-q) m.a11 }

/-- Matrix composition clipped to the coefficient range that can survive in
the caller's degree-bounded transformation. -/
def composeLowWith (plan : MulPlan F) (len : Nat)
    (m n : GcdStep F) : GcdStep F :=
  { a00 := mulLow plan len m.a00 n.a00 + mulLow plan len m.a01 n.a10
    a01 := mulLow plan len m.a00 n.a01 + mulLow plan len m.a01 n.a11
    a10 := mulLow plan len m.a10 n.a00 + mulLow plan len m.a11 n.a10
    a11 := mulLow plan len m.a10 n.a01 + mulLow plan len m.a11 n.a11 }

/-- Apply a transformation to a polynomial pair. -/
def apply (m : GcdStep F) (a b : DensePoly F) : DensePoly F × DensePoly F :=
  (m.a00 * a + m.a01 * b, m.a10 * a + m.a11 * b)

/-- Apply a transformation using the selected multiplication plan. -/
def applyWith (plan : MulPlan F) (m : GcdStep F)
    (a b : DensePoly F) : DensePoly F × DensePoly F :=
  (mulWith plan m.a00 a + mulWith plan m.a01 b,
    mulWith plan m.a10 a + mulWith plan m.a11 b)

/-- Apply a transformation while materializing only the requested low
coefficient range.  Half-gcd supplies the active input size as the bound. -/
def applyLowWith (plan : MulPlan F) (len : Nat) (m : GcdStep F)
    (a b : DensePoly F) : DensePoly F × DensePoly F :=
  (mulLow plan len m.a00 a + mulLow plan len m.a01 b,
    mulLow plan len m.a10 a + mulLow plan len m.a11 b)

/-- Reconstruct a full application from its already-computed high-half
application and one application to the low halves.  Half-gcd uses this to
avoid applying the same recursive matrix to the full operands again. -/
def applyFromHighWith (plan : MulPlan F) (k : Nat) (m : GcdStep F)
    (highPair : DensePoly F × DensePoly F) (a b : DensePoly F) :
    DensePoly F × DensePoly F :=
  let lowPair := applyWith plan m (low k a) (low k b)
  (lowPair.1 + shift k highPair.1, lowPair.2 + shift k highPair.2)

/-- Planned composition has the ordinary matrix semantics. -/
theorem composeWith_eq (plan : MulPlan F) (m n : GcdStep F) :
    composeWith plan m n = compose m n := by
  cases m
  cases n
  simp only [composeWith, compose, mulWith_eq]

/-- Specialized Euclidean composition has the generic planned matrix
semantics. -/
theorem euclidComposeWith_eq (plan : MulPlan F) (q : DensePoly F)
    (m : GcdStep F) :
    euclidComposeWith plan q m = composeWith plan (euclid q) m := by
  cases m
  simp only [euclidComposeWith, composeWith, euclid, mulWith_eq]
  have honemul : ∀ p : DensePoly F, (1 : DensePoly F) * p = p := by
    intro p
    rw [mul_comm_poly, mul_one_right_poly]
  simp only [zero_mul, zero_add, honemul]

/-- Planned application has the ordinary matrix semantics. -/
theorem applyWith_eq (plan : MulPlan F) (m : GcdStep F) (a b : DensePoly F) :
    applyWith plan m a b = apply m a b := by
  simp only [applyWith, apply, mulWith_eq]

private theorem add_mulLow_eq (plan : MulPlan F) (len : Nat)
    (a b c d : DensePoly F) (hsize : (a * b + c * d).size ≤ len) :
    mulLow plan len a b + mulLow plan len c d = a * b + c * d := by
  apply ext_coeff
  intro i
  rw [coeff_add_semiring, coeff_add_semiring,
    coeff_mulLow, coeff_mulLow]
  by_cases hi : i < len
  · simp [hi]
  · rw [_root_.ite_eq_right hi, _root_.ite_eq_right hi]
    have hz : (a * b).coeff i + (c * d).coeff i = 0 := by
      rw [← coeff_add_semiring]
      exact coeff_eq_zero_of_size_le (a * b + c * d) (by omega)
    grind

/-- Clipped application is ordinary matrix application once the supplied
bound covers both output polynomials. -/
theorem applyLowWith_eq (plan : MulPlan F) (len : Nat) (m : GcdStep F)
    (a b : DensePoly F)
    (hfirst : (m.apply a b).1.size ≤ len)
    (hsecond : (m.apply a b).2.size ≤ len) :
    m.applyLowWith plan len a b = m.apply a b := by
  apply Prod.ext
  · exact add_mulLow_eq plan len m.a00 a m.a01 b hfirst
  · exact add_mulLow_eq plan len m.a10 a m.a11 b hsecond

/-- Clipped matrix composition is ordinary composition once the bound covers
all four resulting entries. -/
theorem composeLowWith_eq (plan : MulPlan F) (len : Nat) (m n : GcdStep F)
    (h00 : (m.compose n).a00.size ≤ len)
    (h01 : (m.compose n).a01.size ≤ len)
    (h10 : (m.compose n).a10.size ≤ len)
    (h11 : (m.compose n).a11.size ≤ len) :
    m.composeLowWith plan len n = m.compose n := by
  cases m with
  | mk m00 m01 m10 m11 =>
      cases n with
      | mk n00 n01 n10 n11 =>
          simp only [composeLowWith, compose] at h00 h01 h10 h11 ⊢
          rw [add_mulLow_eq plan len m00 n00 m01 n10 h00,
            add_mulLow_eq plan len m00 n01 m01 n11 h01,
            add_mulLow_eq plan len m10 n00 m11 n10 h10,
            add_mulLow_eq plan len m10 n01 m11 n11 h11]

/-- Identity leaves a pair unchanged. -/
@[simp]
theorem apply_one (a b : DensePoly F) : one.apply a b = (a, b) := by
  apply Prod.ext
  · dsimp [apply, one]
    rw [mul_comm_poly 1 a, mul_one_right_poly, zero_mul, add_zero_poly]
  · dsimp [apply, one]
    rw [zero_mul, zero_add, mul_comm_poly 1 b, mul_one_right_poly]

/-- The elementary matrix performs exactly one Euclidean update. -/
theorem apply_euclid (q a b : DensePoly F) :
    (euclid q).apply a b = (b, a - q * b) := by
  apply Prod.ext
  · dsimp [apply, euclid]
    rw [zero_mul, zero_add, mul_comm_poly 1 b, mul_one_right_poly]
  · dsimp [apply, euclid]
    rw [mul_comm_poly 1 a, mul_one_right_poly, mul_comm_poly (-q) b]
    change a + b * (0 - q) = a - q * b
    rw [mul_sub_zero_comm]
    exact (sub_eq_add_neg_poly a (q * b)).symm

/-- Matrix composition agrees with sequential application. -/
theorem apply_compose (m n : GcdStep F) (a b : DensePoly F) :
    (compose m n).apply a b = m.apply (n.apply a b).1 (n.apply a b).2 := by
  apply Prod.ext
  · dsimp [apply, compose]
    rw [mul_add_left_poly, mul_add_left_poly,
      mul_add_right_poly, mul_add_right_poly,
      ← mul_assoc_poly, ← mul_assoc_poly, ← mul_assoc_poly, ← mul_assoc_poly]
    apply ext_coeff
    intro i
    simp only [coeff_add_semiring]
    grind
  · dsimp [apply, compose]
    rw [mul_add_left_poly, mul_add_left_poly,
      mul_add_right_poly, mul_add_right_poly,
      ← mul_assoc_poly, ← mul_assoc_poly, ← mul_assoc_poly, ← mul_assoc_poly]
    apply ext_coeff
    intro i
    simp only [coeff_add_semiring]
    grind

/-- Polynomial-pair action is faithful for two-by-two transformations. -/
theorem ext_apply {m n : GcdStep F}
    (h : ∀ a b : DensePoly F, m.apply a b = n.apply a b) : m = n := by
  have hmulzero : ∀ p : DensePoly F, p * 0 = 0 := by
    intro p
    rw [mul_comm_poly, zero_mul]
  have h00 := congrArg Prod.fst (h 1 0)
  have h10 := congrArg Prod.snd (h 1 0)
  have h01 := congrArg Prod.fst (h 0 1)
  have h11 := congrArg Prod.snd (h 0 1)
  simp only [apply, mul_one_right_poly, hmulzero, add_zero_poly,
    zero_add] at h00 h10 h01 h11
  cases m
  cases n
  simp only at h00 h10 h01 h11 ⊢
  subst_vars
  rfl

/-- Identity is a right identity for transformation composition. -/
@[simp]
theorem compose_one (m : GcdStep F) : compose m one = m := by
  apply ext_apply
  intro a b
  rw [apply_compose, apply_one]

/-- Identity is a left identity for transformation composition. -/
@[simp]
theorem one_compose (m : GcdStep F) : compose one m = m := by
  apply ext_apply
  intro a b
  rw [apply_compose, apply_one]

end GcdStep

/-- Compose the Euclidean matrices represented by a quotient sequence. -/
def quotientStep (plan : MulPlan F) (qs : List (DensePoly F)) : GcdStep F :=
  qs.foldl (fun m q => GcdStep.composeWith plan (GcdStep.euclid q) m)
    GcdStep.one

/-- Execute a quotient sequence as ordinary Euclidean pair updates. -/
def runQuotients : List (DensePoly F) → DensePoly F → DensePoly F →
    DensePoly F × DensePoly F
  | [], a, b => (a, b)
  | q :: qs, a, b => runQuotients qs b (a - q * b)

private theorem apply_quotientFold (plan : MulPlan F) (qs : List (DensePoly F))
    (matrix : GcdStep F) (a b : DensePoly F) :
    (qs.foldl (fun m q => GcdStep.composeWith plan (GcdStep.euclid q) m)
      matrix).apply a b =
      runQuotients qs (matrix.apply a b).1 (matrix.apply a b).2 := by
  induction qs generalizing matrix a b with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.foldl_cons, runQuotients]
      rw [ih, GcdStep.composeWith_eq, GcdStep.apply_compose,
        GcdStep.apply_euclid]

/-- The executable quotient matrix performs exactly the corresponding
Euclidean update sequence. -/
theorem apply_quotientStep (plan : MulPlan F) (qs : List (DensePoly F))
    (a b : DensePoly F) :
    (quotientStep plan qs).apply a b = runQuotients qs a b := by
  unfold quotientStep
  rw [apply_quotientFold, GcdStep.apply_one]

/-- Running concatenated quotient blocks is sequential execution. -/
theorem runQuotients_append (qs rs : List (DensePoly F))
    (a b : DensePoly F) :
    runQuotients (qs ++ rs) a b =
      runQuotients rs (runQuotients qs a b).1 (runQuotients qs a b).2 := by
  induction qs generalizing a b with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.cons_append, runQuotients]
      exact ih b (a - q * b)

/-- Quotient matrices turn list concatenation into matrix composition. -/
theorem quotientStep_append (plan : MulPlan F)
    (qs rs : List (DensePoly F)) :
    quotientStep plan (qs ++ rs) =
      GcdStep.composeWith plan (quotientStep plan rs) (quotientStep plan qs) := by
  rw [GcdStep.composeWith_eq]
  apply GcdStep.ext_apply
  intro a b
  rw [apply_quotientStep, runQuotients_append, GcdStep.apply_compose,
    apply_quotientStep, apply_quotientStep]

/-- A singleton quotient list is its elementary Euclidean matrix. -/
theorem quotientStep_singleton (plan : MulPlan F) (q : DensePoly F) :
    quotientStep plan [q] = GcdStep.euclid q := by
  unfold quotientStep
  simp only [List.foldl_cons, List.foldl_nil]
  rw [GcdStep.composeWith_eq, GcdStep.compose_one]

private theorem quotientStep_cons (plan : MulPlan F) (q : DensePoly F)
    (qs : List (DensePoly F)) :
    quotientStep plan (q :: qs) = GcdStep.composeWith plan
      (quotientStep plan qs) (GcdStep.euclid q) := by
  simpa only [List.singleton_append, quotientStep_singleton] using
    quotientStep_append plan [q] qs

/-- A quotient sequence is an exact prefix of the established Euclidean
sequence, ending at the displayed pair. -/
inductive ExactQuotients : List (DensePoly F) → DensePoly F → DensePoly F →
    DensePoly F → DensePoly F → Prop where
  | nil (a b : DensePoly F) : ExactQuotients [] a b a b
  | cons {q r a b c d : DensePoly F} {qs : List (DensePoly F)}
      (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r))
      (tail : ExactQuotients qs b r c d) :
      ExactQuotients (q :: qs) a b c d

/-- An exact Euclidean prefix containing only steps at which the divisor is
nonzero.  This is the executable trace relation: `xgcdAux` takes precisely
these steps and stops before any attempted division by zero. -/
inductive ActiveQuotients : List (DensePoly F) → DensePoly F → DensePoly F →
    DensePoly F → DensePoly F → Prop where
  | nil (a b : DensePoly F) : ActiveQuotients [] a b a b
  | cons {q r a b c d : DensePoly F} {qs : List (DensePoly F)}
      (hb : 0 < b.size)
      (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r))
      (tail : ActiveQuotients qs b r c d) :
      ActiveQuotients (q :: qs) a b c d

/-- An exact Euclidean prefix whose divisors have positive degree and whose
quotients are nonzero.  These are precisely the steps a half-gcd block may
lift from high halves; constant-divisor finishing remains an exact boundary
division. -/
inductive ProperQuotients : List (DensePoly F) → DensePoly F → DensePoly F →
    DensePoly F → DensePoly F → Prop where
  | nil (a b : DensePoly F) : ProperQuotients [] a b a b
  | cons {q r a b c d : DensePoly F} {qs : List (DensePoly F)}
      (hq : 0 < q.size) (hb : 1 < b.size)
      (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r))
      (tail : ProperQuotients qs b r c d) :
      ProperQuotients (q :: qs) a b c d

/-- Forgetting the half-gcd degree guards leaves an ordinary exact Euclidean
prefix. -/
theorem ProperQuotients.exact {qs : List (DensePoly F)}
    {a b c d : DensePoly F} (hproper : ProperQuotients qs a b c d) :
    ExactQuotients qs a b c d := by
  induction hproper with
  | nil => exact ExactQuotients.nil _ _
  | cons hq hb hdiv tail ih => exact ExactQuotients.cons hdiv ih

/-- Proper half-gcd steps are active executable Euclidean steps. -/
theorem ProperQuotients.active {qs : List (DensePoly F)}
    {a b c d : DensePoly F} (hproper : ProperQuotients qs a b c d) :
    ActiveQuotients qs a b c d := by
  induction hproper with
  | nil => exact ActiveQuotients.nil _ _
  | cons hq hb hdiv tail ih =>
      exact ActiveQuotients.cons (by omega) hdiv ih

/-- Every active trace is an exact Euclidean prefix. -/
theorem ActiveQuotients.exact {qs : List (DensePoly F)}
    {a b c d : DensePoly F} (hactive : ActiveQuotients qs a b c d) :
    ExactQuotients qs a b c d := by
  induction hactive with
  | nil => exact ExactQuotients.nil _ _
  | cons hb hdiv tail ih => exact ExactQuotients.cons hdiv ih

/-- Concatenating adjacent proper blocks preserves their Euclidean
certificate. -/
theorem ProperQuotients.append {qs rs : List (DensePoly F)}
    {a b c d e f : DensePoly F}
    (hfirst : ProperQuotients qs a b c d)
    (hsecond : ProperQuotients rs c d e f) :
    ProperQuotients (qs ++ rs) a b e f := by
  induction hfirst with
  | nil => exact hsecond
  | cons hq hb hdiv tail ih =>
      exact ProperQuotients.cons hq hb hdiv (ih hsecond)

/-- Concatenating adjacent exact Euclidean blocks preserves exactness. -/
theorem ExactQuotients.append {qs rs : List (DensePoly F)}
    {a b c d e f : DensePoly F}
    (hfirst : ExactQuotients qs a b c d)
    (hsecond : ExactQuotients rs c d e f) :
    ExactQuotients (qs ++ rs) a b e f := by
  induction hfirst with
  | nil => exact hsecond
  | cons hdiv tail ih => exact ExactQuotients.cons hdiv (ih hsecond)

/-- Concatenating adjacent active traces preserves executability. -/
theorem ActiveQuotients.append {qs rs : List (DensePoly F)}
    {a b c d e f : DensePoly F}
    (hfirst : ActiveQuotients qs a b c d)
    (hsecond : ActiveQuotients rs c d e f) :
    ActiveQuotients (qs ++ rs) a b e f := by
  induction hfirst with
  | nil => exact hsecond
  | cons hb hdiv tail ih =>
      exact ActiveQuotients.cons hb hdiv (ih hsecond)

private theorem sub_mul_eq_remainder {a b q r : DensePoly F}
    (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r)) :
    a - q * b = r := by
  have hreconstruct :
      let qr := _root_.Hex.DensePoly.divMod a b
      qr.1 * b + qr.2 = a := by
    by_cases hb : b.size = 0
    · rw [divMod_eq_zero_self_of_size_zero a b hb]
      simp only [zero_mul, zero_add]
    · have hbpos : 0 < b.size := Nat.pos_of_ne_zero hb
      have hlead : b.leadingCoeff ≠ (0 : F) :=
        leadingCoeff_ne_zero_of_pos_size b hbpos
      apply divMod_reconstruction a b
      intro x
      rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
        Lean.Grind.Field.inv_mul_cancel hlead, Lean.Grind.Semiring.mul_one]
      exact Lean.Grind.AddCommGroup.sub_self x
  rw [hdiv] at hreconstruct
  simp only at hreconstruct
  apply ext_coeff
  intro i
  have hcoeff := congrArg (fun p : DensePoly F => p.coeff i) hreconstruct
  simp only [coeff_add_semiring, coeff_sub_ring] at hcoeff ⊢
  grind

private theorem size_le_of_coeff_zero_above {p : DensePoly F} {n : Nat}
    (hzero : ∀ i, n ≤ i → p.coeff i = 0) : p.size ≤ n := by
  by_cases hle : p.size ≤ n
  · exact hle
  · have hpos : 0 < p.size := by omega
    have hlast := coeff_last_ne_zero_of_pos_size p hpos
    exact False.elim (hlast (hzero (p.size - 1) (by omega)))

private theorem size_add_le_max (p q : DensePoly F) :
    (p + q).size ≤ max p.size q.size := by
  apply size_le_of_coeff_zero_above
  intro i hi
  rw [coeff_add_semiring,
    coeff_eq_zero_of_size_le p (Nat.le_trans (Nat.le_max_left ..) hi),
    coeff_eq_zero_of_size_le q (Nat.le_trans (Nat.le_max_right ..) hi)]
  exact Lean.Grind.Semiring.add_zero 0

private theorem size_neg_le (p : DensePoly F) : (-p).size ≤ p.size := by
  apply size_le_of_coeff_zero_above
  intro i hi
  rw [coeff_neg_ring, coeff_eq_zero_of_size_le p hi]
  exact Lean.Grind.AddCommGroup.neg_zero

private def GcdStep.SizeBound (matrix : GcdStep F) (n : Nat) : Prop :=
  matrix.a00.size ≤ n ∧ matrix.a01.size ≤ n ∧
    matrix.a10.size ≤ n ∧ matrix.a11.size ≤ n

private theorem size_add_eq_left_of_lt {p q : DensePoly F}
    (hlt : q.size < p.size) : (p + q).size = p.size := by
  have hpos : 0 < p.size := by omega
  have hlast := coeff_last_ne_zero_of_pos_size p hpos
  have hqzero : q.coeff (p.size - 1) = 0 :=
    coeff_eq_zero_of_size_le q (by omega)
  have hlower : p.size ≤ (p + q).size := by
    by_cases hle : p.size ≤ (p + q).size
    · exact hle
    · have hzero : (p + q).coeff (p.size - 1) = 0 :=
        coeff_eq_zero_of_size_le (p + q) (by omega)
      rw [coeff_add_semiring, hqzero, Lean.Grind.Semiring.add_zero] at hzero
      exact False.elim (hlast hzero)
  have hupper : (p + q).size ≤ p.size := by
    apply size_le_of_coeff_zero_above
    intro i hi
    rw [coeff_add_semiring, coeff_eq_zero_of_size_le p hi,
      coeff_eq_zero_of_size_le q (by omega)]
    exact Lean.Grind.Semiring.add_zero 0
  omega

private theorem size_shift_of_pos (k : Nat) (p : DensePoly F)
    (hp : 0 < p.size) : (shift k p).size = k + p.size := by
  rw [← monomial_one_mul_poly_eq_shift]
  have hone : (1 : F) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
  have hpne : p ≠ 0 := by
    intro hzero
    subst p
    simp only [size_zero] at hp
    omega
  rw [size_mul_field (monomial k 1) p
    (monomial_ne_zero_of_ne_zero hone) hpne,
    size_monomial_of_ne_zero hone]
  omega

private theorem size_shift (k : Nat) (p : DensePoly F) :
    (shift k p).size = if p.size = 0 then 0 else k + p.size := by
  by_cases hp : p.size = 0
  · have hpzero : p = 0 := (size_eq_zero_iff p).mp hp
    subst p
    simp [size_zero]
  · rw [_root_.ite_eq_right hp, size_shift_of_pos k p (Nat.pos_of_ne_zero hp)]

private theorem GcdStep.apply_split (matrix : GcdStep F) (k : Nat)
    (a b : DensePoly F) :
    matrix.apply a b =
      let lowPair := matrix.apply (low k a) (low k b)
      let highPair := matrix.apply (high k a) (high k b)
      (lowPair.1 + shift k highPair.1,
        lowPair.2 + shift k highPair.2) := by
  calc
    matrix.apply a b = matrix.apply
        (low k a + shift k (high k a))
        (low k b + shift k (high k b)) := by
      rw [low_add_shift_high, low_add_shift_high]
    _ = _ := by
      apply Prod.ext
      · dsimp [GcdStep.apply]
        rw [mul_add_right_poly, mul_add_right_poly, mul_shift, mul_shift]
        apply ext_coeff
        intro i
        simp only [coeff_add_semiring, coeff_shift]
        have hzero : (Zero.zero : F) = 0 := rfl
        simp only [hzero]
        split <;> grind
      · dsimp [GcdStep.apply]
        rw [mul_add_right_poly, mul_add_right_poly, mul_shift, mul_shift]
        apply ext_coeff
        intro i
        simp only [coeff_add_semiring, coeff_shift]
        have hzero : (Zero.zero : F) = 0 := rfl
        simp only [hzero]
        split <;> grind

/-- Reusing the exact high-half application preserves ordinary matrix
application semantics. -/
theorem GcdStep.applyFromHighWith_eq (plan : MulPlan F) (k : Nat)
    (matrix : GcdStep F) (a b : DensePoly F) :
    matrix.applyFromHighWith plan k
      (matrix.apply (high k a) (high k b)) a b = matrix.apply a b := by
  rw [GcdStep.applyFromHighWith, GcdStep.applyWith_eq]
  exact (GcdStep.apply_split matrix k a b).symm

private theorem size_shift_lt (k : Nat) {p q : DensePoly F}
    (hlt : p.size < q.size) : (shift k p).size < (shift k q).size := by
  rw [size_shift, size_shift]
  split <;> split <;> omega

private theorem size_reconstruct (q b r : DensePoly F)
    (hq : 0 < q.size) (hb : 0 < b.size) (hr : r.size < b.size) :
    (q * b + r).size = q.size + b.size - 1 := by
  have hqne : q ≠ 0 := by
    intro hzero
    subst q
    simp only [size_zero] at hq
    omega
  have hbne : b ≠ 0 := by
    intro hzero
    subst b
    simp only [size_zero] at hb
    omega
  rw [size_add_eq_left_of_lt (p := q * b) (q := r) (by
    rw [size_mul_field q b hqne hbne]
    omega), size_mul_field q b hqne hbne]

private theorem quotient_reconstruct {a b q r : DensePoly F}
    (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r)) :
    q * b + r = a := by
  have hsub := sub_mul_eq_remainder hdiv
  apply ext_coeff
  intro i
  have hcoeff := congrArg (fun p : DensePoly F => p.coeff i) hsub
  simp only [coeff_sub_ring, coeff_add_semiring] at hcoeff ⊢
  grind

/-- Executing an exact prefix reaches its certified terminal pair. -/
theorem ExactQuotients.run {qs : List (DensePoly F)} {a b c d : DensePoly F}
    (hexact : ExactQuotients qs a b c d) :
    runQuotients qs a b = (c, d) := by
  induction hexact with
  | nil => rfl
  | cons hdiv tail ih =>
      rw [runQuotients, sub_mul_eq_remainder hdiv]
      exact ih

/-- Consequently the composed quotient matrix reaches the same certified
terminal pair. -/
theorem ExactQuotients.apply (plan : MulPlan F)
    {qs : List (DensePoly F)} {a b c d : DensePoly F}
    (hexact : ExactQuotients qs a b c d) :
    (quotientStep plan qs).apply a b = (c, d) := by
  rw [apply_quotientStep, hexact.run]

/-- Apply a proposed quotient sequence as one composed transformation without
certifying it.  This operation is used only inside high-half prediction. -/
def applyQuotients (plan : MulPlan F) (qs : List (DensePoly F))
    (a b : DensePoly F) : DensePoly F × DensePoly F :=
  GcdStep.applyWith plan (quotientStep plan qs) a b

/-- Recursive high-half quotient prediction.  Its two recursive calls are on
half the prediction fuel.  The first predicts the leading Euclidean block;
one exact boundary division exposes the second leading block.  Predictions
are deliberately untrusted until checked on the full operands. -/
def halfGcdGuesses (plan : MulPlan F) :
    Nat → DensePoly F → DensePoly F → List (DensePoly F)
  | 0, _, _ => []
  | fuel + 1, a, b =>
      if b.size = 0 || b.size * 2 ≤ a.size then
        []
      else
        let cut := a.size / 2
        let first := halfGcdGuesses plan (fuel / 2) (high cut a) (high cut b)
        let cd := applyQuotients plan first a b
        if cd.2.size = 0 || cd.2.size * 2 ≤ a.size then
          first
        else
          let qr := divModWith plan cd.1 cd.2
          let cut₂ := cd.2.size / 2
          let second := halfGcdGuesses plan (fuel / 2)
            (high cut₂ cd.2) (high cut₂ qr.2)
          first ++ qr.1 :: second
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

/-! Divide-and-conquer matrix engine.

The quotient predictor above is useful as a small executable specification,
but consuming its quotients one at a time repeats full-size coefficient
updates.  The engine below is the actual half-gcd shape: recursive calls see
only high halves; their already-computed high applications are reused while
only the low halves are multiplied at the current recursion level. -/

/-- Reduce a Euclidean pair through roughly half of the active degree.  The
fuel is a totality guard; recursive calls receive half of it. -/
private def halfGcdMatrix (plan : MulPlan F) :
    Nat → DensePoly F → DensePoly F → GcdStep F
  | 0, _, _ => GcdStep.one
  | fuel + 1, a, b =>
      let m := a.size / 2
      if a.size ≤ 1 || a.size ≤ b.size || b.size ≤ m then
        GcdStep.one
      else
        let first := halfGcdMatrix plan (fuel / 2) (high m a) (high m b)
        let highCd := GcdStep.applyWith plan first (high m a) (high m b)
        let cd := GcdStep.applyFromHighWith plan m first highCd a b
        if cd.1.size = (shift m highCd.1).size ∧
            cd.2.size = (shift m highCd.2).size then
          if cd.2.size ≤ m then
            first
          else
            let qr := divModWith plan cd.1 cd.2
            let boundary := GcdStep.euclidComposeWith plan qr.1 first
            if qr.2.size ≤ m then
              boundary
            else
              let cut₂ := 2 * m - (cd.2.size - 1)
              let second := halfGcdMatrix plan (fuel / 2)
                (high cut₂ cd.2) (high cut₂ qr.2)
              let highEf := GcdStep.applyWith plan second
                (high cut₂ cd.2) (high cut₂ qr.2)
              let ef := GcdStep.applyFromHighWith plan cut₂ second highEf
                cd.2 qr.2
              if ef.1.size = (shift cut₂ highEf.1).size ∧
                  ef.2.size = (shift cut₂ highEf.2).size then
                GcdStep.composeLowWith plan a.size second boundary
              else
                boundary
        else
          GcdStep.one
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

/-- The completed transformation together with the terminal gcd already
available at the end of the recursive Euclidean reduction. -/
private structure GcdMatrixResult (F : Type u) [Zero F] [DecidableEq F] where
  matrix : GcdStep F
  gcd : DensePoly F

/-- Finish the Euclidean sequence by repeatedly applying half-gcd blocks and
one exact boundary division.  Carrying the terminal gcd avoids applying the
completed matrix to the original full-size inputs a second time. -/
private def gcdMatrixResult (plan : MulPlan F) :
    Nat → DensePoly F → DensePoly F → GcdMatrixResult F
  | 0, a, _ => { matrix := GcdStep.one, gcd := a }
  | fuel + 1, a, b =>
      if b.isZero then
        { matrix := GcdStep.one, gcd := a }
      else
        let block := halfGcdMatrix plan fuel a b
        let cd := GcdStep.applyWith plan block a b
        if cd.2.isZero then
          { matrix := block, gcd := cd.1 }
        else
          let qr := divModWith plan cd.1 cd.2
          let boundary := GcdStep.euclidComposeWith plan qr.1 block
          if qr.2.isZero then
            { matrix := boundary, gcd := cd.2 }
          else
            let rest := gcdMatrixResult plan fuel cd.2 qr.2
            { matrix := GcdStep.composeWith plan rest.matrix boundary
              gcd := rest.gcd }
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

/-- Internal divide-and-conquer implementation used by the public gcd and
extended-gcd projections.  The active quotient trace below certifies that its
first row is exactly the established extended-gcd coefficient pair. -/
private def xgcdMatrixWith (plan : MulPlan F) (p q : DensePoly F) : XGCDResult F :=
  let result := gcdMatrixResult plan (p.size + q.size + 1) p q
  { gcd := result.gcd, left := result.matrix.a00, right := result.matrix.a01 }

private theorem fieldCandidate_eq (plan : MulPlan F) (a b q : DensePoly F)
    (hsmall : (a - mulWith plan q b).degree?.getD 0 < b.degree?.getD 0) :
    _root_.Hex.DensePoly.divMod a b = (q, a - mulWith plan q b) := by
  let r := a - mulWith plan q b
  have hbdeg : 0 < b.degree?.getD 0 := by omega
  have hbpos : 0 < b.size := by
    rcases Nat.eq_zero_or_pos b.size with hz | hz
    · rw [(degree?_eq_none_iff b).mpr hz, Option.getD_none] at hbdeg
      omega
    · exact hz
  have hlead : b.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero_of_pos_size b hbpos
  have hcancel : ∀ x : F,
      x - (x / b.leadingCoeff) * b.leadingCoeff = 0 := by
    intro x
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.inv_mul_cancel hlead, Lean.Grind.Semiring.mul_one]
    grind
  have hexact : ∀ x : F,
      (x * b.leadingCoeff) / b.leadingCoeff = x := by
    intro x
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlead, Lean.Grind.Semiring.mul_one]
  have htop : ∀ x : F, x ≠ 0 → x * b.leadingCoeff ≠ 0 := by
    intro x hx hzero
    have h := congrArg (fun y : F => y * b.leadingCoeff⁻¹) hzero
    rw [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hlead, Lean.Grind.Semiring.mul_one] at h
    exact hx h
  have hrec : q * b + r = a := by
    apply ext_coeff
    intro i
    dsimp [r]
    rw [coeff_add_semiring, coeff_sub_ring, mulWith_eq]
    grind
  exact divMod_eq_of_reconstruction a b q r hbdeg hcancel hexact htop
    hrec hsmall

private theorem degree_getD_lt_of_size_lt {r b : DensePoly F}
    (hb : 1 < b.size) (hlt : r.size < b.size) :
    r.degree?.getD 0 < b.degree?.getD 0 := by
  rw [degree?_eq_some_of_pos_size b (by omega), Option.getD_some]
  by_cases hr : r.size = 0
  · rw [(degree?_eq_none_iff r).mpr hr, Option.getD_none]
    omega
  · have hrpos : 0 < r.size := Nat.pos_of_ne_zero hr
    rw [degree?_eq_some_of_pos_size r hrpos, Option.getD_some]
    omega

private theorem fieldCandidate_eq_of_size (plan : MulPlan F)
    (a b q : DensePoly F) (hb : 1 < b.size)
    (hsmall : (a - mulWith plan q b).size < b.size) :
    _root_.Hex.DensePoly.divMod a b = (q, a - mulWith plan q b) := by
  exact fieldCandidate_eq plan a b q (degree_getD_lt_of_size_lt hb hsmall)

private theorem fieldRemainder_size_lt {a b q r : DensePoly F}
    (hb : 1 < b.size)
    (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r)) :
    r.size < b.size := by
  have hbpos : 0 < b.size := by omega
  have hlead : b.leadingCoeff ≠ (0 : F) :=
    leadingCoeff_ne_zero_of_pos_size b hbpos
  have hcancel : ∀ x : F,
      x - (x / b.leadingCoeff) * b.leadingCoeff = 0 := by
    intro x
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.inv_mul_cancel hlead, Lean.Grind.Semiring.mul_one]
    exact Lean.Grind.AddCommGroup.sub_self x
  have hbdeg : 0 < b.degree?.getD 0 := by
    rw [degree?_eq_some_of_pos_size b hbpos, Option.getD_some]
    omega
  have hdegree := divMod_remainder_degree_lt_of_pos_degree_of_cancel
    a b hbdeg hcancel
  rw [hdiv] at hdegree
  simp only at hdegree
  by_cases hr : r.size = 0
  · omega
  · have hrpos : 0 < r.size := Nat.pos_of_ne_zero hr
    rw [degree?_eq_some_of_pos_size r hrpos, Option.getD_some,
      degree?_eq_some_of_pos_size b hbpos, Option.getD_some] at hdegree
    omega

private theorem fieldRemainder_eq_zero_of_size_one {a b q r : DensePoly F}
    (hb : b.size = 1)
    (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r)) : r = 0 := by
  have hbpos : 0 < b.size := by omega
  have hlead : b.leadingCoeff ≠ (0 : F) :=
    leadingCoeff_ne_zero_of_pos_size b hbpos
  have hcancel : ∀ x : F,
      x - (x / b.leadingCoeff) * b.leadingCoeff = 0 := by
    intro x
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.inv_mul_cancel hlead, Lean.Grind.Semiring.mul_one]
    exact Lean.Grind.AddCommGroup.sub_self x
  have hzero := divMod_remainder_eq_zero_of_degree_zero_of_cancel
    a b hb hcancel
  rw [hdiv] at hzero
  exact hzero

private theorem fieldRemainder_size_lt_of_pos {a b q r : DensePoly F}
    (hb : 0 < b.size)
    (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r)) :
    r.size < b.size := by
  by_cases hone : b.size = 1
  · rw [fieldRemainder_eq_zero_of_size_one hone hdiv, size_zero]
    exact hb
  · exact fieldRemainder_size_lt (by omega) hdiv

/-- Every coefficient polynomial in a proper quotient transformation fits
within the initial leading operand.  This is the clipping budget used when
two half-gcd blocks are composed. -/
private theorem ProperQuotients.matrixBound (plan : MulPlan F)
    {qs : List (DensePoly F)} {a b c d : DensePoly F}
    (hproper : ProperQuotients qs a b c d) (ha : 0 < a.size) :
    GcdStep.SizeBound (quotientStep plan qs) a.size := by
  induction hproper with
  | nil =>
      have hone : (1 : DensePoly F).size = 1 :=
        size_one (fun h => Lean.Grind.Field.zero_ne_one h.symm)
      simp only [quotientStep, List.foldl_nil, GcdStep.SizeBound,
        GcdStep.one, hone, size_zero]
      omega
  | @cons q r a b c d qs hq hb hdiv tail ih =>
      have hbpos : 0 < b.size := by omega
      rcases ih hbpos with ⟨h00, h01, h10, h11⟩
      have hrlt := fieldRemainder_size_lt hb hdiv
      have harec := quotient_reconstruct hdiv
      have hasize : a.size = q.size + b.size - 1 := by
        rw [← harec]
        exact size_reconstruct q b r hq hbpos hrlt
      have hnegq := size_neg_le q
      have h01prod := size_mul_le (quotientStep plan qs).a01 (-q)
      have h11prod := size_mul_le (quotientStep plan qs).a11 (-q)
      have hsecond0 := size_add_le_max (quotientStep plan qs).a00
        ((quotientStep plan qs).a01 * (-q))
      have hsecond1 := size_add_le_max (quotientStep plan qs).a10
        ((quotientStep plan qs).a11 * (-q))
      rw [quotientStep_cons, GcdStep.composeWith_eq]
      have hmulzero : ∀ p : DensePoly F, p * 0 = 0 := by
        intro p
        rw [mul_comm_poly, zero_mul]
      simp only [GcdStep.SizeBound, GcdStep.compose, GcdStep.euclid,
        hmulzero, mul_one_right_poly, zero_add]
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · omega

/-- A complete active Euclidean trace has at most one quotient per stored
coefficient of its initial divisor. -/
theorem ActiveQuotients.length_le {qs : List (DensePoly F)}
    {a b c d : DensePoly F} (hactive : ActiveQuotients qs a b c d)
    (hd : d = 0) :
    qs.length ≤ b.size := by
  induction hactive with
  | nil => exact Nat.zero_le _
  | cons hb hdiv tail ih =>
      have hrlt := fieldRemainder_size_lt_of_pos hb hdiv
      simp only [List.length_cons]
      have := ih hd
      omega

/-- Proper Euclidean blocks preserve strict ordering of consecutive
remainders. -/
theorem ProperQuotients.terminal_lt {qs : List (DensePoly F)}
    {a b c d : DensePoly F} (hproper : ProperQuotients qs a b c d)
    (hinput : b.size < a.size) : d.size < c.size := by
  induction hproper with
  | nil => exact hinput
  | cons hq hb hdiv tail ih =>
      exact ih (fieldRemainder_size_lt hb hdiv)

/-- The second remainder of a proper block never exceeds its second input. -/
theorem ProperQuotients.second_le {qs : List (DensePoly F)}
    {a b c d : DensePoly F} (hproper : ProperQuotients qs a b c d) :
    d.size ≤ b.size := by
  induction hproper with
  | nil => exact Nat.le_refl _
  | cons hq hb hdiv tail ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (fieldRemainder_size_lt hb hdiv))

private theorem fieldQuotient_size_pos {a b q r : DensePoly F}
    (hb : 1 < b.size) (hinput : b.size < a.size)
    (hdiv : _root_.Hex.DensePoly.divMod a b = (q, r)) :
    0 < q.size := by
  by_cases hq : 0 < q.size
  · exact hq
  · have hqzero : q = 0 := (size_eq_zero_iff q).mp (Nat.eq_zero_of_not_pos hq)
    have hsub := sub_mul_eq_remainder hdiv
    have hareq : a = r := by
      apply ext_coeff
      intro i
      have hcoeff := congrArg (fun p : DensePoly F => p.coeff i) hsub
      rw [hqzero, zero_mul, coeff_sub_ring] at hcoeff
      simp only [coeff_zero] at hcoeff
      grind
    have hrem := fieldRemainder_size_lt hb hdiv
    rw [← hareq] at hrem
    omega

/-- A proper quotient block computed on high halves lifts to the full inputs
once its terminal pair has the shifted high-half sizes.  The proof runs the
Euclidean recurrence backward: terminal sizes determine the preceding two
sizes, making every proposed remainder strictly smaller than its divisor and
therefore every quotient exact. -/
theorem ProperQuotients.liftHigh (plan : MulPlan F) (k : Nat)
    {qs : List (DensePoly F)} {ah bh ch dh A B C D : DensePoly F}
    (hproper : ProperQuotients qs ah bh ch dh)
    (hrun : runQuotients qs A B = (C, D))
    (hcsize : C.size = (shift k ch).size)
    (hdsize : D.size = (shift k dh).size) :
    ProperQuotients qs A B C D ∧
      A.size = (shift k ah).size ∧ B.size = (shift k bh).size := by
  induction hproper generalizing A B C D with
  | nil =>
      simp only [runQuotients] at hrun
      cases hrun
      exact ⟨ProperQuotients.nil _ _, hcsize, hdsize⟩
  | @cons q r ah bh ch dh qs hq hb hdiv tail ih =>
      let R := A - q * B
      have hrunTail : runQuotients qs B R = (C, D) := by
        simpa only [runQuotients, R] using hrun
      rcases ih hrunTail hcsize hdsize with
        ⟨tailFull, hBsize, hRsize⟩
      have hhighRem : r.size < bh.size := fieldRemainder_size_lt hb hdiv
      have hfullRem : R.size < B.size := by
        rw [hRsize, hBsize]
        exact size_shift_lt k hhighRem
      have hbhpos : 0 < bh.size := by omega
      have hBexplicit : B.size = k + bh.size := by
        rw [hBsize, size_shift_of_pos k bh hbhpos]
      have hBpos : 0 < B.size := by omega
      have hBdegree : 1 < B.size := by omega
      have hfullDivRaw := fieldCandidate_eq_of_size plan A B q hBdegree
        (by simpa only [mulWith_eq, R] using hfullRem)
      have hfullDiv : _root_.Hex.DensePoly.divMod A B = (q, R) := by
        simpa only [mulWith_eq, R] using hfullDivRaw
      have hhighSub : ah - q * bh = r := sub_mul_eq_remainder hdiv
      have hhighRec : q * bh + r = ah := by
        apply ext_coeff
        intro i
        have hcoeff := congrArg (fun p : DensePoly F => p.coeff i) hhighSub
        simp only [coeff_sub_ring, coeff_add_semiring] at hcoeff ⊢
        grind
      have hfullRec : q * B + R = A := by
        apply ext_coeff
        intro i
        simp only [R, coeff_add_semiring, coeff_sub_ring]
        grind
      have hahSize : ah.size = q.size + bh.size - 1 := by
        rw [← hhighRec]
        exact size_reconstruct q bh r hq hbhpos hhighRem
      have hASize : A.size = q.size + B.size - 1 := by
        rw [← hfullRec]
        exact size_reconstruct q B R hq hBpos hfullRem
      have hahpos : 0 < ah.size := by omega
      have hAlift : A.size = (shift k ah).size := by
        rw [size_shift_of_pos k ah hahpos]
        omega
      exact ⟨ProperQuotients.cons hq hBdegree hfullDiv tailFull,
        hAlift, hBsize⟩

/-- A matrix together with the exact proper quotient block it represents. -/
private def MatrixProper (plan : MulPlan F) (matrix : GcdStep F)
    (a b c d : DensePoly F) : Prop :=
  ∃ qs, ProperQuotients qs a b c d ∧
    matrix = quotientStep plan qs ∧ matrix.apply a b = (c, d)

/-- A matrix together with the exact, not necessarily positive-degree,
Euclidean quotient block it represents. -/
private def MatrixExact (plan : MulPlan F) (matrix : GcdStep F)
    (a b c d : DensePoly F) : Prop :=
  ∃ qs, ActiveQuotients qs a b c d ∧
    matrix = quotientStep plan qs ∧ matrix.apply a b = (c, d)

private theorem MatrixProper.one (plan : MulPlan F) (a b : DensePoly F) :
    MatrixProper plan GcdStep.one a b a b := by
  exact ⟨[], ProperQuotients.nil _ _, rfl, GcdStep.apply_one a b⟩

private theorem MatrixExact.one (plan : MulPlan F) (a b : DensePoly F) :
    MatrixExact plan GcdStep.one a b a b := by
  exact ⟨[], ActiveQuotients.nil _ _, rfl, GcdStep.apply_one a b⟩

private theorem MatrixProper.exact (plan : MulPlan F)
    {matrix : GcdStep F} {a b c d : DensePoly F}
    (hmatrix : MatrixProper plan matrix a b c d) :
    MatrixExact plan matrix a b c d := by
  rcases hmatrix with ⟨qs, hproper, hmatrix, happly⟩
  exact ⟨qs, hproper.active, hmatrix, happly⟩

private theorem MatrixProper.terminal_lt (plan : MulPlan F)
    {matrix : GcdStep F} {a b c d : DensePoly F}
    (hmatrix : MatrixProper plan matrix a b c d)
    (hinput : b.size < a.size) : d.size < c.size := by
  rcases hmatrix with ⟨qs, hproper, hmatrix, happly⟩
  exact hproper.terminal_lt hinput

private theorem MatrixProper.second_le (plan : MulPlan F)
    {matrix : GcdStep F} {a b c d : DensePoly F}
    (hmatrix : MatrixProper plan matrix a b c d) : d.size ≤ b.size := by
  rcases hmatrix with ⟨qs, hproper, hmatrix, happly⟩
  exact hproper.second_le

private theorem MatrixProper.compose (plan : MulPlan F)
    {first second : GcdStep F} {a b c d e f : DensePoly F}
    (hfirst : MatrixProper plan first a b c d)
    (hsecond : MatrixProper plan second c d e f) :
    MatrixProper plan (GcdStep.composeWith plan second first) a b e f := by
  rcases hfirst with ⟨qs, hqs, hfirstMatrix, hfirstApply⟩
  rcases hsecond with ⟨rs, hrs, hsecondMatrix, hsecondApply⟩
  refine ⟨qs ++ rs, hqs.append hrs, ?_, ?_⟩
  · rw [hfirstMatrix, hsecondMatrix]
    exact (quotientStep_append plan qs rs).symm
  · rw [GcdStep.composeWith_eq, GcdStep.apply_compose, hfirstApply,
      hsecondApply]

private theorem MatrixProper.composeLow (plan : MulPlan F)
    {first second : GcdStep F} {a b c d e f : DensePoly F}
    (hfirst : MatrixProper plan first a b c d)
    (hsecond : MatrixProper plan second c d e f)
    (ha : 0 < a.size) :
    MatrixProper plan
      (GcdStep.composeLowWith plan a.size second first) a b e f := by
  have hordinary := MatrixProper.compose plan hfirst hsecond
  rcases hordinary with ⟨qs, hproper, hmatrix, happly⟩
  have hbound := hproper.matrixBound plan ha
  have hbound' : GcdStep.SizeBound (GcdStep.compose second first) a.size := by
    rw [← GcdStep.composeWith_eq plan second first, hmatrix]
    exact hbound
  rcases hbound' with ⟨h00, h01, h10, h11⟩
  rw [GcdStep.composeLowWith_eq plan a.size second first h00 h01 h10 h11]
  exact ⟨qs, hproper, by simpa only [GcdStep.composeWith_eq] using hmatrix,
    by simpa only [GcdStep.composeWith_eq] using happly⟩

private theorem MatrixExact.compose (plan : MulPlan F)
    {first second : GcdStep F} {a b c d e f : DensePoly F}
    (hfirst : MatrixExact plan first a b c d)
    (hsecond : MatrixExact plan second c d e f) :
    MatrixExact plan (GcdStep.composeWith plan second first) a b e f := by
  rcases hfirst with ⟨qs, hqs, hfirstMatrix, hfirstApply⟩
  rcases hsecond with ⟨rs, hrs, hsecondMatrix, hsecondApply⟩
  refine ⟨qs ++ rs, hqs.append hrs, ?_, ?_⟩
  · rw [hfirstMatrix, hsecondMatrix]
    exact (quotientStep_append plan qs rs).symm
  · rw [GcdStep.composeWith_eq, GcdStep.apply_compose, hfirstApply,
      hsecondApply]

private theorem MatrixProper.euclid (plan : MulPlan F)
    {matrix : GcdStep F} {a b c d q r : DensePoly F}
    (hmatrix : MatrixProper plan matrix a b c d)
    (hq : 0 < q.size) (hd : 1 < d.size)
    (hdiv : _root_.Hex.DensePoly.divMod c d = (q, r)) :
    MatrixProper plan
      (GcdStep.euclidComposeWith plan q matrix) a b d r := by
  rw [GcdStep.euclidComposeWith_eq]
  apply hmatrix.compose
  refine ⟨[q], ProperQuotients.cons hq hd hdiv
    (ProperQuotients.nil d r), (quotientStep_singleton plan q).symm, ?_⟩
  rw [GcdStep.apply_euclid, sub_mul_eq_remainder hdiv]

private theorem MatrixExact.euclid (plan : MulPlan F)
    {matrix : GcdStep F} {a b c d q r : DensePoly F}
    (hmatrix : MatrixExact plan matrix a b c d)
    (hd : 0 < d.size)
    (hdiv : _root_.Hex.DensePoly.divMod c d = (q, r)) :
    MatrixExact plan
      (GcdStep.euclidComposeWith plan q matrix) a b d r := by
  rw [GcdStep.euclidComposeWith_eq]
  apply hmatrix.compose
  refine ⟨[q], ActiveQuotients.cons hd hdiv (ActiveQuotients.nil d r),
    (quotientStep_singleton plan q).symm, ?_⟩
  rw [GcdStep.apply_euclid, sub_mul_eq_remainder hdiv]

private theorem MatrixProper.liftHigh (plan : MulPlan F) (k : Nat)
    {matrix : GcdStep F} {ah bh ch dh A B : DensePoly F}
    (hmatrix : MatrixProper plan matrix ah bh ch dh)
    (hcsize : (matrix.apply A B).1.size =
      (shift k (matrix.apply ah bh).1).size)
    (hdsize : (matrix.apply A B).2.size =
      (shift k (matrix.apply ah bh).2).size) :
    MatrixProper plan matrix A B
      (matrix.apply A B).1 (matrix.apply A B).2 := by
  rcases hmatrix with ⟨qs, hproper, hmatrix, happly⟩
  have hrun : runQuotients qs A B = matrix.apply A B := by
    rw [← apply_quotientStep, ← hmatrix]
  have hcsize' : (matrix.apply A B).1.size = (shift k ch).size := by
    rw [hcsize, happly]
  have hdsize' : (matrix.apply A B).2.size = (shift k dh).size := by
    rw [hdsize, happly]
  have hlift := hproper.liftHigh plan k hrun hcsize' hdsize'
  exact ⟨qs, hlift.1, hmatrix, rfl⟩

private theorem halfGcdMatrix_proper (plan : MulPlan F) (fuel : Nat)
    (a b : DensePoly F) :
    ∃ c d, MatrixProper plan (halfGcdMatrix plan fuel a b) a b c d := by
  induction fuel using Nat.strongRecOn generalizing a b with
  | ind fuel ih =>
      cases fuel with
      | zero =>
          exact ⟨a, b, by
            simpa only [halfGcdMatrix] using MatrixProper.one plan a b⟩
      | succ fuel =>
          unfold halfGcdMatrix
          simp only [GcdStep.applyWith_eq, GcdStep.applyFromHighWith_eq]
          split
          · exact ⟨a, b, MatrixProper.one plan a b⟩
          · rename_i hactive
            let cut := a.size / 2
            let first := halfGcdMatrix plan (fuel / 2) (high cut a) (high cut b)
            let highCd := first.apply (high cut a) (high cut b)
            let cd := first.apply a b
            let qr := divModWith plan cd.1 cd.2
            let boundary := GcdStep.euclidComposeWith plan qr.1 first
            let cut₂ := 2 * cut - (cd.2.size - 1)
            let second := halfGcdMatrix plan (fuel / 2)
              (high cut₂ cd.2) (high cut₂ qr.2)
            let highEf := second.apply (high cut₂ cd.2) (high cut₂ qr.2)
            let ef := second.apply cd.2 qr.2
            change ∃ c d, MatrixProper plan
              (if cd.1.size = (shift cut highCd.1).size ∧
                  cd.2.size = (shift cut highCd.2).size then
                if cd.2.size ≤ cut then first
                else if qr.2.size ≤ cut then boundary
                else if ef.1.size = (shift cut₂ highEf.1).size ∧
                    ef.2.size = (shift cut₂ highEf.2).size then
                  GcdStep.composeLowWith plan a.size second boundary
                else boundary
              else GcdStep.one) a b c d
            split
            · rename_i hvalid
              rcases ih (fuel / 2) (by omega) (high cut a) (high cut b) with
                ⟨highC, highD, hfirstHigh⟩
              have hbase := hactive
              simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbase
              have hfirstFull : MatrixProper plan first a b cd.1 cd.2 := by
                exact hfirstHigh.liftHigh plan cut hvalid.1 hvalid.2
              split
              · exact ⟨cd.1, cd.2, hfirstFull⟩
              · rename_i hnotStop
                have hacut : 0 < cut := by
                  dsimp [cut]
                  omega
                have hab : b.size < a.size := by omega
                have horder : cd.2.size < cd.1.size :=
                  MatrixProper.terminal_lt plan hfirstFull hab
                have hddegree : 1 < cd.2.size := by omega
                have hdiv : _root_.Hex.DensePoly.divMod cd.1 cd.2 = qr := by
                  dsimp [qr]
                  exact (divModWith_eq plan cd.1 cd.2).symm
                have hqpos : 0 < qr.1.size :=
                  fieldQuotient_size_pos hddegree horder hdiv
                have hboundary : MatrixProper plan boundary a b cd.2 qr.2 := by
                  exact MatrixProper.euclid plan hfirstFull hqpos hddegree hdiv
                split
                · exact ⟨cd.2, qr.2, hboundary⟩
                · rename_i hcontinue
                  rcases ih (fuel / 2) (by omega)
                    (high cut₂ cd.2) (high cut₂ qr.2) with
                    ⟨highE, highF, hsecondHigh⟩
                  split
                  · rename_i hsecondValid
                    have hsecondFull :
                        MatrixProper plan second cd.2 qr.2 ef.1 ef.2 := by
                      exact hsecondHigh.liftHigh plan cut₂
                        hsecondValid.1 hsecondValid.2
                    exact ⟨ef.1, ef.2,
                      MatrixProper.composeLow plan hboundary hsecondFull (by omega)⟩
                  · exact ⟨cd.2, qr.2, hboundary⟩
            · exact ⟨a, b, MatrixProper.one plan a b⟩

private theorem gcdMatrixResult_exact (plan : MulPlan F) (fuel : Nat)
    (a b : DensePoly F) (hfuel : b.size < fuel) :
    MatrixExact plan (gcdMatrixResult plan fuel a b).matrix a b
      (gcdMatrixResult plan fuel a b).gcd 0 := by
  induction fuel generalizing a b with
  | zero => omega
  | succ fuel ih =>
      unfold gcdMatrixResult
      simp only [GcdStep.applyWith_eq]
      split
      · rename_i hbzero
        have hbsize : b.size = 0 := (isZero_eq_true_iff b).mp hbzero
        have hbeq : b = 0 := (size_eq_zero_iff b).mp hbsize
        subst b
        exact MatrixExact.one plan a 0
      · rename_i hbnonzero
        let block := halfGcdMatrix plan fuel a b
        let cd := block.apply a b
        let qr := divModWith plan cd.1 cd.2
        let boundary := GcdStep.euclidComposeWith plan qr.1 block
        let rest := gcdMatrixResult plan fuel cd.2 qr.2
        rcases halfGcdMatrix_proper plan fuel a b with
          ⟨c, d, qs, hproper, hblockMatrix, hblockApply⟩
        have hblockMatrix' : block = quotientStep plan qs := hblockMatrix
        have hblockApply' : block.apply a b = (c, d) := hblockApply
        have hblock : MatrixExact plan block a b cd.1 cd.2 := by
          refine ⟨qs, ?_, hblockMatrix', rfl⟩
          change ActiveQuotients qs a b
            (block.apply a b).1 (block.apply a b).2
          rw [hblockApply']
          exact hproper.active
        have hcdSecond : cd.2.size ≤ b.size := by
          have hdle := hproper.second_le
          change (block.apply a b).2.size ≤ b.size
          rw [hblockApply']
          exact hdle
        split
        · rename_i hcdzero
          have hcdsize : cd.2.size = 0 :=
            (isZero_eq_true_iff cd.2).mp hcdzero
          have hcdeq : cd.2 = 0 := (size_eq_zero_iff cd.2).mp hcdsize
          simpa only [hcdeq] using hblock
        · rename_i hcdnonzero
          have hcdpos : 0 < cd.2.size :=
            Nat.pos_of_ne_zero fun hzero =>
              hcdnonzero ((isZero_eq_true_iff cd.2).mpr hzero)
          have hdiv : _root_.Hex.DensePoly.divMod cd.1 cd.2 = qr := by
            dsimp [qr]
            exact (divModWith_eq plan cd.1 cd.2).symm
          have hboundary : MatrixExact plan boundary a b cd.2 qr.2 :=
            MatrixExact.euclid plan hblock hcdpos hdiv
          split
          · rename_i hqrzero
            have hqrsize : qr.2.size = 0 :=
              (isZero_eq_true_iff qr.2).mp hqrzero
            have hqreq : qr.2 = 0 := (size_eq_zero_iff qr.2).mp hqrsize
            simpa only [hqreq] using hboundary
          · rename_i hqrnonzero
            have hcddegree : 1 < cd.2.size := by
              have hcdneone : cd.2.size ≠ 1 := by
                intro hcdone
                have hqreq : qr.2 = 0 :=
                  fieldRemainder_eq_zero_of_size_one hcdone hdiv
                apply hqrnonzero
                apply (isZero_eq_true_iff qr.2).mpr
                rw [hqreq, size_zero]
              omega
            have hqrlt : qr.2.size < cd.2.size :=
              fieldRemainder_size_lt hcddegree hdiv
            have hrecFuel : qr.2.size < fuel := by omega
            have hrest := ih cd.2 qr.2 hrecFuel
            exact MatrixExact.compose plan hboundary hrest

private theorem ActiveQuotients.xgcdAux_eq
    {qs : List (DensePoly F)} {a b c d : DensePoly F}
    (hactive : ActiveQuotients qs a b c d) (hd : d = 0)
    (s₀ t₀ s₁ t₁ : DensePoly F) (fuel : Nat)
    (hlen : qs.length ≤ fuel) :
    xgcdAux a s₀ t₀ b s₁ t₁ fuel =
      { gcd := c
        left := (runQuotients qs s₀ s₁).1
        right := (runQuotients qs t₀ t₁).1 } := by
  induction qs generalizing a b c d fuel s₀ t₀ s₁ t₁ with
  | nil =>
      cases hactive
      subst b
      cases fuel with
      | zero => rfl
      | succ fuel =>
          unfold xgcdAux
          rw [show (0 : DensePoly F).isZero = true from
            (isZero_eq_true_iff 0).mpr size_zero]
          rfl
  | cons q qs ih =>
      cases hactive with
      | cons hb hdiv tail =>
          cases fuel with
          | zero => simp only [List.length_cons] at hlen; omega
          | succ fuel =>
              unfold xgcdAux
              split
              · rename_i hzero
                have hbzero := (isZero_eq_true_iff b).mp hzero
                omega
              · rw [hdiv]
                simp only [runQuotients]
                exact ih tail hd s₁ t₁ (s₀ - q * s₁) (t₀ - q * t₁) fuel (by
                simp only [List.length_cons] at hlen
                omega)

private theorem quotientStep_a00 (plan : MulPlan F)
    (qs : List (DensePoly F)) :
    (quotientStep plan qs).a00 = (runQuotients qs 1 0).1 := by
  have h := congrArg Prod.fst (apply_quotientStep plan qs 1 0)
  have hmulzero : ∀ p : DensePoly F, p * 0 = 0 := by
    intro p
    rw [mul_comm_poly, zero_mul]
  simpa only [GcdStep.apply, mul_one_right_poly, hmulzero,
    add_zero_poly] using h

private theorem quotientStep_a01 (plan : MulPlan F)
    (qs : List (DensePoly F)) :
    (quotientStep plan qs).a01 = (runQuotients qs 0 1).1 := by
  have h := congrArg Prod.fst (apply_quotientStep plan qs 0 1)
  have hmulzero : ∀ p : DensePoly F, p * 0 = 0 := by
    intro p
    rw [mul_comm_poly, zero_mul]
  simpa only [GcdStep.apply, mul_one_right_poly, hmulzero,
    zero_add] using h

private theorem xgcdMatrixWith_eq (plan : MulPlan F)
    (p q : DensePoly F) : xgcdMatrixWith plan p q = xgcd p q := by
  unfold xgcdMatrixWith xgcd
  let fuel := p.size + q.size + 1
  let result := gcdMatrixResult plan fuel p q
  change XGCDResult.mk result.gcd result.matrix.a00 result.matrix.a01 =
    xgcdAux p 1 0 q 0 1 fuel
  rcases gcdMatrixResult_exact plan fuel p q (by dsimp [fuel]; omega) with
    ⟨qs, hactive, hmatrix, happly⟩
  have hmatrix' : result.matrix = quotientStep plan qs := hmatrix
  have hlen : qs.length ≤ fuel := by
    have htrace := hactive.length_le rfl
    dsimp [fuel]
    omega
  have hx := hactive.xgcdAux_eq rfl 1 0 0 1 fuel hlen
  rw [hx]
  rw [hmatrix', quotientStep_a00, quotientStep_a01]

/-- Extended Euclidean recursion with a queue of high-half quotient
predictions.  Each recursive call consumes one ordinary Euclidean step, so
the fuel convention is identical to `DensePoly.xgcdAux`. -/
def xgcdAuxWith (plan : MulPlan F) :
    List (DensePoly F) →
      DensePoly F → DensePoly F → DensePoly F →
      DensePoly F → DensePoly F → DensePoly F → Nat → XGCDResult F
  | _, r₀, s₀, t₀, _, _, _, 0 =>
      { gcd := r₀, left := s₀, right := t₀ }
  | queued, r₀, s₀, t₀, r₁, s₁, t₁, fuel + 1 =>
      if r₁.isZero then
        { gcd := r₀, left := s₀, right := t₀ }
      else
        let guesses := if queued.isEmpty then
          halfGcdGuesses plan (max r₀.size r₁.size) r₀ r₁
        else queued
        match guesses with
        | q :: rest =>
            let r := r₀ - mulWith plan q r₁
            if r.degree?.getD 0 < r₁.degree?.getD 0 then
              xgcdAuxWith plan rest
                r₁ s₁ t₁ r
                (s₀ - mulWith plan q s₁)
                (t₀ - mulWith plan q t₁) fuel
            else
              let qr := divModWith plan r₀ r₁
              xgcdAuxWith plan []
                r₁ s₁ t₁ qr.2
                (s₀ - mulWith plan qr.1 s₁)
                (t₀ - mulWith plan qr.1 t₁) fuel
        | [] =>
            let qr := divModWith plan r₀ r₁
            xgcdAuxWith plan []
              r₁ s₁ t₁ qr.2
              (s₀ - mulWith plan qr.1 s₁)
              (t₀ - mulWith plan qr.1 t₁) fuel

/-- Plan-driven half-gcd extended gcd. -/
def xgcdWith (plan : MulPlan F) (p q : DensePoly F) : XGCDResult F :=
  xgcdMatrixWith plan p q

/-- Gcd projection of the half-gcd engine. -/
def gcdWith (plan : MulPlan F) (p q : DensePoly F) : DensePoly F :=
  (xgcdWith plan p q).gcd

/-- One-sided result projection of the half-gcd engine. -/
def xgcdLeftWith (plan : MulPlan F) (p q : DensePoly F) : XGCDLeftResult F :=
  let r := xgcdWith plan p q
  { gcd := r.gcd, left := r.left }

private theorem xgcdAuxWith_eq (plan : MulPlan F)
    (queued : List (DensePoly F))
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly F) (fuel : Nat) :
    xgcdAuxWith plan queued r₀ s₀ t₀ r₁ s₁ t₁ fuel =
      xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel := by
  induction fuel generalizing queued r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero => rfl
  | succ fuel ih =>
      unfold xgcdAuxWith xgcdAux
      split
      · rfl
      · rename_i hr
        dsimp only
        split
        · rename_i q rest hguesses
          split
          · rename_i hsmall
            have hqr := fieldCandidate_eq plan r₀ r₁ q hsmall
            rw [hqr]
            simpa only [mulWith_eq] using
              ih rest r₁ s₁ t₁ (r₀ - mulWith plan q r₁)
                (s₀ - mulWith plan q s₁) (t₀ - mulWith plan q t₁)
          · rename_i hnot_small
            rw [divModWith_eq]
            simpa only [mulWith_eq] using
              ih [] r₁ s₁ t₁ (_root_.Hex.DensePoly.divMod r₀ r₁).2
                (s₀ - mulWith plan (_root_.Hex.DensePoly.divMod r₀ r₁).1 s₁)
                (t₀ - mulWith plan (_root_.Hex.DensePoly.divMod r₀ r₁).1 t₁)
        · rw [divModWith_eq]
          simpa only [mulWith_eq] using
            ih [] r₁ s₁ t₁ (_root_.Hex.DensePoly.divMod r₀ r₁).2
              (s₀ - mulWith plan (_root_.Hex.DensePoly.divMod r₀ r₁).1 s₁)
              (t₀ - mulWith plan (_root_.Hex.DensePoly.divMod r₀ r₁).1 t₁)

/-- Half-gcd returns exactly the established extended-gcd result, including
the raw gcd scaling and both Bezout coefficients. -/
theorem xgcdWith_eq (plan : MulPlan F) (p q : DensePoly F) :
    xgcdWith plan p q = xgcd p q := by
  exact xgcdMatrixWith_eq plan p q

/-- Half-gcd returns exactly the established gcd. -/
theorem gcdWith_eq (plan : MulPlan F) (p q : DensePoly F) :
    gcdWith plan p q = gcd p q := by
  rw [gcdWith, xgcdWith_eq, xgcd_gcd_eq_gcd]

/-- The one-sided half-gcd projection agrees exactly with the established
one-sided extended gcd. -/
theorem xgcdLeftWith_eq (plan : MulPlan F) (p q : DensePoly F) :
    xgcdLeftWith plan p q = xgcdLeft p q := by
  unfold xgcdLeftWith
  rw [xgcdWith_eq]
  have hg := xgcdLeft_gcd_eq_xgcd (R := F) p q
  have hl := xgcdLeft_left_eq_xgcd (R := F) p q
  cases hleft : xgcdLeft p q with
  | mk g l =>
      cases hfull : xgcd p q with
      | mk g' l' r' =>
          rw [hleft, hfull] at hg hl
          simp only at hg hl ⊢
          subst g'
          subst l'
          rfl

end Hex.DensePoly
