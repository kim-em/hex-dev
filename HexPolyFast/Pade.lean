/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.HalfGcd
public import HexPoly.Monic

public section
set_option backward.proofsInPublic true

/-!
Padé approximation through the fast half-gcd transformation.

Only the first `m + n + 1` coefficients of the supplied series prefix affect
an approximant.  Consequently the API accepts prefixes of arbitrary precision:
longer prefixes are truncated and absent coefficients of shorter prefixes are
zero.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {F : Type u} [DecidableEq F] [Lean.Grind.Field F]

/-- A homogeneous Padé approximant of numerator degree at most `m` and
denominator degree at most `n`.  A nonzero denominator is stronger than the
nontrivial-pair condition and is what the half-gcd construction supplies. -/
structure PadeApproximant {k : Nat} (s : TSeries F k) (m n : Nat) where
  p : DensePoly F
  q : DensePoly F
  p_size : p.size ≤ m + 1
  q_size : q.size ≤ n + 1
  q_ne : q ≠ 0
  congruent : ∀ i, i < m + n + 1 →
    (q * polyOfSeries s - p).coeff i = 0

theorem size_low_le (len : Nat) (p : DensePoly F) :
    (low len p).size ≤ len := by
  unfold low
  simpa using size_ofList_le ((List.range len).map p.coeff)

theorem low_eq_self_of_size_le {len : Nat} {p : DensePoly F}
    (hsize : p.size ≤ len) : low len p = p := by
  apply ext_coeff
  intro i
  rw [coeff_low]
  by_cases hi : i < len
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    exact (coeff_eq_zero_of_size_le p (by omega)).symm

private theorem low_one_eq_C (p : DensePoly F) :
    low 1 p = C (p.coeff 0) := by
  apply ext_coeff
  intro i
  rw [coeff_low, coeff_C]
  by_cases hi : i = 0
  · subst i
    simp only [Nat.zero_lt_one, ite_true]
  · have hnot : ¬i < 1 := by omega
    simp only [hi, hnot, ite_false]
    rfl

private theorem coeff_zero_mul (p q : DensePoly F) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  have h := coeff_low_mul_low 1 p q 0 (by omega)
  rw [low_one_eq_C, low_one_eq_C, C_mul_C, coeff_C] at h
  simpa only [ite_true] using h.symm

private theorem eq_shift_high_of_coeff_zero (len : Nat) (p : DensePoly F)
    (hcoeff : ∀ i, i < len → p.coeff i = 0) :
    p = shift len (high len p) := by
  have hlow : low len p = 0 := by
    apply ext_coeff
    intro i
    rw [coeff_low, coeff_zero]
    by_cases hi : i < len
    · rw [ite_eq_left hi, hcoeff i hi]
    · rw [ite_eq_right hi]
  have hsplit := low_add_shift_high len p
  rw [hlow, zero_add] at hsplit
  exact hsplit.symm

/-- The terminal half-gcd boundary underlying Padé construction. -/
@[expose]
def padeBoundary (plan : MulPlan F) {k : Nat} (s : TSeries F k)
    (m n : Nat) : GcdBoundaryResult F :=
  let precision := m + n + 1
  let series := low precision (polyOfSeries s)
  let modulus : DensePoly F := monomial precision 1
  reduceToMatrixResult plan (m + 1) series.size modulus series

/-- Compute a homogeneous Padé approximant with the selected multiplication
plan.  The half-gcd prefix stops precisely when the remainder crosses the
numerator-size boundary. -/
@[expose]
def padeHomogeneous (plan : MulPlan F) {k : Nat} (s : TSeries F k)
    (m n : Nat) : PadeApproximant s m n := by
  let precision := m + n + 1
  let series := low precision (polyOfSeries s)
  let modulus : DensePoly F := monomial precision 1
  let result := padeBoundary plan s m n
  have hone : (1 : F) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
  have hmodulus : modulus.size = precision + 1 := by
    dsimp [modulus]
    exact size_monomial_of_ne_zero hone
  have hseries : series.size ≤ precision := by
    dsimp [series]
    exact size_low_le precision (polyOfSeries s)
  have hinput : series.size < modulus.size := by omega
  have hbound : 0 < m + 1 := by omega
  have hbelow : m + 1 < modulus.size := by omega
  have hspec := reduceToMatrixResult_spec plan (m + 1) modulus series
    hbound hinput hbelow
  change result.matrix.apply modulus series = (result.first, result.second) ∧
    result.second.size ≤ m + 1 ∧ m + 1 < result.first.size ∧
    0 < result.matrix.a11.size ∧
      result.matrix.a11.size + result.first.size = modulus.size + 1 at hspec
  refine
    { p := result.second
      q := result.matrix.a11
      p_size := hspec.2.1
      q_size := ?_
      q_ne := ?_
      congruent := ?_ }
  · omega
  · intro hzero
    have hsizeZero : result.matrix.a11.size = 0 := by
      rw [hzero, size_zero]
    omega
  · intro i hi
    have hqSize : result.matrix.a11.size ≤ precision := by omega
    have hqLow : low precision result.matrix.a11 = result.matrix.a11 :=
      low_eq_self_of_size_le hqSize
    have hproduct :
        (result.matrix.a11 * series).coeff i =
          (result.matrix.a11 * polyOfSeries s).coeff i := by
      change
        (result.matrix.a11 * low precision (polyOfSeries s)).coeff i =
          (result.matrix.a11 * polyOfSeries s).coeff i
      calc
        _ = (low precision result.matrix.a11 *
              low precision (polyOfSeries s)).coeff i := by rw [hqLow]
        _ = _ := coeff_low_mul_low precision result.matrix.a11
          (polyOfSeries s) i hi
    have hmodCoeff :
        (result.matrix.a10 * modulus).coeff i = 0 := by
      dsimp [modulus]
      rw [mul_comm_poly, monomial_one_mul_poly_eq_shift, coeff_shift,
        ite_eq_left hi]
      rfl
    have hsecond := congrArg Prod.snd hspec.1
    rw [GcdStep.apply_snd] at hsecond
    have hcoeff := congrArg (fun p : DensePoly F => p.coeff i) hsecond
    rw [coeff_add_semiring, hmodCoeff] at hcoeff
    rw [coeff_sub_ring, ← hproduct]
    grind

/-- The homogeneous denominator is the lower-row continuant at the Padé
boundary. -/
theorem padeHomogeneous_q (plan : MulPlan F) {k : Nat} (s : TSeries F k)
    (m n : Nat) :
    (padeHomogeneous plan s m n).q = (padeBoundary plan s m n).matrix.a11 :=
  rfl

/-- A Padé approximant whose denominator is normalized at the origin. -/
structure NormalizedPade {k : Nat} (s : TSeries F k) (m n : Nat) where
  p : DensePoly F
  q : DensePoly F
  p_size : p.size ≤ m + 1
  q_size : q.size ≤ n + 1
  q_zero : q.coeff 0 = 1
  congruent : ∀ i, i < m + n + 1 →
    (q * polyOfSeries s - p).coeff i = 0

private theorem homogeneous_unit (plan : MulPlan F) {k : Nat}
    (s : TSeries F k) (m n : Nat) (candidate : NormalizedPade s m n) :
    (padeHomogeneous plan s m n).q.coeff 0 ≠ 0 := by
  let precision := m + n + 1
  let series := low precision (polyOfSeries s)
  let modulus : DensePoly F := monomial precision 1
  let result := padeBoundary plan s m n
  have hone : (1 : F) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
  have hmodulus : modulus.size = precision + 1 := by
    dsimp [modulus]
    exact size_monomial_of_ne_zero hone
  have hseries : series.size ≤ precision := by
    dsimp [series]
    exact size_low_le precision (polyOfSeries s)
  have hinput : series.size < modulus.size := by omega
  have hbound : 0 < m + 1 := by omega
  have hbelow : m + 1 < modulus.size := by omega
  have hspec := reduceToMatrixResult_spec plan (m + 1) modulus series
    hbound hinput hbelow
  change result.matrix.apply modulus series = (result.first, result.second) ∧
    result.second.size ≤ m + 1 ∧ m + 1 < result.first.size ∧
    0 < result.matrix.a11.size ∧
      result.matrix.a11.size + result.first.size = modulus.size + 1 at hspec
  have hdet := reduceToMatrixResult_det plan (m + 1) series.size
    modulus series hbound hinput
  change result.matrix.det = 1 ∨ result.matrix.det = -1 at hdet
  rw [padeHomogeneous_q]
  intro hqZero
  have hqSize : result.matrix.a11.size ≤ n + 1 := by omega
  have hcandidateProduct : ∀ i, i < precision →
      (candidate.q * series).coeff i =
        (candidate.q * polyOfSeries s).coeff i := by
    intro i hi
    have hcandidateSize : candidate.q.size ≤ precision := by
      dsimp [precision]
      have hsize := candidate.q_size
      omega
    have hcandidateLow : low precision candidate.q = candidate.q :=
      low_eq_self_of_size_le hcandidateSize
    change
      (candidate.q * low precision (polyOfSeries s)).coeff i =
        (candidate.q * polyOfSeries s).coeff i
    calc
      _ = (low precision candidate.q *
            low precision (polyOfSeries s)).coeff i := by
          rw [hcandidateLow]
      _ = _ := coeff_low_mul_low precision candidate.q
        (polyOfSeries s) i hi
  let discrepancy := candidate.q * series - candidate.p
  have hdiscrepancy : ∀ i, i < precision → discrepancy.coeff i = 0 := by
    intro i hi
    dsimp [discrepancy]
    rw [coeff_sub_ring, hcandidateProduct i hi]
    have hcongruent := candidate.congruent i hi
    rw [coeff_sub_ring] at hcongruent
    exact hcongruent
  let quotient := high precision discrepancy
  have hexact : discrepancy = modulus * quotient := by
    calc
      discrepancy = shift precision quotient :=
        eq_shift_high_of_coeff_zero precision discrepancy hdiscrepancy
      _ = modulus * quotient := by
        dsimp [modulus]
        exact (monomial_one_mul_poly_eq_shift precision quotient).symm
  have hsecond := congrArg Prod.snd hspec.1
  rw [GcdStep.apply_snd] at hsecond
  change result.matrix.a10 * modulus + result.matrix.a11 * series =
    result.second at hsecond
  let obstruction :=
    candidate.q * result.matrix.a10 + result.matrix.a11 * quotient
  have hfactor :
      candidate.q * result.second - result.matrix.a11 * candidate.p =
        modulus * obstruction := by
    dsimp [obstruction]
    rw [← hsecond]
    dsimp [discrepancy] at hexact
    grind
  have hcrossSize :
      (candidate.q * result.second).size ≤ precision := by
    apply Nat.le_trans (size_mul_le candidate.q result.second)
    have hq := candidate.q_size
    have hp := hspec.2.1
    dsimp [precision]
    omega
  have hotherSize :
      (result.matrix.a11 * candidate.p).size ≤ precision := by
    apply Nat.le_trans (size_mul_le result.matrix.a11 candidate.p)
    have hp := candidate.p_size
    dsimp [precision]
    omega
  have hcrossZero :
      candidate.q * result.second - result.matrix.a11 * candidate.p = 0 := by
    apply ext_coeff
    intro i
    rw [coeff_zero]
    by_cases hi : i < precision
    · rw [hfactor]
      dsimp [modulus]
      rw [monomial_one_mul_poly_eq_shift, coeff_shift,
        ite_eq_left hi]
      rfl
    · rw [coeff_sub_ring,
        coeff_eq_zero_of_size_le (candidate.q * result.second) (by omega),
        coeff_eq_zero_of_size_le (result.matrix.a11 * candidate.p) (by omega)]
      grind
  have hobstructionProduct : modulus * obstruction = 0 := by
    rw [← hfactor, hcrossZero]
  have hmodulusNe : modulus ≠ 0 := by
    intro hzero
    have hz := congrArg DensePoly.size hzero
    rw [hmodulus, size_zero] at hz
    omega
  have hobstruction : obstruction = 0 := by
    by_cases hzero : obstruction = 0
    · exact hzero
    · have hsize := size_mul_field modulus obstruction hmodulusNe hzero
      rw [hobstructionProduct, size_zero] at hsize
      have hpositive : 0 < obstruction.size := by
        apply Nat.pos_of_ne_zero
        intro hsizeZero
        exact hzero ((size_eq_zero_iff obstruction).mp hsizeZero)
      omega
  have ha10Zero : result.matrix.a10.coeff 0 = 0 := by
    have hcoeff := congrArg (fun p : DensePoly F => p.coeff 0) hobstruction
    dsimp [obstruction] at hcoeff
    rw [coeff_add_semiring, coeff_zero_mul, coeff_zero_mul,
      candidate.q_zero, hqZero, coeff_zero] at hcoeff
    grind
  have hdetZero : result.matrix.det.coeff 0 = 0 := by
    rw [GcdStep.det, coeff_sub_ring, coeff_zero_mul, coeff_zero_mul,
      hqZero, ha10Zero]
    grind
  rcases hdet with hdet | hdet
  · rw [hdet, coeff_ofNat] at hdetZero
    simp only [ite_true] at hdetZero
    exact Lean.Grind.Field.zero_ne_one hdetZero.symm
  · rw [hdet, coeff_neg_ring, coeff_ofNat] at hdetZero
    simp only [ite_true] at hdetZero
    grind

def PadeApproximant.normalize {k : Nat} {s : TSeries F k} {m n : Nat}
    (approx : PadeApproximant s m n) (hc : approx.q.coeff 0 ≠ 0) :
    NormalizedPade s m n := by
  let c := approx.q.coeff 0
  have hinv : c⁻¹ ≠ 0 := by
    intro hzero
    have hcancel := Lean.Grind.Field.inv_mul_cancel hc
    rw [hzero] at hcancel
    grind
  refine
    { p := scale c⁻¹ approx.p
      q := scale c⁻¹ approx.q
      p_size := ?_
      q_size := ?_
      q_zero := ?_
      congruent := ?_ }
  · rw [size_scale_field hinv]
    exact approx.p_size
  · rw [size_scale_field hinv]
    exact approx.q_size
  · rw [coeff_scale_semiring]
    exact Lean.Grind.Field.inv_mul_cancel hc
  · intro i hi
    have hcongruent := approx.congruent i hi
    rw [coeff_sub_ring] at hcongruent
    rw [← scale_mul, coeff_sub_ring, coeff_scale_semiring,
      coeff_scale_semiring]
    grind

/-- Compute the normalized rational-series Padé form when its denominator
can be made a unit at the origin. -/
def pade? (plan : MulPlan F) {k : Nat} (s : TSeries F k)
    (m n : Nat) : Option (NormalizedPade s m n) :=
  let approx := padeHomogeneous plan s m n
  if hc : approx.q.coeff 0 = 0 then none
  else some (approx.normalize hc)

/-- Normalized Padé construction fails exactly when no denominator with
constant coefficient one satisfies the requested bounds and congruence. -/
theorem pade?_eq_none_iff (plan : MulPlan F) {k : Nat} (s : TSeries F k)
    (m n : Nat) :
    pade? plan s m n = none ↔ ¬Nonempty (NormalizedPade s m n) := by
  constructor
  · intro hnone hexists
    rcases hexists with ⟨candidate⟩
    let approx := padeHomogeneous plan s m n
    change (if hc : approx.q.coeff 0 = 0 then none
      else some (approx.normalize hc)) = none at hnone
    split at hnone
    · rename_i hzero
      exact (homogeneous_unit plan s m n candidate) (by
        simpa only [approx] using hzero)
    · simp only [reduceCtorEq] at hnone
  · intro hnone
    let approx := padeHomogeneous plan s m n
    change (if hc : approx.q.coeff 0 = 0 then none
      else some (approx.normalize hc)) = none
    split
    · rfl
    · rename_i hc
      exact False.elim (hnone ⟨approx.normalize hc⟩)

end Hex.DensePoly
