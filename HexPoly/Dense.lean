import Std

/-!
Dense array-backed polynomials with the invariant that the stored coefficient array has no
trailing zeros. This normalization makes structural equality coincide with semantic equality.
-/
namespace Hex

universe u

/-- `DensePolyNormalized coeffs` means either `coeffs` is empty or its last coefficient is
nonzero, so the array has no trailing zeros. -/
def DensePolyNormalized {R : Type u} [Zero R] [DecidableEq R] (coeffs : Array R) : Prop :=
  coeffs.size = 0 ∨ coeffs.back? ≠ some (Zero.zero : R)

/-- Dense polynomials store coefficients in ascending degree order, with index `i` holding the
coefficient of `x^i`. -/
structure DensePoly (R : Type u) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : DensePolyNormalized coeffs

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

instance : DecidableEq (DensePoly R) := by
  intro a b
  match decEq a.coeffs b.coeffs with
  | isTrue h =>
      exact isTrue (by
        cases a
        cases b
        cases h
        simp)
  | isFalse h =>
      exact isFalse (by
        intro hab
        apply h
        exact congrArg DensePoly.coeffs hab)

/-- Remove trailing zeros from a coefficient list without disturbing the remaining order. -/
def trimTrailingZerosList : List R → List R
  | [] => []
  | a :: as =>
      let trimmed := trimTrailingZerosList as
      if trimmed = [] ∧ a = (Zero.zero : R) then [] else a :: trimmed

/-- Trimming preserves the value at every index, including indices beyond the trimmed length
where both sides default to `0`. -/
theorem trimTrailingZerosList_getD (coeffs : List R) (n : Nat) :
    (trimTrailingZerosList coeffs).getD n (Zero.zero : R) =
      coeffs.getD n (Zero.zero : R) := by
  induction coeffs generalizing n with
  | nil =>
      simp [trimTrailingZerosList]
  | cons a as ih =>
      cases n with
      | zero =>
          by_cases htrim : trimTrailingZerosList as = [] ∧ a = (Zero.zero : R)
          · simp [trimTrailingZerosList, htrim]
          · simp [trimTrailingZerosList, htrim]
      | succ n =>
          by_cases htrim : trimTrailingZerosList as = [] ∧ a = (Zero.zero : R)
          · have htail : trimTrailingZerosList as = [] := htrim.1
            have hcoeff := ih n
            simp [trimTrailingZerosList, htrim]
            change Zero.zero = as.getD n (Zero.zero : R)
            rw [← hcoeff, htail]
            simp
          · simpa [trimTrailingZerosList, htrim] using ih n

theorem trimTrailingZerosList_length_le (coeffs : List R) :
    (trimTrailingZerosList coeffs).length ≤ coeffs.length := by
  induction coeffs with
  | nil =>
      simp [trimTrailingZerosList]
  | cons a as ih =>
      by_cases htrim : trimTrailingZerosList as = [] ∧ a = (Zero.zero : R)
      · simp [trimTrailingZerosList, htrim]
      · simp [trimTrailingZerosList, htrim]
        omega

/-- Trimming leaves the list either empty or with a nonzero last entry; this is the list-level
form of the `DensePolyNormalized` invariant. -/
theorem trimTrailingZerosList_normalized (coeffs : List R) :
    trimTrailingZerosList coeffs = [] ∨
      (trimTrailingZerosList coeffs).getLast? ≠ some (Zero.zero : R) := by
  induction coeffs with
  | nil =>
      simp [trimTrailingZerosList]
  | cons a as ih =>
      by_cases htrim : trimTrailingZerosList as = [] ∧ a = (Zero.zero : R)
      · simp [trimTrailingZerosList, htrim]
      · cases htail : trimTrailingZerosList as with
        | nil =>
            right
            intro hlast
            have ha_ne : a ≠ (Zero.zero : R) := by
              intro ha
              exact htrim ⟨htail, ha⟩
            simp [trimTrailingZerosList, htail, ha_ne] at hlast
        | cons b bs =>
            right
            intro hlast
            rcases ih with has_empty | has_last
            · simp [htail] at has_empty
            · apply has_last
              simpa [trimTrailingZerosList, htrim, htail] using hlast

/-- Normalize a coefficient array by discarding all trailing zeros. -/
def trimTrailingZeros (coeffs : Array R) : Array R :=
  (trimTrailingZerosList coeffs.toList).toArray

/-- Build a dense polynomial from a raw coefficient array by normalizing away trailing zeros. -/
def ofCoeffs (coeffs : Array R) : DensePoly R :=
  { coeffs := trimTrailingZeros coeffs
    normalized := by
      unfold trimTrailingZeros DensePolyNormalized
      simpa using trimTrailingZerosList_normalized (R := R) coeffs.toList }

/-- The zero polynomial. -/
def zero : DensePoly R :=
  ofCoeffs #[]

instance : Zero (DensePoly R) where
  zero := zero

/-- Build a dense polynomial from a coefficient list by normalizing away trailing zeros. -/
def ofList (coeffs : List R) : DensePoly R :=
  ofCoeffs coeffs.toArray

/-- Build the constant polynomial with value `c`. The zero constant collapses to the zero
polynomial. -/
def C (c : R) : DensePoly R :=
  ofCoeffs #[c]

/-- Build the monomial `c * x^n`. The zero coefficient collapses to the zero polynomial. -/
def monomial (n : Nat) (c : R) : DensePoly R :=
  if hc : c = (Zero.zero : R) then 0 else
    { coeffs := (Array.replicate n (Zero.zero : R)).push c
      normalized := by
        right
        intro hback
        have hlast :
            ((Array.replicate n (Zero.zero : R)).push c).back? = some c := by
          simp
        rw [hlast] at hback
        exact hc (Option.some.inj hback) }

/-- The number of stored coefficients. For a normalized polynomial this is one more than the
degree, except for the zero polynomial where it is `0`. -/
def size (p : DensePoly R) : Nat :=
  p.coeffs.size

theorem size_ofCoeffs_le (coeffs : Array R) :
    (ofCoeffs coeffs).size ≤ coeffs.size := by
  unfold ofCoeffs size trimTrailingZeros
  simpa using trimTrailingZerosList_length_le (R := R) coeffs.toList

/-- `true` exactly when the polynomial is zero. -/
def isZero (p : DensePoly R) : Bool :=
  p.coeffs.isEmpty

/-- The coefficient of `x^n`, defaulting to `0` when `n` is out of range. -/
def coeff (p : DensePoly R) (n : Nat) : R :=
  p.coeffs.getD n (Zero.zero : R)

/-- Coefficient of `ofCoeffs arr` agrees with `arr.getD _ 0`: trimming trailing zeros does not
change the value at any index. -/
@[simp] theorem coeff_ofCoeffs (coeffs : Array R) (n : Nat) :
    (ofCoeffs coeffs).coeff n = coeffs.getD n (Zero.zero : R) := by
  unfold ofCoeffs coeff trimTrailingZeros
  simpa using trimTrailingZerosList_getD (R := R) coeffs.toList n

/-- Characterising lemma for the constant polynomial: its coefficient is `c` at degree `0`,
zero elsewhere. -/
@[simp] theorem coeff_C (c : R) (n : Nat) :
    (C c).coeff n = if n = 0 then c else (Zero.zero : R) := by
  rw [C, coeff_ofCoeffs]
  cases n with
  | zero =>
      simp
  | succ n =>
      simp

/-- Characterising lemma for monomials: `monomial n c` has coefficient `c` at degree `n` and zero
elsewhere, even when `c = 0` (in which case the polynomial is zero and every coefficient is `0`). -/
theorem coeff_monomial (n : Nat) (c : R) (i : Nat) :
    (monomial n c).coeff i = if i = n then c else (Zero.zero : R) := by
  unfold monomial
  by_cases hc : c = (Zero.zero : R)
  · rw [dif_pos hc]
    change (0 : DensePoly R).coeff i = if i = n then c else (Zero.zero : R)
    by_cases hi : i = n
    · subst i
      rw [if_pos rfl, hc]
      change (#[] : Array R).getD n (Zero.zero : R) = Zero.zero
      simp [Array.getD]
    · change (#[] : Array R).getD i (Zero.zero : R) = if i = n then c else Zero.zero
      simp [Array.getD, hi]
  · simp [hc, coeff, Array.getD]
    by_cases hi : i = n
    · subst i
      rw [dif_pos (Nat.lt_succ_self n)]
      rw [show
          ((Array.replicate n (Zero.zero : R)).push c)[n] = c by
            simpa using
              (Array.getElem_push_eq (xs := Array.replicate n (Zero.zero : R)) (x := c))]
      simp
    · by_cases hlt : i < n
      · have hrep : i < (Array.replicate n (Zero.zero : R)).size := by
          simpa using hlt
        have hpush : i < n + 1 := by omega
        rw [dif_pos hpush]
        rw [Array.getElem_push_lt hrep]
        simp [hi]
      · have hnle : n < i := by omega
        have hpush_not : ¬ i < n + 1 := by omega
        rw [dif_neg hpush_not]
        simp [hi]

/-- List-level companion to `coeff_ofCoeffs`: building a polynomial from a coefficient list and
reading back at index `n` recovers the original list entry (defaulting to `0` past the end). -/
@[simp] theorem coeff_ofCoeffs_list (coeffs : List R) (n : Nat) :
    (ofCoeffs coeffs.toArray).coeff n = coeffs.getD n (Zero.zero : R) := by
  simp [coeff_ofCoeffs]

/-- Extensionality for normalized dense polynomials when the stored sizes agree. -/
theorem ext_of_size_eq {p q : DensePoly R}
    (hsize : p.size = q.size)
    (hcoeff : ∀ i, i < p.size → p.coeff i = q.coeff i) :
    p = q := by
  cases p with
  | mk pc pn =>
    cases q with
    | mk qc qn =>
      congr
      apply Array.ext hsize
      intro i hi₁ hi₂
      calc
        pc[i] = pc.getD i (Zero.zero : R) := Array.getElem_eq_getD (Zero.zero : R)
        _ = qc.getD i (Zero.zero : R) := hcoeff i hi₁
        _ = qc[i] := (Array.getElem_eq_getD (Zero.zero : R)).symm

/-- Coefficients outside the stored support are zero. -/
theorem coeff_eq_zero_of_size_le (p : DensePoly R) {i : Nat} (h : p.size ≤ i) :
    p.coeff i = (Zero.zero : R) := by
  unfold coeff Array.getD
  have hcoeffs : p.coeffs.size ≤ i := by
    simpa [size] using h
  rw [dif_neg (Nat.not_lt.mpr hcoeffs)]

/-- The last stored coefficient of a nonzero normalized dense polynomial is nonzero. -/
theorem coeff_last_ne_zero_of_pos_size (p : DensePoly R) (hpos : 0 < p.size) :
    p.coeff (p.size - 1) ≠ (Zero.zero : R) := by
  rcases p.normalized with hzero | hback
  · simp [size, hzero] at hpos
  · intro hcoeff
    apply hback
    rw [Array.back?_eq_getElem?]
    have hi : p.size - 1 < p.size := by omega
    have hi' : p.coeffs.size - 1 < p.coeffs.size := by
      simpa [size] using hi
    rw [Array.getElem?_eq_getElem hi']
    have hget :
        p.coeffs[p.coeffs.size - 1] = p.coeff (p.size - 1) := by
      rw [show p.size = p.coeffs.size by rfl]
      exact Array.getElem_eq_getD (Zero.zero : R)
    simp [hget, hcoeff]

/-- Coefficientwise equality of normalized dense polynomials forces equal stored sizes. -/
theorem size_eq_of_coeff_eq {p q : DensePoly R}
    (hcoeff : ∀ i, p.coeff i = q.coeff i) :
    p.size = q.size := by
  rcases Nat.lt_trichotomy p.size q.size with hpq | hpq | hqp
  · let i := q.size - 1
    have hp_le : p.size ≤ i := by omega
    have hp_zero : p.coeff i = (Zero.zero : R) :=
      coeff_eq_zero_of_size_le p hp_le
    have hq_ne : q.coeff i ≠ (Zero.zero : R) :=
      coeff_last_ne_zero_of_pos_size q (by omega)
    have h := hcoeff i
    rw [hp_zero] at h
    exact False.elim (hq_ne h.symm)
  · exact hpq
  · let i := p.size - 1
    have hq_le : q.size ≤ i := by omega
    have hq_zero : q.coeff i = (Zero.zero : R) :=
      coeff_eq_zero_of_size_le q hq_le
    have hp_ne : p.coeff i ≠ (Zero.zero : R) :=
      coeff_last_ne_zero_of_pos_size p (by omega)
    have h := hcoeff i
    rw [hq_zero] at h
    exact False.elim (hp_ne h)

/-- Extensionality for normalized dense polynomials by their coefficient functions. This is the
preferred form of extensionality: it asks only for coefficient agreement, since size agreement
is forced (via `size_eq_of_coeff_eq`). -/
@[ext] theorem ext_coeff {p q : DensePoly R}
    (hcoeff : ∀ i, p.coeff i = q.coeff i) :
    p = q := by
  apply ext_of_size_eq (size_eq_of_coeff_eq hcoeff)
  intro i _hi
  exact hcoeff i

/-- The largest exponent with a stored coefficient, or `none` for the zero polynomial. -/
def degree? (p : DensePoly R) : Option Nat :=
  if _h : p.size = 0 then none else some (p.size - 1)

/-- The zero polynomial has no stored coefficients. -/
@[simp] theorem size_zero : (0 : DensePoly R).size = 0 := by
  rfl

/-- The constant polynomial `C 0` collapses to the zero polynomial, so its coefficient array is
empty. -/
@[simp] theorem coeffs_C_zero : (C (0 : R)).coeffs = #[] := by
  change (C (Zero.zero : R)).coeffs = #[]
  simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList]

/-- A constant polynomial with a nonzero scalar stores a single-element coefficient array; this is
the companion to `coeffs_C_zero` for the nonzero case. -/
theorem coeffs_C_of_ne_zero {c : R} (hc : c ≠ (0 : R)) : (C c).coeffs = #[c] := by
  change c ≠ Zero.zero at hc
  simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList, hc]

/-- A constant polynomial has size at most one, with size `0` when the scalar is zero and `1`
otherwise. -/
theorem size_C_le_one (c : R) : (C c).size ≤ 1 := by
  by_cases hc : c = (0 : R)
  · rw [hc]
    change (C (Zero.zero : R)).size ≤ 1
    simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList, size]
  · change c ≠ Zero.zero at hc
    simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList, hc, size]

/-- The `degree?` of a constant polynomial, defaulted to `0`, is `0` regardless of the scalar:
either `degree? = none` (when `c = 0`) and `getD 0 = 0`, or `degree? = some 0` (otherwise). -/
@[simp] theorem degree?_C_getD (c : R) : (C c).degree?.getD 0 = 0 := by
  by_cases hc : c = (0 : R)
  · rw [hc]
    change (C (Zero.zero : R)).degree?.getD 0 = 0
    simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList, degree?, size]
  · change c ≠ Zero.zero at hc
    simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList, hc, degree?, size]

/-- The support of a dense polynomial, listed in ascending degree order. -/
def support (p : DensePoly R) : List Nat :=
  (List.range p.size).filter fun i => p.coeff i ≠ (Zero.zero : R)

/-- Return the underlying normalized coefficient array. -/
def toArray (p : DensePoly R) : Array R :=
  p.coeffs

end DensePoly
end Hex
