/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section
set_option backward.proofsInPublic true

/-!
Dense array-backed polynomials with the invariant that the stored coefficient array has no
trailing zeros. This normalization makes structural equality coincide with semantic equality.
-/
namespace Hex

universe u

/-- `DensePolyNormalized coeffs` means either `coeffs` is empty or its last coefficient is
nonzero, so the array has no trailing zeros. -/
@[expose]
def DensePolyNormalized {R : Type u} [Zero R] [DecidableEq R] (coeffs : Array R) : Prop :=
  coeffs.size = 0 ∨ coeffs.back? ≠ some (Zero.zero : R)

/-- Dense polynomials store coefficients in ascending degree order, with index `i` holding the
coefficient of `x^i`. -/
structure DensePoly (R : Type u) [Zero R] [DecidableEq R] where
  /-- The stored coefficients in ascending degree order. -/
  coeffs : Array R
  /-- Proof that `coeffs` carries no trailing zeros. -/
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
@[expose]
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

/-- Trimming trailing zeros never increases the coefficient-list length. -/
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

/-- Appending a trailing zero does not change the trailing-zero-trimmed list. -/
private theorem trimTrailingZerosList_append_zero (L : List R) :
    trimTrailingZerosList (L ++ [(Zero.zero : R)]) = trimTrailingZerosList L := by
  induction L with
  | nil => simp [trimTrailingZerosList]
  | cons a as ih =>
      show trimTrailingZerosList (a :: (as ++ [Zero.zero])) = trimTrailingZerosList (a :: as)
      unfold trimTrailingZerosList
      rw [ih]

/-- A list whose last entry is nonzero is its own trailing-zero-trim. -/
private theorem trimTrailingZerosList_append_ne_zero (L : List R) {v : R}
    (hv : v ≠ (Zero.zero : R)) :
    trimTrailingZerosList (L ++ [v]) = L ++ [v] := by
  induction L with
  | nil => simp [trimTrailingZerosList, hv]
  | cons a as ih =>
      show trimTrailingZerosList (a :: (as ++ [v])) = a :: (as ++ [v])
      unfold trimTrailingZerosList
      rw [ih]; simp

/-- Normalize a coefficient array by discarding all trailing zeros. The compiled runtime
uses the value-equal `trimTrailingZerosImpl` (proved by `trimTrailingZeros_eq_impl`,
registered `@[csimp]`), which pops trailing zeros off the array in place instead of
round-tripping through `coeffs.toList`. -/
@[expose]
noncomputable def trimTrailingZeros (coeffs : Array R) : Array R :=
  (trimTrailingZerosList coeffs.toList).toArray

omit [Zero R] [DecidableEq R] in
/-- An array with last element `v` splits as `pop ++ [v]` on the list side. -/
private theorem toList_eq_pop_append (coeffs : Array R) {v : R} (hb : coeffs.back? = some v) :
    coeffs.toList = coeffs.pop.toList ++ [v] := by
  have hgl : coeffs.toList.getLast? = some v := by
    rw [List.getLast?_eq_getElem?, Array.length_toList, Array.getElem?_toList,
      ← Array.back?_eq_getElem?, hb]
  have hne : coeffs.toList ≠ [] := by intro h; rw [h] at hgl; simp at hgl
  have hv : coeffs.toList.getLast hne = v := by
    rw [List.getLast?_eq_some_getLast hne] at hgl
    exact (Option.some.injEq _ _).mp hgl
  rw [Array.toList_pop, ← hv]
  exact (List.dropLast_concat_getLast hne).symm

/-- An array whose last entry is nonzero (or which is empty) is already trailing-zero free,
so trimming its coefficient list returns the list unchanged. -/
private theorem trimTrailingZerosList_toList_self (coeffs : Array R)
    (hb : coeffs.back? ≠ some (Zero.zero : R)) :
    trimTrailingZerosList coeffs.toList = coeffs.toList := by
  cases hbk : coeffs.back? with
  | none => rw [Array.back?_eq_none_iff] at hbk; subst hbk; simp [trimTrailingZerosList]
  | some v =>
      have hv : v ≠ (Zero.zero : R) := fun h => hb (h ▸ hbk)
      rw [toList_eq_pop_append coeffs hbk, trimTrailingZerosList_append_ne_zero _ hv]

/-- Trimming an array with nonzero last entry (or empty) is the identity. -/
private theorem trimTrailingZeros_self (coeffs : Array R)
    (hb : coeffs.back? ≠ some (Zero.zero : R)) :
    trimTrailingZeros coeffs = coeffs := by
  unfold trimTrailingZeros
  rw [trimTrailingZerosList_toList_self coeffs hb, Array.toArray_toList]

/-- Popping a trailing zero does not change the trim. -/
private theorem trimTrailingZeros_pop (coeffs : Array R)
    (hb : coeffs.back? = some (Zero.zero : R)) :
    trimTrailingZeros coeffs.pop = trimTrailingZeros coeffs := by
  unfold trimTrailingZeros
  rw [toList_eq_pop_append coeffs hb, trimTrailingZerosList_append_zero]

/-- Runtime loop for `trimTrailingZeros`: pop trailing zeros off the array, up to `n` of
them. With `n = coeffs.size` it pops the whole trailing-zero run, reusing the input
storage in place when it is uniquely referenced rather than allocating a list. -/
@[expose]
def trimTrailingZerosGo (coeffs : Array R) : Nat → Array R
  | 0 => coeffs
  | n + 1 =>
      if coeffs.back? = some (Zero.zero : R) then trimTrailingZerosGo coeffs.pop n else coeffs

/-- Once the fuel `n` is at least the array size, `trimTrailingZerosGo` has popped the whole
trailing-zero run and so agrees with `trimTrailingZeros`. -/
private theorem trimTrailingZerosGo_eq (n : Nat) :
    ∀ (coeffs : Array R), coeffs.size ≤ n →
      trimTrailingZerosGo coeffs n = trimTrailingZeros coeffs := by
  induction n with
  | zero =>
      intro coeffs hsize
      have hbk : coeffs.back? = none := by
        rw [Array.back?_eq_getElem?]; exact Array.getElem?_eq_none (by omega)
      have hbne : coeffs.back? ≠ some (Zero.zero : R) := by rw [hbk]; simp
      rw [trimTrailingZerosGo, trimTrailingZeros_self coeffs hbne]
  | succ n ih =>
      intro coeffs hsize
      rw [trimTrailingZerosGo]
      by_cases hb : coeffs.back? = some (Zero.zero : R)
      · rw [if_pos hb, ih coeffs.pop (by rw [Array.size_pop]; omega), trimTrailingZeros_pop coeffs hb]
      · rw [if_neg hb, trimTrailingZeros_self coeffs hb]

/-- Runtime implementation of `trimTrailingZeros`. -/
@[expose]
def trimTrailingZerosImpl (coeffs : Array R) : Array R :=
  trimTrailingZerosGo coeffs coeffs.size

/-- Register the value-equal `trimTrailingZerosImpl` as the compiled implementation of
`trimTrailingZeros`. Unlike `@[implemented_by]`, the `@[csimp]` swap is backed by the proof
`trimTrailingZerosGo_eq`, so the runtime loop is verified equal to the specification. -/
@[csimp]
theorem trimTrailingZeros_eq_impl : @trimTrailingZeros = @trimTrailingZerosImpl := by
  funext R _ _ coeffs
  show trimTrailingZeros coeffs = trimTrailingZerosImpl coeffs
  unfold trimTrailingZerosImpl
  exact (trimTrailingZerosGo_eq coeffs.size coeffs (Nat.le_refl _)).symm

/-- Build a dense polynomial from a raw coefficient array by normalizing away trailing zeros. -/
@[expose]
def ofCoeffs (coeffs : Array R) : DensePoly R :=
  { coeffs := trimTrailingZeros coeffs
    normalized := by
      unfold trimTrailingZeros DensePolyNormalized
      simpa using trimTrailingZerosList_normalized (R := R) coeffs.toList }

/-- The zero polynomial. -/
@[expose]
def zero : DensePoly R :=
  ofCoeffs #[]

instance : Zero (DensePoly R) where
  zero := zero

/-- Build a dense polynomial from a coefficient list by normalizing away trailing zeros. -/
@[expose]
def ofList (coeffs : List R) : DensePoly R :=
  ofCoeffs coeffs.toArray

/-- Build the constant polynomial with value `c`. The zero constant collapses to the zero
polynomial. -/
@[expose]
def C (c : R) : DensePoly R :=
  ofCoeffs #[c]

/-- Build the monomial `c * x^n`. The zero coefficient collapses to the zero polynomial. -/
@[expose]
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
@[expose]
def size (p : DensePoly R) : Nat :=
  p.coeffs.size

/-- The normalized polynomial built from a raw coefficient array stores no more coefficients
than the input array. -/
theorem size_ofCoeffs_le (coeffs : Array R) :
    (ofCoeffs coeffs).size ≤ coeffs.size := by
  unfold ofCoeffs size trimTrailingZeros
  simpa using trimTrailingZerosList_length_le (R := R) coeffs.toList

/-- `true` exactly when the polynomial is zero. -/
@[expose]
def isZero (p : DensePoly R) : Bool :=
  p.coeffs.isEmpty

/-- The coefficient of `x^n`, defaulting to `0` when `n` is out of range. -/
@[expose]
def coeff (p : DensePoly R) (n : Nat) : R :=
  p.coeffs.getD n (Zero.zero : R)

/-- Coefficient of `ofCoeffs arr` agrees with `arr.getD _ 0`: trimming trailing zeros does not
change the value at any index. -/
@[simp, grind =] theorem coeff_ofCoeffs (coeffs : Array R) (n : Nat) :
    (ofCoeffs coeffs).coeff n = coeffs.getD n (Zero.zero : R) := by
  unfold ofCoeffs coeff trimTrailingZeros
  simpa using trimTrailingZerosList_getD (R := R) coeffs.toList n

/-- Characterising lemma for the constant polynomial: its coefficient is `c` at degree `0`,
zero elsewhere. -/
@[simp, grind =] theorem coeff_C (c : R) (n : Nat) :
    (C c).coeff n = if n = 0 then c else (Zero.zero : R) := by
  rw [C, coeff_ofCoeffs]
  cases n with
  | zero =>
      simp
  | succ n =>
      simp

/-- Characterising lemma for monomials: `monomial n c` has coefficient `c` at degree `n` and zero
elsewhere, even when `c = 0` (in which case the polynomial is zero and every coefficient is `0`). -/
@[simp, grind =] theorem coeff_monomial (n : Nat) (c : R) (i : Nat) :
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
        rw [dif_pos hpush, Array.getElem_push_lt hrep]
        simp [hi]
      · have hnle : n < i := by omega
        have hpush_not : ¬ i < n + 1 := by omega
        rw [dif_neg hpush_not]
        simp [hi]

/-- Coefficient of `ofList coeffs` agrees with `coeffs.getD _ 0`: normalization does not change
the value at any index. -/
@[simp, grind =] theorem coeff_ofList (coeffs : List R) (n : Nat) :
    (ofList coeffs).coeff n = coeffs.getD n (Zero.zero : R) := by
  simp [ofList, coeff_ofCoeffs]

/-- List-level companion to `coeff_ofCoeffs`, retained as a compatibility alias for callers that
construct lists explicitly before converting them to arrays. Prefer `coeff_ofList` when the
caller-facing constructor is `ofList`. -/
@[simp, grind =] theorem coeff_ofCoeffs_list (coeffs : List R) (n : Nat) :
    (ofCoeffs coeffs.toArray).coeff n = coeffs.getD n (Zero.zero : R) := by
  simp

/-- The normalized polynomial built from a raw coefficient list stores no more coefficients
than the input list. -/
theorem size_ofList_le (coeffs : List R) :
    (ofList coeffs).size ≤ coeffs.length := by
  simpa [ofList] using size_ofCoeffs_le (R := R) coeffs.toArray

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

/-- Coefficient-level Boolean equality of two dense polynomials: equal stored
sizes and equal coefficients at every stored index. Because `DensePoly` is
normalized (no trailing zeros), this decides genuine equality, and unlike the
structural `DecidableEq (DensePoly R)` — which delegates to the core
`Array.instDecidableEqImpl` and does not kernel-reduce under the module system
(see `progress/lean4-array-decidableeq-module-repro.md`) — it is a plain
`Bool` fold that reduces on literal data under plain `public import`. -/
@[expose]
def beqCoeffs (a b : DensePoly R) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => decide (a.coeff i = b.coeff i)

/-- `beqCoeffs` is sound: a `true` result forces genuine polynomial equality. -/
theorem eq_of_beqCoeffs {a b : DensePoly R} (h : beqCoeffs a b = true) : a = b := by
  unfold beqCoeffs at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  have hsz : a.size = b.size := eq_of_beq hsize
  apply ext_coeff
  intro i
  by_cases hi : i < a.size
  · exact of_decide_eq_true ((List.all_eq_true.mp hall) i (List.mem_range.mpr hi))
  · have ha : a.coeff i = 0 := coeff_eq_zero_of_size_le a (Nat.le_of_not_lt hi)
    have hb : b.coeff i = 0 := coeff_eq_zero_of_size_le b (by omega)
    rw [ha, hb]

/-- `beqCoeffs` decides equality: the checker returns `true` exactly on equal
polynomials. -/
theorem beqCoeffs_iff_eq {a b : DensePoly R} : beqCoeffs a b = true ↔ a = b := by
  constructor
  · exact eq_of_beqCoeffs
  · intro h
    subst h
    unfold beqCoeffs
    rw [Bool.and_eq_true]
    constructor
    · exact beq_self_eq_true a.size
    · rw [List.all_eq_true]
      intro i _
      exact decide_eq_true rfl

/-- The largest exponent with a stored coefficient, or `none` for the zero polynomial. -/
@[expose]
def degree? (p : DensePoly R) : Option Nat :=
  if _h : p.size = 0 then none else some (p.size - 1)

/-- The zero polynomial has no stored coefficients. -/
@[simp, grind =] theorem size_zero : (0 : DensePoly R).size = 0 := by
  rfl

/-- The zero polynomial has no degree. -/
@[simp, grind =] theorem degree?_zero : (0 : DensePoly R).degree? = none := by
  unfold degree?
  simp

/-- Defaulting the degree of the zero polynomial returns the supplied default. -/
@[simp, grind =] theorem degree?_zero_getD (d : Nat) : ((0 : DensePoly R).degree?).getD d = d := by
  simp

/-- `isZero` is the Boolean test for having no stored coefficients. -/
theorem isZero_eq_true_iff (p : DensePoly R) :
    p.isZero = true ↔ p.size = 0 := by
  simp [isZero, size]

/-- A polynomial is nonzero exactly when it stores at least one coefficient. -/
theorem isZero_eq_false_iff (p : DensePoly R) :
    p.isZero = false ↔ 0 < p.size := by
  rw [← Bool.not_eq_true, isZero_eq_true_iff]
  exact ⟨fun h => Nat.pos_of_ne_zero h, fun h hzero => by omega⟩

/-- The constant polynomial `C 0` collapses to the zero polynomial, so its coefficient array is
empty. -/
@[simp, grind =] theorem coeffs_C_zero : (C (0 : R)).coeffs = #[] := by
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

/-- The zero constant polynomial stores no coefficients. -/
@[simp, grind =] theorem size_C_zero : (C (0 : R)).size = 0 := by
  change (C (0 : R)).coeffs.size = 0
  simp

/-- A nonzero constant polynomial stores exactly its scalar coefficient. -/
theorem size_C_of_ne_zero {c : R} (hc : c ≠ (0 : R)) : (C c).size = 1 := by
  change (C c).coeffs.size = 1
  rw [coeffs_C_of_ne_zero hc]
  rfl

/-- A constant polynomial is zero exactly when its scalar is zero. -/
theorem isZero_C_eq_true_iff (c : R) : (C c).isZero = true ↔ c = (0 : R) := by
  constructor
  · intro hzero
    by_cases hc : c = (0 : R)
    · exact hc
    · have hsize : (C c).size = 0 := (isZero_eq_true_iff (C c)).1 hzero
      have hone : (C c).size = 1 := size_C_of_ne_zero hc
      exact False.elim (Nat.succ_ne_zero 0 (hone.symm.trans hsize))
  · intro hc
    subst c
    change (C (Zero.zero : R)).isZero = true
    rw [isZero_eq_true_iff]
    exact size_C_zero

/-- The monomial with zero coefficient is the zero polynomial. -/
@[simp, grind =] theorem monomial_zero (n : Nat) : monomial n (0 : R) = 0 := by
  change monomial n (Zero.zero : R) = 0
  rw [monomial, dif_pos rfl]

/-- A monomial with nonzero coefficient stores exactly the `n + 1` coefficients up to degree `n`.
-/
theorem size_monomial_of_ne_zero {n : Nat} {c : R} (hc : c ≠ (0 : R)) :
    (monomial n c).size = n + 1 := by
  change c ≠ Zero.zero at hc
  rw [monomial, dif_neg hc]
  change ((Array.replicate n (Zero.zero : R)).push c).size = n + 1
  simp

/-- A monomial is zero exactly when its coefficient is zero. -/
theorem isZero_monomial_eq_true_iff (n : Nat) (c : R) :
    (monomial n c).isZero = true ↔ c = (0 : R) := by
  constructor
  · intro hzero
    by_cases hc : c = (0 : R)
    · exact hc
    · have hsize : (monomial n c).size = 0 := (isZero_eq_true_iff (monomial n c)).1 hzero
      have hmono : (monomial n c).size = n + 1 := size_monomial_of_ne_zero (n := n) hc
      exact False.elim (Nat.succ_ne_zero n (hmono.symm.trans hsize))
  · intro hc
    subst c
    change (monomial n (0 : R)).isZero = true
    rw [monomial_zero, isZero_eq_true_iff]
    exact size_zero

/-- A monomial with nonzero coefficient is not the zero polynomial. -/
theorem isZero_monomial_eq_false_of_ne_zero {n : Nat} {c : R} (hc : c ≠ (0 : R)) :
    (monomial n c).isZero = false := by
  rw [← Bool.not_eq_true]
  intro hzero
  exact hc ((isZero_monomial_eq_true_iff n c).1 hzero)

/-- The `degree?` of a constant polynomial, defaulted to `0`, is `0` regardless of the scalar:
either `degree? = none` (when `c = 0`) and `getD 0 = 0`, or `degree? = some 0` (otherwise). -/
@[simp, grind =] theorem degree?_C_getD (c : R) : (C c).degree?.getD 0 = 0 := by
  by_cases hc : c = (0 : R)
  · rw [hc]
    change (C (Zero.zero : R)).degree?.getD 0 = 0
    simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList, degree?, size]
  · change c ≠ Zero.zero at hc
    simp [C, ofCoeffs, trimTrailingZeros, trimTrailingZerosList, hc, degree?, size]

/-- The zero polynomial is the only dense polynomial with no degree. -/
theorem degree?_eq_none_iff (p : DensePoly R) :
    p.degree? = none ↔ p.size = 0 := by
  unfold degree?
  by_cases h : p.size = 0
  · simp [h]
  · simp [h]

/-- A nonzero dense polynomial has degree one less than its stored coefficient count. -/
theorem degree?_eq_some_of_pos_size (p : DensePoly R) (hpos : 0 < p.size) :
    p.degree? = some (p.size - 1) := by
  unfold degree?
  rw [dif_neg (Nat.ne_of_gt hpos)]

/-- A monomial with nonzero coefficient has degree exactly its exponent. -/
theorem degree?_monomial_of_ne_zero {n : Nat} {c : R} (hc : c ≠ (0 : R)) :
    (monomial n c).degree? = some n := by
  have hsize : (monomial n c).size = n + 1 := size_monomial_of_ne_zero hc
  rw [degree?_eq_some_of_pos_size _ (hsize ▸ Nat.succ_pos n), hsize, Nat.add_sub_cancel]

/-- The default-0 degree of a monomial with nonzero coefficient is its exponent. -/
theorem degree?_monomial_getD_of_ne_zero {n : Nat} {c : R} (hc : c ≠ (0 : R)) :
    (monomial n c).degree?.getD 0 = n := by
  rw [degree?_monomial_of_ne_zero hc, Option.getD_some]

/-- A monomial with nonzero coefficient is not the zero polynomial. -/
theorem monomial_ne_zero_of_ne_zero {n : Nat} {c : R} (hc : c ≠ (0 : R)) :
    (monomial n c) ≠ (0 : DensePoly R) := by
  intro h
  have hsize : (monomial n c).size = n + 1 := size_monomial_of_ne_zero hc
  rw [h, size_zero] at hsize
  exact Nat.succ_ne_zero n hsize.symm

/-- The support of a dense polynomial, listed in ascending degree order. -/
@[expose]
def support (p : DensePoly R) : List Nat :=
  (List.range p.size).filter fun i => p.coeff i ≠ (Zero.zero : R)

/-- Membership in `support` is coefficient nonzeroness inside the stored range. -/
@[simp] theorem mem_support {p : DensePoly R} {i : Nat} :
    i ∈ p.support ↔ i < p.size ∧ p.coeff i ≠ (Zero.zero : R) := by
  simp [support]

/-- The zero polynomial has empty support. -/
@[simp, grind =] theorem support_zero : (0 : DensePoly R).support = [] := by
  simp [support]

/-- A constant polynomial has support `{0}` exactly when its scalar is nonzero. -/
@[simp, grind =] theorem support_C (c : R) :
    (C c).support = if c = (0 : R) then [] else [0] := by
  by_cases hc : c = (0 : R)
  · simp [hc, support]
  · have hcz : c ≠ Zero.zero := hc
    simp [support, size_C_of_ne_zero hc, hc, hcz]

/-- Membership in the support of a constant polynomial is exactly nonzero degree zero. -/
theorem mem_support_C {c : R} {i : Nat} :
    i ∈ (C c).support ↔ i = 0 ∧ c ≠ (0 : R) := by
  by_cases hc : c = (0 : R)
  · simp [support_C, hc]
  · simp [support_C, hc]

private theorem filter_range_succ_eq_singleton (n : Nat) :
    (List.range (n + 1)).filter (fun i => i = n) = [n] := by
  rw [show n + 1 = Nat.succ n by omega, List.range_succ, List.filter_append]
  have hleft : (List.range n).filter (fun i => decide (i = n)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi hdec
    have hlt : i < n := by
      simpa using (List.mem_range.mp hi)
    simp at hdec
    omega
  simp [hleft]

/-- A monomial has support `{n}` exactly when its coefficient is nonzero. -/
@[simp, grind =] theorem support_monomial (n : Nat) (c : R) :
    (monomial n c).support = if c = (0 : R) then [] else [n] := by
  by_cases hc : c = (0 : R)
  · simp [hc]
  · have hcz : c ≠ Zero.zero := hc
    simpa [support, size_monomial_of_ne_zero hc, coeff_monomial, hc, hcz]
      using filter_range_succ_eq_singleton n

/-- Membership in the support of a monomial is exactly its nonzero exponent. -/
theorem mem_support_monomial {n : Nat} {c : R} {i : Nat} :
    i ∈ (monomial n c).support ↔ i = n ∧ c ≠ (0 : R) := by
  by_cases hc : c = (0 : R)
  · simp [hc]
  · simp [hc]

/-- Return the underlying normalized coefficient array. -/
@[expose]
def toArray (p : DensePoly R) : Array R :=
  p.coeffs

/-- The exposed normalized coefficient array has the same size as the polynomial. -/
@[simp, grind =] theorem toArray_size (p : DensePoly R) :
    p.toArray.size = p.size := by
  rfl

/-- Reading the exposed normalized coefficient array with default `0` is the polynomial
coefficient function. -/
@[simp] theorem toArray_getD (p : DensePoly R) (n : Nat) :
    p.toArray.getD n (Zero.zero : R) = p.coeff n := by
  rfl

/-- Spec-level view of the stored coefficients as a list, lowest degree first.
`noncomputable` by design: kernel-facing specifications, theorem statements,
and proofs read coefficients through this list view, while runtime code stays
on the `Array` API. A deliberate runtime list round-trip spells out
`toArray.toList` explicitly. -/
@[expose]
noncomputable def toList (p : DensePoly R) : List R :=
  p.toArray.toList

/-- The spec-level coefficient list has one entry per stored coefficient. -/
@[simp, grind =] theorem length_toList (p : DensePoly R) :
    p.toList.length = p.size := by
  simp [toList, toArray, size]

/-- Normalizing the already-normalized coefficient array reconstructs the same polynomial. -/
@[simp, grind =] theorem ofCoeffs_toArray (p : DensePoly R) :
    ofCoeffs p.toArray = p := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs]
  rfl

/-- Building from the spec-level coefficient list reconstructs the same polynomial. -/
@[simp, grind =] theorem ofList_toList (p : DensePoly R) :
    ofList p.toList = p := by
  simp [toList, ofList]

/-- Normalizing an empty coefficient array gives the zero polynomial. -/
@[simp, grind =] theorem ofCoeffs_empty :
    (ofCoeffs (#[] : Array R) : DensePoly R) = 0 := by
  rfl

/-- Normalizing an empty coefficient list gives the zero polynomial. -/
@[simp, grind =] theorem ofList_nil :
    (ofList ([] : List R) : DensePoly R) = 0 := by
  rfl

/-- An array consisting only of zeros normalizes to the zero polynomial. -/
@[simp, grind =] theorem ofCoeffs_replicate_zero (n : Nat) :
    (ofCoeffs (Array.replicate n (Zero.zero : R)) : DensePoly R) = 0 := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs]
  change (Array.replicate n (Zero.zero : R)).getD i (Zero.zero : R) = (Zero.zero : R)
  simp [Array.getD]

end DensePoly
end Hex
