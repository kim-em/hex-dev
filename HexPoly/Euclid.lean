import Init.Grind.Ring.Basic
import Init.Data.List.Lemmas
import HexPoly.Operations

/-!
Executable Euclidean-algorithm operations for dense array-backed polynomials.

This module extends `DensePoly` with a field-based long-division routine, the
derived gcd and extended-gcd algorithms, integer content/primitive-part helpers,
and the existential polynomial CRT construction used by downstream libraries.
-/
namespace Hex

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- The leading coefficient, or `0` for the zero polynomial. -/
def leadingCoeff (p : DensePoly R) : R :=
  p.coeffs.back?.getD 0

/-- The constant polynomial `1`. -/
instance [One R] : One (DensePoly R) where
  one := C 1

/-- A polynomial is monic when its leading coefficient is `1`. -/
def Monic [One R] (p : DensePoly R) : Prop :=
  p.leadingCoeff = 1

private def arrayDegreeAux (coeffs : Array R) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      let i := fuel
      if coeffs.getD i (Zero.zero : R) = (Zero.zero : R) then
        arrayDegreeAux coeffs fuel
      else
        some i

private def arrayDegree? (coeffs : Array R) : Option Nat :=
  arrayDegreeAux coeffs coeffs.size

private theorem arrayDegreeAux_some_lt {coeffs : Array R} {fuel rd : Nat}
    (h : arrayDegreeAux coeffs fuel = some rd) :
    rd < fuel := by
  induction fuel generalizing rd with
  | zero =>
      simp [arrayDegreeAux] at h
  | succ fuel ih =>
      unfold arrayDegreeAux at h
      by_cases hcoeff : coeffs[fuel]?.getD (Zero.zero : R) = (Zero.zero : R)
      · simp [hcoeff] at h
        exact Nat.lt_succ_of_lt (ih h)
      · simp [hcoeff] at h
        subst rd
        omega

private theorem arrayDegreeAux_some_coeff_ne_zero {coeffs : Array R} {fuel rd : Nat}
    (h : arrayDegreeAux coeffs fuel = some rd) :
    coeffs.getD rd (Zero.zero : R) ≠ (Zero.zero : R) := by
  induction fuel generalizing rd with
  | zero =>
      simp [arrayDegreeAux] at h
  | succ fuel ih =>
      unfold arrayDegreeAux at h
      by_cases hcoeff : coeffs[fuel]?.getD (Zero.zero : R) = (Zero.zero : R)
      · simp [hcoeff] at h
        exact ih h
      · simp [hcoeff] at h
        cases h
        rw [Array.getD_eq_getD_getElem?]
        exact hcoeff

private theorem arrayDegreeAux_none_getD_eq_zero {coeffs : Array R} {fuel i : Nat}
    (h : arrayDegreeAux coeffs fuel = none) (hi : i < fuel) :
    coeffs.getD i (Zero.zero : R) = (Zero.zero : R) := by
  induction fuel generalizing i with
  | zero =>
      omega
  | succ fuel ih =>
      unfold arrayDegreeAux at h
      by_cases hcoeff : coeffs[fuel]?.getD (Zero.zero : R) = (Zero.zero : R)
      · simp [hcoeff] at h
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
        · exact ih h hlt
        · subst i
          rw [Array.getD_eq_getD_getElem?]
          exact hcoeff
      · simp [hcoeff] at h

private theorem arrayDegreeAux_some_above_eq_zero {coeffs : Array R} {fuel rd i : Nat}
    (h : arrayDegreeAux coeffs fuel = some rd) (hrd : rd < i) (hi : i < fuel) :
    coeffs.getD i (Zero.zero : R) = (Zero.zero : R) := by
  induction fuel generalizing rd i with
  | zero =>
      omega
  | succ fuel ih =>
      unfold arrayDegreeAux at h
      by_cases hcoeff : coeffs[fuel]?.getD (Zero.zero : R) = (Zero.zero : R)
      · simp [hcoeff] at h
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
        · exact ih h hrd hlt
        · subst i
          rw [Array.getD_eq_getD_getElem?]
          exact hcoeff
      · simp [hcoeff] at h
        cases h
        omega

private theorem arrayDegree?_some_lt {coeffs : Array R} {rd : Nat}
    (h : arrayDegree? coeffs = some rd) :
    rd < coeffs.size := by
  exact arrayDegreeAux_some_lt h

private theorem arrayDegree?_some_coeff_ne_zero {coeffs : Array R} {rd : Nat}
    (h : arrayDegree? coeffs = some rd) :
    coeffs.getD rd (Zero.zero : R) ≠ (Zero.zero : R) := by
  exact arrayDegreeAux_some_coeff_ne_zero h

private theorem arrayDegree?_some_above_eq_zero {coeffs : Array R} {rd i : Nat}
    (h : arrayDegree? coeffs = some rd) (hrd : rd < i) :
    coeffs.getD i (Zero.zero : R) = (Zero.zero : R) := by
  by_cases hi : i < coeffs.size
  · exact arrayDegreeAux_some_above_eq_zero h hrd hi
  · unfold Array.getD
    exact dif_neg hi

private theorem arrayDegree?_none_getD_eq_zero {coeffs : Array R} {i : Nat}
    (h : arrayDegree? coeffs = none) :
    coeffs.getD i (Zero.zero : R) = (Zero.zero : R) := by
  by_cases hi : i < coeffs.size
  · exact arrayDegreeAux_none_getD_eq_zero h hi
  · unfold Array.getD
    exact dif_neg hi

private theorem ofCoeffs_degree_getD_lt_of_forall_zero_ge {coeffs : Array R} {bound : Nat}
    (hpos : 0 < bound)
    (hzero : ∀ i, bound ≤ i → coeffs.getD i (Zero.zero : R) = (Zero.zero : R)) :
    (ofCoeffs coeffs : DensePoly R).degree?.getD 0 < bound := by
  let p : DensePoly R := ofCoeffs coeffs
  have hsize_le : p.size ≤ bound := by
    by_cases hle : p.size ≤ bound
    · exact hle
    · have hlt : bound < p.size := Nat.lt_of_not_ge hle
      let i := p.size - 1
      have hpos_size : 0 < p.size := by omega
      have hbound_i : bound ≤ i := by omega
      have hcoeff_zero : coeffs.getD i (Zero.zero : R) = (Zero.zero : R) :=
        hzero i hbound_i
      have hpcoeff_zero : p.coeff i = (Zero.zero : R) := by
        dsimp [p]
        rw [coeff_ofCoeffs]
        exact hcoeff_zero
      have hpcoeff_ne : p.coeff i ≠ (Zero.zero : R) :=
        coeff_last_ne_zero_of_pos_size p hpos_size
      exact False.elim (hpcoeff_ne hpcoeff_zero)
  by_cases hsize_zero : p.size = 0
  · simp [p, degree?, hsize_zero, hpos]
  · have hpos_size : 0 < p.size := Nat.pos_of_ne_zero hsize_zero
    have hdeg : p.degree?.getD 0 = p.size - 1 := by
      simp [degree?, hsize_zero]
    rw [hdeg]
    omega

private def subtractScaledShiftStep [Sub R] [Mul R]
    (q : Array R) (shift : Nat) (coeff : R) (next : Array R) (j : Nat) : Array R :=
  let idx := shift + j
  next.set! idx (next.getD idx (Zero.zero : R) - coeff * q.getD j (Zero.zero : R))

private def subtractScaledShift [Sub R] [Mul R]
    (rem q : Array R) (shift : Nat) (coeff : R) : Array R :=
  (List.range q.size).foldl (subtractScaledShiftStep q shift coeff) rem

omit [DecidableEq R] in
private theorem array_getD_set!_same (xs : Array R) (n : Nat) (v : R)
    (hn : n < xs.size) :
    (xs.set! n v).getD n (Zero.zero : R) = v := by
  simp [Array.getD, hn]

omit [DecidableEq R] in
private theorem array_getD_set!_ne (xs : Array R) (n k : Nat) (v : R)
    (hne : k ≠ n) :
    (xs.set! k v).getD n (Zero.zero : R) = xs.getD n (Zero.zero : R) := by
  by_cases hkn : k = n
  · exact False.elim (hne hkn)
  · by_cases hn : n < xs.size
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hn, hkn]
    · unfold Array.getD
      simp [Array.set!_eq_setIfInBounds, hn]

omit [DecidableEq R] in
private theorem subtractScaledShift_fold_getD_of_forall_ne [Sub R] [Mul R]
    (rem q : Array R) (shift : Nat) (coeff : R) (n : Nat) (xs : List Nat)
    (hne : ∀ j, j ∈ xs → shift + j ≠ n) :
    (xs.foldl (subtractScaledShiftStep q shift coeff) rem).getD n (Zero.zero : R) =
      rem.getD n (Zero.zero : R) := by
  induction xs generalizing rem with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [ih (rem := subtractScaledShiftStep q shift coeff rem j) (by
        intro k hk
        exact hne k (List.mem_cons_of_mem j hk))]
      unfold subtractScaledShiftStep
      exact array_getD_set!_ne rem n (shift + j)
        (rem.getD (shift + j) (Zero.zero : R) -
          coeff * q.getD j (Zero.zero : R))
        (hne j List.mem_cons_self)

omit [DecidableEq R] in
private theorem subtractScaledShift_fold_size [Sub R] [Mul R]
    (rem q : Array R) (shift : Nat) (coeff : R) (xs : List Nat) :
    (xs.foldl (subtractScaledShiftStep q shift coeff) rem).size = rem.size := by
  induction xs generalizing rem with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      unfold subtractScaledShiftStep
      simp [Array.set!_eq_setIfInBounds]

omit [DecidableEq R] in
private theorem subtractScaledShift_getD_of_forall_ne [Sub R] [Mul R]
    (rem q : Array R) (shift : Nat) (coeff : R) (n : Nat)
    (hne : ∀ j, j < q.size → shift + j ≠ n) :
    (subtractScaledShift rem q shift coeff).getD n (Zero.zero : R) =
      rem.getD n (Zero.zero : R) := by
  unfold subtractScaledShift
  apply subtractScaledShift_fold_getD_of_forall_ne
  intro j hj
  exact hne j (List.mem_range.mp hj)

omit [DecidableEq R] in
private theorem subtractScaledShift_fold_getD_range [Lean.Grind.CommRing R]
    (rem q : Array R) (shift : Nat) (coeff : R) (n m : Nat)
    (hbound : ∀ j, j < m → shift + j < rem.size) :
    ((List.range m).foldl (subtractScaledShiftStep q shift coeff) rem).getD n
        (Zero.zero : R) =
      if shift ≤ n ∧ n - shift < m then
        rem.getD n (Zero.zero : R) - coeff * q.getD (n - shift) (Zero.zero : R)
      else
        rem.getD n (Zero.zero : R) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hnlast : n = shift + m
      · subst n
        have hprefix :
            ((List.range m).foldl (subtractScaledShiftStep q shift coeff) rem).getD
                (shift + m) (Zero.zero : R) =
              rem.getD (shift + m) (Zero.zero : R) := by
          rw [ih]
          · simp
          · intro j hj
            exact hbound j (by omega)
        have hprefix_size :
            ((List.range m).foldl (subtractScaledShiftStep q shift coeff) rem).size =
              rem.size :=
          subtractScaledShift_fold_size rem q shift coeff (List.range m)
        change
          (((List.range m).foldl (subtractScaledShiftStep q shift coeff) rem).set!
              (shift + m)
              (((List.range m).foldl (subtractScaledShiftStep q shift coeff) rem).getD
                (shift + m) (Zero.zero : R) -
                coeff * q.getD m (Zero.zero : R))).getD
            (shift + m) (Zero.zero : R) =
              if shift ≤ shift + m ∧ shift + m - shift < m + 1 then
                rem.getD (shift + m) (Zero.zero : R) -
                  coeff * q.getD (shift + m - shift) (Zero.zero : R)
              else
                rem.getD (shift + m) (Zero.zero : R)
        rw [array_getD_set!_same]
        · rw [hprefix]
          have hsub : shift + m - shift = m := by omega
          simp [hsub]
        · simpa [hprefix_size] using hbound m (by omega)
      · change
          (((List.range m).foldl (subtractScaledShiftStep q shift coeff) rem).set!
              (shift + m)
              (((List.range m).foldl (subtractScaledShiftStep q shift coeff) rem).getD
                (shift + m) (Zero.zero : R) -
                coeff * q.getD m (Zero.zero : R))).getD n (Zero.zero : R) =
              if shift ≤ n ∧ n - shift < m + 1 then
                rem.getD n (Zero.zero : R) - coeff * q.getD (n - shift) (Zero.zero : R)
              else
                rem.getD n (Zero.zero : R)
        rw [array_getD_set!_ne]
        · rw [ih]
          · by_cases h : shift ≤ n ∧ n - shift < m
            · have hsucc : shift ≤ n ∧ n - shift < m + 1 := ⟨h.1, by omega⟩
              simp [h, hsucc]
            · have hnot_m : ¬ (shift ≤ n ∧ n - shift = m) := by
                intro hm
                apply hnlast
                omega
              have hiff : (shift ≤ n ∧ n - shift < m + 1) ↔
                  (shift ≤ n ∧ n - shift < m) := by
                constructor
                · intro hsucc
                  have hne : n - shift ≠ m := by
                    intro hm
                    exact hnot_m ⟨hsucc.1, hm⟩
                  exact ⟨hsucc.1, by omega⟩
                · intro hlt
                  exact ⟨hlt.1, by omega⟩
              by_cases hsucc : shift ≤ n ∧ n - shift < m + 1
              · have h' : shift ≤ n ∧ n - shift < m := hiff.mp hsucc
                exact False.elim (h h')
              · simp [h, hsucc]
          · intro j hj
            exact hbound j (by omega)
        · omega

omit [DecidableEq R] in
private theorem subtractScaledShift_getD [Lean.Grind.CommRing R]
    (rem q : Array R) (shift : Nat) (coeff : R) (n : Nat)
    (hbound : ∀ j, j < q.size → shift + j < rem.size) :
    (subtractScaledShift rem q shift coeff).getD n (Zero.zero : R) =
      if shift ≤ n ∧ n - shift < q.size then
        rem.getD n (Zero.zero : R) - coeff * q.getD (n - shift) (Zero.zero : R)
      else
        rem.getD n (Zero.zero : R) := by
  unfold subtractScaledShift
  exact subtractScaledShift_fold_getD_range rem q shift coeff n q.size hbound

omit [DecidableEq R] in
private theorem subtractScaledShift_getD_last [Sub R] [Mul R]
    (rem q : Array R) (shift qDegree : Nat) (coeff : R)
    (hsize : q.size = qDegree + 1) (hidx : shift + qDegree < rem.size) :
    (subtractScaledShift rem q shift coeff).getD (shift + qDegree) (Zero.zero : R) =
      rem.getD (shift + qDegree) (Zero.zero : R) -
        coeff * q.getD qDegree (Zero.zero : R) := by
  unfold subtractScaledShift
  rw [hsize, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hprefix :
      ((List.range qDegree).foldl (subtractScaledShiftStep q shift coeff) rem).getD
          (shift + qDegree) (Zero.zero : R) =
        rem.getD (shift + qDegree) (Zero.zero : R) := by
    apply subtractScaledShift_fold_getD_of_forall_ne
    intro j hj
    have hjlt : j < qDegree := List.mem_range.mp hj
    omega
  have hprefix_size :
      ((List.range qDegree).foldl (subtractScaledShiftStep q shift coeff) rem).size =
        rem.size :=
    subtractScaledShift_fold_size rem q shift coeff (List.range qDegree)
  change
    (((List.range qDegree).foldl (subtractScaledShiftStep q shift coeff) rem).set!
        (shift + qDegree)
        (((List.range qDegree).foldl (subtractScaledShiftStep q shift coeff) rem).getD
          (shift + qDegree) (Zero.zero : R) -
          coeff * q.getD qDegree (Zero.zero : R))).getD
      (shift + qDegree) (Zero.zero : R) =
        rem.getD (shift + qDegree) (Zero.zero : R) -
          coeff * q.getD qDegree (Zero.zero : R)
  rw [array_getD_set!_same]
  · rw [hprefix]
  · simpa [hprefix_size] using hidx

omit [DecidableEq R] in
private theorem subtractScaledShift_getD_above_last [Sub R] [Mul R]
    (rem q : Array R) (shift qDegree : Nat) (coeff : R) (n : Nat)
    (hsize : q.size = qDegree + 1) (hn : shift + qDegree < n) :
    (subtractScaledShift rem q shift coeff).getD n (Zero.zero : R) =
      rem.getD n (Zero.zero : R) := by
  apply subtractScaledShift_getD_of_forall_ne
  intro j hj
  have hjle : j ≤ qDegree := by omega
  omega

omit [DecidableEq R] in
private theorem subtractScaledShift_getD_last_cancel [Sub R] [Mul R]
    (rem q : Array R) (shift qDegree : Nat) (coeff : R)
    (hsize : q.size = qDegree + 1) (hidx : shift + qDegree < rem.size)
    (hcancel :
      rem.getD (shift + qDegree) (Zero.zero : R) -
        coeff * q.getD qDegree (Zero.zero : R) = (Zero.zero : R)) :
    (subtractScaledShift rem q shift coeff).getD (shift + qDegree) (Zero.zero : R) =
      (Zero.zero : R) := by
  rw [subtractScaledShift_getD_last rem q shift qDegree coeff hsize hidx]
  exact hcancel

private def divModArrayAux [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R)
    (fuel : Nat) (quot rem : Array R) : Array R × Array R :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      match arrayDegree? rem with
      | none => (quot, rem)
      | some rd =>
          if _hdeg : rd < qDegree then
            (quot, rem)
          else
            let shift := rd - qDegree
            let coeff := scaleLead (rem.getD rd (Zero.zero : R))
            let quot := quot.set! shift coeff
            let rem := subtractScaledShift rem q shift coeff
            divModArrayAux q qDegree scaleLead fuel quot rem

private theorem divModArrayAux_scaleLead_congr [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) {scaleLead₁ scaleLead₂ : R → R}
    (hscale : ∀ a : R, scaleLead₁ a = scaleLead₂ a)
    (fuel : Nat) (quot rem : Array R) :
    divModArrayAux q qDegree scaleLead₁ fuel quot rem =
      divModArrayAux q qDegree scaleLead₂ fuel quot rem := by
  induction fuel generalizing quot rem with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold divModArrayAux
      cases hdeg : arrayDegree? rem with
      | none =>
          rfl
      | some rd =>
          by_cases hrd : rd < qDegree
          · simp [hrd]
          · simp [hrd]
            rw [hscale]
            exact ih _ _

private theorem divModArrayAux_remainder_zero_ge [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R)
    (fuel : Nat) (quot rem : Array R)
    (hsize : q.size = qDegree + 1)
    (hcancel :
      ∀ a : R, a - scaleLead a * q.getD qDegree (Zero.zero : R) = (Zero.zero : R))
    (hzero : ∀ i, qDegree + fuel ≤ i → rem.getD i (Zero.zero : R) = (Zero.zero : R)) :
    ∀ i, qDegree ≤ i →
      (divModArrayAux q qDegree scaleLead fuel quot rem).2.getD i (Zero.zero : R) =
        (Zero.zero : R) := by
  induction fuel generalizing quot rem with
  | zero =>
      intro i hi
      simpa [divModArrayAux] using hzero i (by simpa using hi)
  | succ fuel ih =>
      intro i hi
      unfold divModArrayAux
      cases hdeg : arrayDegree? rem with
      | none =>
          exact arrayDegree?_none_getD_eq_zero hdeg
      | some rd =>
          by_cases hrd_lt : rd < qDegree
          · simp [hrd_lt]
            simpa [Array.getD_eq_getD_getElem?] using
              arrayDegree?_some_above_eq_zero hdeg (by omega : rd < i)
          · simp [hrd_lt]
            let shift := rd - qDegree
            let coeff := scaleLead (rem.getD rd (Zero.zero : R))
            have hrd_nonzero : rem.getD rd (Zero.zero : R) ≠ (Zero.zero : R) :=
              arrayDegree?_some_coeff_ne_zero hdeg
            have hrd_le : rd ≤ qDegree + fuel := by
              by_cases hle : rd ≤ qDegree + fuel
              · exact hle
              · exfalso
                have hbound : qDegree + (fuel + 1) ≤ rd := by omega
                exact hrd_nonzero (hzero rd hbound)
            have hrd_eq : shift + qDegree = rd := by
              dsimp [shift]
              omega
            have hrd_size : rd < rem.size := arrayDegree?_some_lt hdeg
            have hrec := ih
              (quot := quot.set! (rd - qDegree) (scaleLead (rem.getD rd (Zero.zero : R))))
              (rem := subtractScaledShift rem q (rd - qDegree)
                (scaleLead (rem.getD rd (Zero.zero : R))))
              (by
                intro n hn
                rcases Nat.lt_trichotomy rd n with hlt | heq | hgt
                · rw [subtractScaledShift_getD_above_last rem q shift qDegree coeff n hsize]
                  · exact arrayDegree?_some_above_eq_zero hdeg hlt
                  · omega
                · subst n
                  have hlast :
                      (subtractScaledShift rem q shift coeff).getD
                          (shift + qDegree) (Zero.zero : R) = (Zero.zero : R) := by
                    apply subtractScaledShift_getD_last_cancel
                    · exact hsize
                    · simpa [hrd_eq] using hrd_size
                    · rw [hrd_eq]
                      exact hcancel (rem.getD rd (Zero.zero : R))
                  simpa [shift, coeff, hrd_eq] using hlast
                · have hle : n ≤ rd := by omega
                  exfalso
                  omega)
              i hi
            simpa [Array.getD_eq_getD_getElem?] using hrec

private def divModArray [Sub R] [Mul R]
    (p q : DensePoly R) (scaleLead : R → R) : DensePoly R × DensePoly R :=
  if q.isZero then
    (0, p)
  else
    let qDegree := q.size - 1
    let quotientSize := p.size - qDegree
    let quot := Array.replicate quotientSize (Zero.zero : R)
    let qr := divModArrayAux q.toArray qDegree scaleLead p.size quot p.toArray
    (ofCoeffs qr.1, ofCoeffs qr.2)

/-- The array-backed long division result depends only on the pointwise values of the
leading-coefficient scaling function. -/
theorem divModArray_scaleLead_congr [Sub R] [Mul R]
    (p q : DensePoly R) {scaleLead₁ scaleLead₂ : R → R}
    (hscale : ∀ a : R, scaleLead₁ a = scaleLead₂ a) :
    divModArray p q scaleLead₁ = divModArray p q scaleLead₂ := by
  unfold divModArray
  by_cases hqzero : q.isZero
  · simp [hqzero]
  · simp [hqzero]
    rw [divModArrayAux_scaleLead_congr q.toArray (q.size - 1) hscale]
    simp

theorem divModArray_remainder_degree_lt_of_pos_degree [Sub R] [Mul R]
    (p q : DensePoly R) (scaleLead : R → R)
    (hdegree : 0 < q.degree?.getD 0)
    (hcancel : ∀ a : R, a - scaleLead a * q.leadingCoeff = (Zero.zero : R)) :
    (divModArray p q scaleLead).2.degree?.getD 0 < q.degree?.getD 0 := by
  unfold divModArray
  by_cases hqzero : q.isZero
  · have hqsize : q.size = 0 := by
      simp [isZero] at hqzero
      simpa [size] using hqzero
    have hdeg_zero : q.degree?.getD 0 = 0 := by
      simp [degree?, hqsize]
    omega
  · rw [if_neg hqzero]
    let qDegree := q.size - 1
    let quotientSize := p.size - qDegree
    let quot := Array.replicate quotientSize (Zero.zero : R)
    let qr := divModArrayAux q.toArray qDegree scaleLead p.size quot p.toArray
    have hqpos : 0 < q.size := Nat.pos_of_ne_zero (by
      intro hsize_zero
      apply hqzero
      have hcoeffs : q.coeffs.size = 0 := by
        simpa [size] using hsize_zero
      have hisempty : q.coeffs.isEmpty = true := by
        simpa [Array.isEmpty_iff_size_eq_zero] using hcoeffs
      simpa [isZero] using hisempty)
    have hdeg_eq : q.degree?.getD 0 = qDegree := by
      simp [degree?, Nat.ne_of_gt hqpos, qDegree]
    have hsize : q.toArray.size = qDegree + 1 := by
      have hcoeffpos : 0 < q.coeffs.size := by
        simpa [size] using hqpos
      have hraw : q.coeffs.size = (q.coeffs.size - 1) + 1 := by omega
      simpa [qDegree, toArray, size] using hraw
    have hlead : q.toArray.getD qDegree (Zero.zero : R) = q.leadingCoeff := by
      unfold leadingCoeff toArray
      dsimp [qDegree]
      change q.coeffs.getD (q.coeffs.size - 1) (Zero.zero : R) =
        q.coeffs.back?.getD (Zero.zero : R)
      have hidx : q.coeffs.size - 1 < q.coeffs.size := by
        simpa [size] using Nat.sub_one_lt_of_lt hqpos
      rw [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_getElem hidx]
      rw [Array.back?_eq_getElem?]
      rw [Array.getElem?_eq_getElem hidx]
    have hzero_start :
        ∀ i, qDegree + p.size ≤ i → p.toArray.getD i (Zero.zero : R) = (Zero.zero : R) := by
      intro i hi
      unfold toArray Array.getD
      have hle : p.coeffs.size ≤ i := by
        simpa [size] using (by omega : p.size ≤ i)
      rw [dif_neg (Nat.not_lt.mpr hle)]
    have hzero_final :
        ∀ i, qDegree ≤ i → qr.2.getD i (Zero.zero : R) = (Zero.zero : R) := by
      dsimp [qr, quot]
      apply divModArrayAux_remainder_zero_ge
      · exact hsize
      · intro a
        rw [hlead]
        exact hcancel a
      · exact hzero_start
    rw [hdeg_eq]
    dsimp [qr]
    apply ofCoeffs_degree_getD_lt_of_forall_zero_ge
    · simpa [hdeg_eq] using hdegree
    · exact hzero_final

/-- Long division by a monic divisor over a commutative ring. -/
private def divModMonicAux [One R] [Add R] [Sub R] [Mul R]
    (q : DensePoly R) (fuel : Nat)
    (quot rem : DensePoly R) : DensePoly R × DensePoly R :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      if _hq : q.isZero then
        (0, rem)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if _hdeg : rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := rem.leadingCoeff
              let term := monomial k coeff
              divModMonicAux q fuel (quot + term) (rem - term * q)
        | _, _ => (quot, rem)

/-- Divide by a monic polynomial. The remainder has degree below the divisor whenever the fuel
is sufficient, which is the case for normalized dense polynomials. -/
def divModMonic [One R] [Add R] [Sub R] [Mul R]
    (p q : DensePoly R) (_hmonic : Monic q) :
    DensePoly R × DensePoly R :=
  divModArray p q id

/-- Field-based long division with remainder. Division by `0` returns `(0, p)`. -/
private def divModAux [One R] [Add R] [Sub R] [Mul R] [Div R]
    (q : DensePoly R) (fuel : Nat)
    (quot rem : DensePoly R) : DensePoly R × DensePoly R :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      if _hq : q.isZero then
        (0, rem)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if _hdeg : rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := rem.leadingCoeff / q.leadingCoeff
              let term := monomial k coeff
              divModAux q fuel (quot + term) (rem - term * q)
        | _, _ => (quot, rem)

/-- Polynomial division with remainder over a field. -/
def divMod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R × DensePoly R :=
  if p.degree?.getD 0 < q.degree?.getD 0 then
    (0, p)
  else
    divModArray p q (fun coeff => coeff / q.leadingCoeff)

theorem divMod_remainder_degree_lt_of_pos_degree_core [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R)
    (hdegree : 0 < q.degree?.getD 0)
    (hcancel : ∀ a : R, a - (a / q.leadingCoeff) * q.leadingCoeff = (Zero.zero : R)) :
    (divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  unfold divMod
  by_cases hlt : p.degree?.getD 0 < q.degree?.getD 0
  · simp [hlt]
  · rw [if_neg hlt]
    exact divModArray_remainder_degree_lt_of_pos_degree p q
      (fun coeff => coeff / q.leadingCoeff) hdegree hcancel

theorem divMod_remainder_eq_zero_of_degree_zero_core [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R)
    (hqsize : q.size = 1)
    (hcancel : ∀ a : R, a - (a / q.leadingCoeff) * q.leadingCoeff = (Zero.zero : R)) :
    (divMod p q).2 = 0 := by
  unfold divMod
  have hqdeg : q.degree?.getD 0 = 0 := by
    simp [degree?, hqsize]
  have hnot_lt : ¬ p.degree?.getD 0 < q.degree?.getD 0 := by
    rw [hqdeg]
    exact Nat.not_lt_zero _
  rw [if_neg hnot_lt]
  unfold divModArray
  have hqzero : q.isZero = false := by
    cases h : q.isZero
    · rfl
    · have hsize0 : q.size = 0 := by
        simp [isZero] at h
        simpa [size] using h
      omega
  rw [if_neg (by simpa [Bool.not_eq_true] using hqzero)]
  let qDegree := q.size - 1
  let quotientSize := p.size - qDegree
  let quot := Array.replicate quotientSize (Zero.zero : R)
  let qr := divModArrayAux q.toArray qDegree (fun coeff => coeff / q.leadingCoeff)
    p.size quot p.toArray
  have hcoeffs_size : q.coeffs.size = 1 := by
    simpa [size] using hqsize
  have hqDegree_zero : qDegree = 0 := by
    dsimp [qDegree]
    omega
  have hsize : q.toArray.size = qDegree + 1 := by
    simp [toArray, hcoeffs_size, hqDegree_zero]
  have hlead : q.toArray.getD qDegree (Zero.zero : R) = q.leadingCoeff := by
    unfold leadingCoeff toArray
    rw [hqDegree_zero]
    change q.coeffs.getD 0 (Zero.zero : R) = q.coeffs.back?.getD (Zero.zero : R)
    rw [Array.getD_eq_getD_getElem?]
    have hidx : 0 < q.coeffs.size := by omega
    rw [Array.getElem?_eq_getElem hidx]
    rw [Array.back?_eq_getElem?]
    have hlast : q.coeffs.size - 1 = 0 := by omega
    rw [hlast, Array.getElem?_eq_getElem hidx]
  have hzero_start :
      ∀ i, qDegree + p.size ≤ i → p.toArray.getD i (Zero.zero : R) = (Zero.zero : R) := by
    intro i hi
    unfold toArray Array.getD
    have hle : p.coeffs.size ≤ i := by
      simpa [size] using (by omega : p.size ≤ i)
    rw [dif_neg (Nat.not_lt.mpr hle)]
  have hzero_final :
      ∀ i, qDegree ≤ i → qr.2.getD i (Zero.zero : R) = (Zero.zero : R) := by
    dsimp [qr, quot]
    apply divModArrayAux_remainder_zero_ge
    · exact hsize
    · intro a
      rw [hlead]
      exact hcancel a
    · exact hzero_start
  apply ext_coeff
  intro i
  rw [coeff_zero]
  change (ofCoeffs qr.2).coeff i = (Zero.zero : R)
  rw [coeff_ofCoeffs]
  exact hzero_final i (by omega)

theorem divMod_remainder_eq_self_of_size_zero_core [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) (hqsize : q.size = 0) :
    (divMod p q).2 = p := by
  unfold divMod
  have hnot_lt : ¬ p.degree?.getD 0 < q.degree?.getD 0 := by
    simp [degree?, hqsize]
  rw [if_neg hnot_lt]
  unfold divModArray
  have hqzero : q.isZero = true := by
    simp [isZero, size] at hqsize ⊢
    simpa [Array.isEmpty_iff_size_eq_zero] using hqsize
  simp [hqzero]

/-- Quotient from polynomial long division over a field. -/
def div [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (divMod p q).1

/-- Remainder from polynomial long division over a field. -/
def mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (divMod p q).2

/-- Remainder from long division by a monic polynomial over a commutative ring. -/
def modByMonic [One R] [Add R] [Sub R] [Mul R]
    (p q : DensePoly R) (hmonic : Monic q) : DensePoly R :=
  (divModMonic p q hmonic).2

instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Div (DensePoly R) where
  div := div

instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Mod (DensePoly R) where
  mod := mod

/-- Commutative-ring divisibility for dense polynomials. -/
instance [Add R] [Mul R] : Dvd (DensePoly R) where
  dvd p q := ∃ r : DensePoly R, q = p * r

/-- Result package for polynomial extended gcd. -/
structure XGCDResult (R : Type u) [Zero R] [DecidableEq R] where
  gcd : DensePoly R
  left : DensePoly R
  right : DensePoly R

/-- Tail-recursive extended Euclidean algorithm. -/
private def xgcdAux [One R] [Add R] [Sub R] [Mul R] [Div R]
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly R) (fuel : Nat) : XGCDResult R :=
  match fuel with
  | 0 => { gcd := r₀, left := s₀, right := t₀ }
  | fuel + 1 =>
      if _hr : r₁.isZero then
        { gcd := r₀, left := s₀, right := t₀ }
      else
        let qr := divMod r₀ r₁
        let q := qr.1
        let r := qr.2
        xgcdAux r₁ s₁ t₁ r (s₀ - q * s₁) (t₀ - q * t₁) fuel

/-- Extended gcd over a field, returning the gcd together with Bezout coefficients. -/
def xgcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : XGCDResult R :=
  xgcdAux p 1 0 q 0 1 (p.size + q.size + 1)

/-- Polynomial gcd over a field. -/
def gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (xgcd p q).gcd

/-- Law package for the executable dense-polynomial division operations.

The algorithms remain available for any coefficient type with the required operations, but
theorems that use long-division invariants should require this class rather than claiming
those invariants for arbitrary, potentially unlawful `Div` and `Sub` instances. -/
class DivModLaws (R : Type u) [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    [Div R] : Prop where
  divMod_spec :
    ∀ p q : DensePoly R,
      let qr := divMod p q
      qr.1 * q + qr.2 = p
  divMod_remainder_degree_lt_of_pos_degree :
    ∀ p q : DensePoly R,
      0 < q.degree?.getD 0 → (divMod p q).2.degree?.getD 0 < q.degree?.getD 0
  divModMonic_eq_divMod_of_monic :
    ∀ (p q : DensePoly R) (hq : Monic q), divModMonic p q hq = divMod p q
  mod_self_eq_zero :
    ∀ p : DensePoly R, p % p = 0
  mod_eq_zero_of_dvd :
    ∀ p q : DensePoly R, q ∣ p → p % q = 0
  mod_mod_of_not_pos_degree :
    ∀ p q : DensePoly R, ¬ 0 < q.degree?.getD 0 → (p % q) % q = p % q
  mod_eq_mod_of_congr :
    ∀ p q m : DensePoly R, m ∣ (p - q) → p % m = q % m
  mod_add_mod :
    ∀ p q m : DensePoly R, (p + q) % m = ((p % m) + (q % m)) % m
  mod_mul_mod :
    ∀ p q m : DensePoly R, (p * q) % m = ((p % m) * (q % m)) % m

/-- Law package for the executable dense-polynomial gcd operations.

The generic algorithms are executable for any coefficient type with the required operations,
but Euclidean gcd correctness is only true for lawful coefficient/division structures. Concrete
coefficient libraries provide this package once they have proved the algorithmic invariants. -/
class GcdLaws (R : Type u) [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    [Div R] : Prop where
  gcd_dvd_left :
    ∀ p q : DensePoly R, gcd p q ∣ p
  gcd_dvd_right :
    ∀ p q : DensePoly R, gcd p q ∣ q
  dvd_gcd :
    ∀ d p q : DensePoly R, d ∣ p → d ∣ q → d ∣ gcd p q
  xgcd_bezout :
    ∀ p q : DensePoly R,
      let r := xgcd p q
      r.left * p + r.right * q = r.gcd

theorem divMod_spec [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  exact DivModLaws.divMod_spec p q

theorem gcd_dvd_left [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    gcd p q ∣ p := by
  exact GcdLaws.gcd_dvd_left p q

theorem gcd_dvd_right [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    gcd p q ∣ q := by
  exact GcdLaws.gcd_dvd_right p q

theorem dvd_gcd [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (d p q : DensePoly R) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  exact GcdLaws.dvd_gcd d p q

theorem xgcd_bezout [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  exact GcdLaws.xgcd_bezout p q

theorem modByMonic_eq_divModMonic [One R] [Add R] [Sub R] [Mul R]
    (p q : DensePoly R) (hq : Monic q) :
    modByMonic p q hq = (divModMonic p q hq).2 := by
  rfl

/-- Zero has zero remainder under monic division. -/
theorem modByMonic_zero [One R] [Add R] [Sub R] [Mul R]
    (q : DensePoly R) (hq : Monic q) :
    modByMonic (0 : DensePoly R) q hq = 0 := by
  unfold modByMonic divModMonic divModArray
  by_cases hqzero : q.isZero
  · simp [hqzero]
  · simp [hqzero, divModArrayAux, toArray]
    change (ofCoeffs (#[] : Array R) : DensePoly R) = 0
    rfl

theorem mod_eq_divMod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p % q = (divMod p q).2 := by
  rfl

theorem divMod_eq_zero_self_of_degree_lt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p.degree?.getD 0 < q.degree?.getD 0 → divMod p q = (0, p) := by
  intro hdeg
  simp [divMod, hdeg]

private theorem ofCoeffs_replicate_zero (n : Nat) :
    (ofCoeffs (Array.replicate n (Zero.zero : R)) : DensePoly R) = 0 := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs]
  change (Array.replicate n (Zero.zero : R)).getD i (Zero.zero : R) = (Zero.zero : R)
  simp [Array.getD]

private theorem ofCoeffs_empty :
    (ofCoeffs (#[] : Array R) : DensePoly R) = 0 := by
  rfl

private theorem ofCoeffs_toArray (p : DensePoly R) :
    ofCoeffs p.toArray = p := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs]
  rfl

private theorem ofCoeffs_set!_eq_add_monomial {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (coeffs : Array S) (shift : Nat) (coeff : S)
    (hshift : shift < coeffs.size)
    (hzero : coeffs.getD shift (Zero.zero : S) = (Zero.zero : S)) :
    (ofCoeffs (coeffs.set! shift coeff) : DensePoly S) =
      ofCoeffs coeffs + monomial shift coeff := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_add_left : ∀ x : S, (Zero.zero : S) + x = x := by
    intro x
    change (0 : S) + x = x
    grind
  have hadd_zero_right : ∀ x : S, x + (Zero.zero : S) = x := by
    intro x
    change x + (0 : S) = x
    grind
  rw [coeff_ofCoeffs]
  rw [coeff_add (ofCoeffs coeffs) (monomial shift coeff) n hzero_add]
  rw [coeff_ofCoeffs, coeff_monomial]
  by_cases hn : n = shift
  · subst n
    rw [array_getD_set!_same]
    · rw [hzero]
      rw [if_pos rfl]
      exact (hzero_add_left coeff).symm
    · exact hshift
  · rw [array_getD_set!_ne]
    · rw [if_neg hn]
      exact (hadd_zero_right (coeffs.getD n (Zero.zero : S))).symm
    · intro h
      exact hn h.symm

theorem divModArray_eq_zero_self_of_degree_lt [Sub R] [Mul R]
    (p q : DensePoly R) (scaleLead : R → R)
    (hdeg : p.degree?.getD 0 < q.degree?.getD 0) :
    divModArray p q scaleLead = (0, p) := by
  unfold divModArray
  by_cases hqzero : q.isZero
  · have hqsize : q.size = 0 := by
      simp [isZero] at hqzero
      simpa [size] using hqzero
    simp [degree?, hqsize] at hdeg
  · rw [if_neg hqzero]
    let qDegree := q.size - 1
    let quotientSize := p.size - qDegree
    let quot := Array.replicate quotientSize (Zero.zero : R)
    have hqpos : 0 < q.size := by
      have hcoeffs : q.coeffs.size ≠ 0 := by
        simpa [isZero, Array.isEmpty_iff_size_eq_zero] using hqzero
      simpa [size, Nat.pos_iff_ne_zero] using hcoeffs
    have hqdeg : q.degree?.getD 0 = qDegree := by
      simp [degree?, qDegree, Nat.ne_of_gt hqpos]
    have hpsize_le : p.size ≤ qDegree := by
      by_cases hppos : 0 < p.size
      · have hpdeg : p.degree?.getD 0 = p.size - 1 := by
          simp [degree?, Nat.ne_of_gt hppos]
        rw [hpdeg, hqdeg] at hdeg
        omega
      · have hpzero : p.size = 0 := by omega
        omega
    have hquot_zero : quotientSize = 0 := by
      dsimp [quotientSize]
      omega
    cases hpsize : p.size with
    | zero =>
        simp [divModArrayAux, ofCoeffs_toArray, ofCoeffs_empty]
    | succ fuel =>
        cases harray : arrayDegree? p.toArray with
        | none =>
            simp [divModArrayAux, ofCoeffs_replicate_zero, ofCoeffs_toArray, harray]
        | some rd =>
            have hrd_lt_size : rd < p.size := by
              simpa [toArray] using arrayDegree?_some_lt harray
            have hrd_lt : rd < qDegree := by omega
            have hrd_lt' : rd < q.size - 1 := by
              simpa [qDegree] using hrd_lt
            have hquot_zero' : fuel + 1 - (q.size - 1) = 0 := by
              have : p.size - qDegree = 0 := by
                simpa [quotientSize] using hquot_zero
              omega
            simp [divModArrayAux, ofCoeffs_toArray, ofCoeffs_empty, harray, hrd_lt',
              hquot_zero']

/-- If field-style coefficient division agrees pointwise with the monic scaling function, then
the executable monic division path agrees with the general `divMod` path away from the early
degree shortcut. -/
theorem divModMonic_eq_divMod_of_monic_core [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) (hq : Monic q)
    (hnot_lt : ¬ p.degree?.getD 0 < q.degree?.getD 0)
    (hscale : ∀ a : R, a / q.leadingCoeff = a) :
    divModMonic p q hq = divMod p q := by
  unfold divModMonic divMod
  rw [if_neg hnot_lt]
  exact (divModArray_scaleLead_congr p q (fun a => hscale a)).symm

/-- Core division invariant: for positive-degree divisors, `divMod` returns a remainder whose
degree is strictly smaller than the divisor degree. -/
theorem divMod_remainder_degree_lt_of_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    0 < q.degree?.getD 0 → (divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  exact DivModLaws.divMod_remainder_degree_lt_of_pos_degree p q

/-- Monic division agrees with field-style division when the divisor is monic. This is the
implementation invariant relating the specialized `divModMonic` path to `divMod`. -/
theorem divModMonic_eq_divMod_of_monic [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) (hq : Monic q) :
    divModMonic p q hq = divMod p q := by
  exact DivModLaws.divModMonic_eq_divMod_of_monic p q hq

/-- A polynomial whose degree is already below the divisor is its own remainder. -/
theorem mod_eq_self_of_degree_lt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p.degree?.getD 0 < q.degree?.getD 0 → p % q = p := by
  intro hdeg
  have hdiv := divMod_eq_zero_self_of_degree_lt p q hdeg
  simpa [DensePoly.mod] using congrArg Prod.snd hdiv

/-- Constant-degree divisors are an idempotent edge case for `%`. -/
theorem mod_mod_of_not_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    ¬ 0 < q.degree?.getD 0 → (p % q) % q = p % q := by
  exact DivModLaws.mod_mod_of_not_pos_degree p q

/-- The computed remainder has degree below a positive-degree divisor. -/
theorem mod_degree_lt_of_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    0 < q.degree?.getD 0 → (p % q).degree?.getD 0 < q.degree?.getD 0 := by
  simpa [DensePoly.mod] using divMod_remainder_degree_lt_of_pos_degree p q

theorem div_mul_add_mod [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    (p / q) * q + (p % q) = p := by
  simpa [DensePoly.div, DensePoly.mod] using divMod_spec p q

theorem mod_eq_zero_of_dvd [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    q ∣ p → p % q = 0 := by
  exact DivModLaws.mod_eq_zero_of_dvd p q

theorem modByMonic_eq_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) (hq : Monic q) :
    modByMonic p q hq = p % q := by
  rw [modByMonic_eq_divModMonic, mod_eq_divMod, divModMonic_eq_divMod_of_monic p q hq]

theorem mod_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    (p % q) % q = p % q := by
  by_cases hq : 0 < q.degree?.getD 0
  · exact mod_eq_self_of_degree_lt (p % q) q (mod_degree_lt_of_pos_degree p q hq)
  · exact mod_mod_of_not_pos_degree p q hq

end DensePoly

namespace DensePoly

private def diagonalMulCoeffTerm {S : Type _} [Zero S] [DecidableEq S] [Mul S]
    (p q : DensePoly S) (n i : Nat) : S :=
  if n < i then 0 else p.coeff i * q.coeff (n - i)

private def boundedDiagonalMulCoeffTerm {S : Type _} [Zero S] [DecidableEq S] [Mul S]
    (p q : DensePoly S) (n i m : Nat) : S :=
  if n < i then 0 else if n - i < m then p.coeff i * q.coeff (n - i) else 0

private theorem fold_mulCoeffStep_eq_bounded_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i m : Nat) (acc : S) :
    (List.range m).foldl (mulCoeffStep p q n i) acc =
      acc + boundedDiagonalMulCoeffTerm p q n i m := by
  induction m generalizing acc with
  | zero =>
      simp [boundedDiagonalMulCoeffTerm]
      grind
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold mulCoeffStep boundedDiagonalMulCoeffTerm
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          grind
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
            grind
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

private theorem fold_mulCoeffStep_eq_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (acc : S) :
    (List.range q.size).foldl (mulCoeffStep p q n i) acc =
      acc + diagonalMulCoeffTerm p q n i := by
  rw [fold_mulCoeffStep_eq_bounded_diagonal]
  unfold boundedDiagonalMulCoeffTerm diagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
  · by_cases hbound : n - i < q.size
    · simp [hlt, hbound]
    · have hcoeff : q.coeff (n - i) = 0 :=
        coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hbound)
      simp [hlt, hbound, hcoeff]
      grind

private theorem fold_mulCoeff_outer_eq_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) (xs : List Nat) (acc : S) :
    xs.foldl (fun coeff i => (List.range q.size).foldl (mulCoeffStep p q n i) coeff) acc =
      xs.foldl (fun coeff i => coeff + diagonalMulCoeffTerm p q n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [fold_mulCoeffStep_eq_diagonal]
      exact ih (acc + diagonalMulCoeffTerm p q n i)

private theorem mulCoeffSum_eq_diagonal {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    mulCoeffSum p q n =
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  unfold mulCoeffSum
  exact fold_mulCoeff_outer_eq_diagonal p q n (List.range p.size) 0

private theorem diagonalMulCoeffTerm_eq_zero_of_size_le {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (hi : p.size ≤ i) :
    diagonalMulCoeffTerm p q n i = 0 := by
  unfold diagonalMulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · have hcoeff : p.coeff i = 0 := coeff_eq_zero_of_size_le p hi
    simp [hn, hcoeff]
    grind

private theorem fold_diagonal_extend {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n d : Nat) :
    (List.range (p.size + d)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : diagonalMulCoeffTerm p q n (p.size + d) = 0 :=
        diagonalMulCoeffTerm_eq_zero_of_size_le p q n (p.size + d) (by omega)
      simp [hterm]
      grind

private theorem diagonalSum_eq_bound {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n m : Nat) (hm : p.size ≤ m) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range m).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  have hm' : p.size + (m - p.size) = m := by omega
  rw [← hm']
  exact (fold_diagonal_extend p q n (m - p.size)).symm

private theorem diagonalMulCoeffTerm_eq_zero_of_degree_lt {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (hi : n < i) :
    diagonalMulCoeffTerm p q n i = 0 := by
  simp [diagonalMulCoeffTerm, hi]

private theorem fold_diagonal_truncate_degree {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n d : Nat) :
    (List.range (n + 1 + d)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : diagonalMulCoeffTerm p q n (n + 1 + d) = 0 :=
        diagonalMulCoeffTerm_eq_zero_of_degree_lt p q n (n + 1 + d) (by omega)
      simp [hterm]
      grind

private theorem diagonalSum_eq_degree_bound {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  by_cases hsize : p.size ≤ n + 1
  · exact diagonalSum_eq_bound p q n (n + 1) hsize
  · have hsize' : n + 1 + (p.size - (n + 1)) = p.size := by omega
    rw [← hsize']
    exact fold_diagonal_truncate_degree p q n (p.size - (n + 1))

private theorem fold_add_right_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List S) (a b : S) :
    xs.foldl (fun acc x => acc + x) (a + b) =
      xs.foldl (fun acc x => acc + x) a + b := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hacc : a + b + x = (a + x) + b := by grind
      rw [hacc]
      exact ih (a + x)

private theorem fold_add_reverse_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List S) (a : S) :
    xs.reverse.foldl (fun acc x => acc + x) a =
      xs.foldl (fun acc x => acc + x) a := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      rw [fold_add_right_commring xs a x]

private theorem range_succ_reverse_eq_map_sub (n : Nat) :
    (List.range (n + 1)).reverse = (List.range (n + 1)).map (fun i => n - i) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.length_reverse] at hleft hright
    rw [List.getElem_reverse]
    simp [List.getElem_map, List.getElem_range]

private theorem diagonalMulCoeffTerm_comm_reindex {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) (hi : i < n + 1) :
    diagonalMulCoeffTerm p q n (n - i) = diagonalMulCoeffTerm q p n i := by
  have hile : i ≤ n := by omega
  have hleft : ¬ n < n - i := by omega
  have hright : ¬ n < i := by omega
  simp [diagonalMulCoeffTerm, hleft, hright, Nat.sub_sub_self hile]
  grind

private theorem fold_diagonal_comm_reindex_list {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) (xs : List Nat)
    (hxs : ∀ i, i ∈ xs → i < n + 1) (acc : S) :
    xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p q n (n - i)) acc =
      xs.foldl (fun acc i => acc + diagonalMulCoeffTerm q p n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hi : i < n + 1 := hxs i (by simp)
      rw [diagonalMulCoeffTerm_comm_reindex p q n i hi]
      exact ih (by
        intro j hj
        exact hxs j (by simp [hj])) (acc + diagonalMulCoeffTerm q p n i)

private theorem fold_diagonal_comm {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm q p n i) 0 := by
  have hrev :
      (List.range (n + 1)).reverse.foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
        (List.range (n + 1)).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
    simpa [List.foldl_map, ← List.map_reverse] using
      fold_add_reverse_commring (S := S)
        ((List.range (n + 1)).map (fun i => diagonalMulCoeffTerm p q n i)) 0
  rw [← hrev]
  rw [range_succ_reverse_eq_map_sub]
  rw [List.foldl_map]
  exact fold_diagonal_comm_reindex_list p q n (List.range (n + 1)) (by
    intro i hi
    exact List.mem_range.mp hi) 0

private theorem diagonalMulCoeffTerm_neg_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n i : Nat) :
    diagonalMulCoeffTerm p (0 - q) n i = 0 - diagonalMulCoeffTerm p q n i := by
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  unfold diagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
    grind
  · rw [coeff_sub 0 q (n - i) hzero_sub, coeff_zero]
    simp [hlt]
    grind

private theorem diagonalSum_neg_right_aux {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) (xs : List Nat) (acc : S) :
    xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p (0 - q) n i) acc =
      acc - xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [diagonalMulCoeffTerm_neg_right]
      rw [ih]
      have htail :=
        fold_add_right_commring (S := S)
          (xs.map (fun i => diagonalMulCoeffTerm p q n i)) 0 (diagonalMulCoeffTerm p q n i)
      simp [List.foldl_map] at htail
      rw [htail]
      grind

private theorem diagonalSum_neg_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p (0 - q) n i) 0 =
      0 -
        (List.range (n + 1)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  exact diagonalSum_neg_right_aux p q n (List.range (n + 1)) 0

theorem mul_sub_zero_comm {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p * (0 - q) = 0 - q * p := by
  apply ext_coeff
  intro n
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_mul, coeff_sub 0 (q * p) n hzero_sub, coeff_zero, coeff_mul]
  rw [mulCoeffSum_eq_diagonal p (0 - q) n, mulCoeffSum_eq_diagonal q p n]
  rw [diagonalSum_eq_degree_bound p (0 - q) n, diagonalSum_eq_degree_bound q p n]
  rw [diagonalSum_neg_right p q n]
  rw [fold_diagonal_comm p q n]

theorem mul_comm_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p * q = q * p := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_diagonal p q n, mulCoeffSum_eq_diagonal q p n]
  rw [diagonalSum_eq_degree_bound p q n, diagonalSum_eq_degree_bound q p n]
  rw [fold_diagonal_comm p q n]

theorem add_sub_add_swap {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (x y z : DensePoly S) :
    (x + y) - (z + x) = y + (0 - z) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_sub (x + y) (z + x) n hzero_sub]
  rw [coeff_add x y n hzero_add, coeff_add z x n hzero_add]
  rw [coeff_add y (0 - z) n hzero_add]
  rw [coeff_sub 0 z n hzero_sub, coeff_zero]
  grind

theorem add_sub_add_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (x y z : DensePoly S) :
    (x + y) - (x + z) = y + (0 - z) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_sub (x + y) (x + z) n hzero_sub]
  rw [coeff_add x y n hzero_add, coeff_add x z n hzero_add]
  rw [coeff_add y (0 - z) n hzero_add]
  rw [coeff_sub 0 z n hzero_sub, coeff_zero]
  grind

theorem add_comm_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p + q = q + p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add p q n hzero_add, coeff_add q p n hzero_add]
  grind

theorem add_assoc_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    p + q + r = p + (q + r) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add (p + q) r n hzero_add]
  rw [coeff_add p q n hzero_add]
  rw [coeff_add p (q + r) n hzero_add]
  rw [coeff_add q r n hzero_add]
  grind

theorem add_zero_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p + 0 = p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add p 0 n hzero_add, coeff_zero]
  grind

theorem sub_eq_add_neg_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    p - q = p + (0 - q) := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_sub p q n hzero_sub]
  rw [coeff_add p (0 - q) n hzero_add]
  rw [coeff_sub 0 q n hzero_sub, coeff_zero]
  grind

private theorem diagonalMulCoeffTerm_one_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) (n i : Nat) :
    diagonalMulCoeffTerm p 1 n i = if i = n then p.coeff n else 0 := by
  unfold diagonalMulCoeffTerm
  by_cases hlt : n < i
  · have hne : i ≠ n := by omega
    simp [hlt, hne]
  · by_cases hin : i = n
    · subst i
      have hone : (1 : DensePoly S).coeff 0 = (1 : S) := by
        change (C (1 : S)).coeff 0 = (1 : S)
        simp [coeff_C]
      simp [hone]
      exact Lean.Grind.Semiring.mul_one (p.coeff n)
    · have hsub_pos : n - i ≠ 0 := by omega
      have hone : (1 : DensePoly S).coeff (n - i) = (0 : S) := by
        change (C (1 : S)).coeff (n - i) = (0 : S)
        simp [coeff_C, hsub_pos]
        rfl
      simp [hlt, hin, hone]
      grind

private theorem fold_single_index {S : Type _}
    [Lean.Grind.CommRing S] (n m : Nat) (x : S) :
    (List.range m).foldl (fun acc i => acc + if i = n then x else 0) 0 =
      if n < m then x else 0 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      by_cases hn : n < m
      · have hne : m ≠ n := by omega
        simp [hn, hne]
        grind
      · by_cases hmn : m = n
        · subst n
          simp
          grind
        · have hn_succ : ¬ n < m + 1 := by omega
          simp [hn, hn_succ, hmn]
          grind

private theorem fold_diagonal_one_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) (n : Nat) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p 1 n i) 0 =
      p.coeff n := by
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p 1 n i) acc =
        xs.foldl (fun acc i => acc + if i = n then p.coeff n else 0) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [diagonalMulCoeffTerm_one_right p n i]
        exact ih (acc + if i = n then p.coeff n else 0)
  rw [show
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p 1 n i) 0 =
        (List.range p.size).foldl (fun acc i => acc + if i = n then p.coeff n else 0) 0 by
    exact hfold (List.range p.size) 0]
  rw [fold_single_index]
  by_cases hn : n < p.size
  · simp [hn]
  · have hcoeff : p.coeff n = 0 := coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hn)
    simp [hn, hcoeff]

private theorem diagonalMulCoeffTerm_add_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n i : Nat) :
    diagonalMulCoeffTerm p (q + r) n i =
      diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i := by
  unfold diagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
    grind
  · have hzero_add : (0 : S) + (0 : S) = 0 := by grind
    rw [coeff_add q r (n - i) hzero_add]
    simp [hlt]
    grind

private theorem fold_add_pair_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f g : Nat → S) (a b : S) :
    xs.foldl (fun acc i => acc + (f i + g i)) (a + b) =
      xs.foldl (fun acc i => acc + f i) a +
        xs.foldl (fun acc i => acc + g i) b := by
  induction xs generalizing a b with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hacc : a + b + (f i + g i) = (a + f i) + (b + g i) := by grind
      rw [hacc]
      exact ih (a + f i) (b + g i)

/-- Pull the initial accumulator out of an additive fold. -/
private theorem fold_add_acc_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f : Nat → S) (acc : S) :
    xs.foldl (fun acc i => acc + f i) acc =
      acc + xs.foldl (fun acc i => acc + f i) 0 := by
  have h :=
    fold_add_right_commring (S := S) (xs.map f) 0 acc
  simp [List.foldl_map] at h
  rw [← show (0 : S) + acc = acc by grind]
  rw [h]
  grind

/-- Flatten a nested additive fold over a mapped list of rows. -/
private theorem fold_add_nested_map_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (row : Nat → List Nat) (F : Nat → Nat → S) (acc : S) :
    xs.foldl
        (fun acc i => acc + (row i).foldl (fun acc j => acc + F i j) 0)
        acc =
      xs.foldl
        (fun acc i => (row i).foldl (fun acc j => acc + F i j) acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [← fold_add_acc_commring (row i) (F i) acc]
      exact ih ((row i).foldl (fun acc j => acc + F i j) acc)

/-- Extending a bounded row by one appends exactly the new boundary term. -/
private theorem triangular_row_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n j : Nat) (hj : j < n + 1) :
    (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0 =
      (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0 +
        F j (n + 1 - j) := by
  have hlen : n + 1 - j + 1 = (n - j + 1) + 1 := by omega
  rw [hlen, List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hidx : n - j + 1 = n + 1 - j := by omega
  rw [hidx]

/-- The first `n + 1` rows of the larger triangle split into the old triangle
plus the new diagonal boundary. -/
private theorem triangular_prefix_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc j =>
          acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
        0 =
      (List.range (n + 1)).foldl
          (fun acc j =>
            acc + (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0)
          0 +
        (List.range (n + 1)).foldl
          (fun acc j => acc + F j (n + 1 - j)) 0 := by
  let oldRow := fun j =>
    (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0
  let newTerm := fun j => F j (n + 1 - j)
  have hfold :
      ∀ (xs : List Nat),
        (∀ j, j ∈ xs → j < n + 1) →
        ∀ acc : S,
        xs.foldl
            (fun acc j =>
              acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
            acc =
          xs.foldl (fun acc j => acc + (oldRow j + newTerm j)) acc := by
    intro xs
    induction xs with
    | nil =>
        intro _hxs acc
        rfl
    | cons j xs ih =>
        intro hxs acc
        simp only [List.foldl_cons]
        rw [triangular_row_succ_commring F n j (hxs j (by simp))]
        exact ih (by
          intro k hk
          exact hxs k (by simp [hk])) (acc + (oldRow j + newTerm j))
  rw [hfold (List.range (n + 1)) (by
    intro j hj
    exact List.mem_range.mp hj) 0]
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  calc
    (List.range (n + 1)).foldl (fun acc j => acc + (oldRow j + newTerm j)) 0 =
        (List.range (n + 1)).foldl (fun acc j => acc + (oldRow j + newTerm j)) (0 + 0) := by
          rw [hzero_add]
    _ =
        (List.range (n + 1)).foldl (fun acc j => acc + oldRow j) 0 +
          (List.range (n + 1)).foldl (fun acc j => acc + newTerm j) 0 := by
        exact fold_add_pair_commring (S := S) (List.range (n + 1)) oldRow newTerm 0 0

/-- Advancing the total-degree triangular enumeration appends the new diagonal. -/
private theorem triangular_total_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1 + 1)).foldl
        (fun acc i =>
          acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
        0 =
      (List.range (n + 1)).foldl
          (fun acc i =>
            acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
          0 +
        (List.range (n + 1 + 1)).foldl
          (fun acc j => acc + F j (n + 1 - j)) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← List.range_succ]

/-- Advancing the first-coordinate triangular enumeration appends the last singleton row. -/
private theorem triangular_first_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1 + 1)).foldl
        (fun acc j =>
          acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
        0 =
      (List.range (n + 1)).foldl
          (fun acc j =>
            acc + (List.range (n + 1 - j + 1)).foldl (fun acc k => acc + F j k) 0)
          0 +
        F (n + 1) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hidx : n + 1 - (n + 1) = 0 := by omega
  simp [hidx]
  grind

/-- The new diagonal splits into the old rows' boundary plus the last corner. -/
private theorem triangular_boundary_succ_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1 + 1)).foldl
        (fun acc j => acc + F j (n + 1 - j)) 0 =
      (List.range (n + 1)).foldl
          (fun acc j => acc + F j (n + 1 - j)) 0 +
        F (n + 1) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hidx : n + 1 - (n + 1) = 0 := by omega
  rw [hidx]

/-- The row-major triangular fold over total degree reindexed by first coordinate.

This is the generic finite reindexing behind convolution associativity:
`i` is the total degree, `j` the first coordinate, and `i - j` the second
coordinate.  The right-hand side enumerates the same finite triangle by
choosing the first coordinate first.
-/
private theorem triangular_fold_reindex_commring {S : Type _} [Lean.Grind.CommRing S]
    (F : Nat → Nat → S) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
        0 =
      (List.range (n + 1)).foldl
        (fun acc j =>
          acc + (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0)
        0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [triangular_total_succ_commring F n]
      rw [triangular_first_succ_commring F n]
      rw [ih]
      rw [triangular_prefix_succ_commring F n]
      rw [triangular_boundary_succ_commring F n]
      grind

private theorem fold_diagonal_add_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n : Nat) :
    (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p (q + r) n i) 0 =
      (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 +
        (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p r n i) 0 := by
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i => acc + diagonalMulCoeffTerm p (q + r) n i) acc =
        xs.foldl
          (fun acc i => acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i))
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [diagonalMulCoeffTerm_add_right p q r n i]
        exact ih (acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i))
  rw [hfold (List.range p.size) 0]
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  calc
    (List.range p.size).foldl
        (fun acc i => acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i)) 0 =
        (List.range p.size).foldl
          (fun acc i => acc + (diagonalMulCoeffTerm p q n i + diagonalMulCoeffTerm p r n i))
          (0 + 0) := by rw [hzero_add]
    _ =
        (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 +
          (List.range p.size).foldl (fun acc i => acc + diagonalMulCoeffTerm p r n i) 0 := by
        exact
          fold_add_pair_commring (S := S) (List.range p.size)
            (fun i => diagonalMulCoeffTerm p q n i)
            (fun i => diagonalMulCoeffTerm p r n i) 0 0

private theorem fold_add_congr {S : Type _} [Add S]
    (xs : List Nat) (f g : Nat → S)
    (hfg : ∀ i, i ∈ xs → f i = g i) (acc : S) :
    xs.foldl (fun acc i => acc + f i) acc =
      xs.foldl (fun acc i => acc + g i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hfg i (by simp)]
      exact ih
        (by
          intro j hj
          exact hfg j (by simp [hj]))
        (acc + g i)

/-- Distribute right multiplication by a constant through an additive fold. -/
private theorem fold_add_mul_right_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f : Nat → S) (c : S) :
    xs.foldl (fun acc i => acc + f i) 0 * c =
      xs.foldl (fun acc i => acc + f i * c) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hzero_f : (0 : S) + f i = f i := by grind
      have hzero_fc : (0 : S) + f i * c = f i * c := by grind
      rw [hzero_f, hzero_fc]
      rw [fold_add_acc_commring xs f (f i)]
      rw [fold_add_acc_commring xs (fun i => f i * c) (f i * c)]
      rw [← ih]
      grind

/-- Distribute left multiplication by a constant through an additive fold. -/
private theorem fold_add_mul_left_commring {S : Type _} [Lean.Grind.CommRing S]
    (xs : List Nat) (f : Nat → S) (c : S) :
    c * xs.foldl (fun acc i => acc + f i) 0 =
      xs.foldl (fun acc i => acc + c * f i) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hzero_f : (0 : S) + f i = f i := by grind
      have hzero_cf : (0 : S) + c * f i = c * f i := by grind
      rw [hzero_f, hzero_cf]
      rw [fold_add_acc_commring xs f (f i)]
      rw [fold_add_acc_commring xs (fun i => c * f i) (c * f i)]
      rw [← ih]
      grind

private theorem diagonal_mul_left_expand {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n i : Nat) (hi : i < n + 1) :
    diagonalMulCoeffTerm (p * q) r n i =
      (List.range (i + 1)).foldl
        (fun acc j => acc + (p.coeff j * q.coeff (i - j)) * r.coeff (n - i)) 0 := by
  have hnot : ¬ n < i := by omega
  simp [diagonalMulCoeffTerm, hnot]
  rw [coeff_mul, mulCoeffSum_eq_diagonal p q i, diagonalSum_eq_degree_bound p q i]
  calc
    (List.range (i + 1)).foldl (fun acc j => acc + diagonalMulCoeffTerm p q i j) 0 *
        r.coeff (n - i) =
        (List.range (i + 1)).foldl
          (fun acc j => acc + diagonalMulCoeffTerm p q i j * r.coeff (n - i)) 0 := by
      exact fold_add_mul_right_commring
        (S := S) (List.range (i + 1))
        (fun j => diagonalMulCoeffTerm p q i j) (r.coeff (n - i))
    _ =
        (List.range (i + 1)).foldl
          (fun acc j => acc + (p.coeff j * q.coeff (i - j)) * r.coeff (n - i)) 0 := by
      apply fold_add_congr
      intro j hj
      have hjlt : j < i + 1 := List.mem_range.mp hj
      have hnotji : ¬ i < j := by omega
      simp [diagonalMulCoeffTerm, hnotji]

private theorem diagonal_mul_right_expand {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n j : Nat) (hj : j < n + 1) :
    diagonalMulCoeffTerm p (q * r) n j =
      (List.range (n - j + 1)).foldl
        (fun acc k => acc + p.coeff j * (q.coeff k * r.coeff (n - j - k))) 0 := by
  have hnot : ¬ n < j := by omega
  simp [diagonalMulCoeffTerm, hnot]
  rw [coeff_mul, mulCoeffSum_eq_diagonal q r (n - j), diagonalSum_eq_degree_bound q r (n - j)]
  calc
    p.coeff j *
        (List.range (n - j + 1)).foldl
          (fun acc k => acc + diagonalMulCoeffTerm q r (n - j) k) 0 =
        (List.range (n - j + 1)).foldl
          (fun acc k => acc + p.coeff j * diagonalMulCoeffTerm q r (n - j) k) 0 := by
      exact fold_add_mul_left_commring
        (S := S) (List.range (n - j + 1))
        (fun k => diagonalMulCoeffTerm q r (n - j) k) (p.coeff j)
    _ =
        (List.range (n - j + 1)).foldl
          (fun acc k => acc + p.coeff j * (q.coeff k * r.coeff (n - j - k))) 0 := by
      apply fold_add_congr
      intro k hk
      have hklt : k < n - j + 1 := List.mem_range.mp hk
      have hnotkn : ¬ n - j < k := by omega
      simp [diagonalMulCoeffTerm, hnotkn]

private theorem fold_diagonal_mul_assoc {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) (n : Nat) :
    (List.range (p * q).size).foldl
        (fun acc i => acc + diagonalMulCoeffTerm (p * q) r n i) 0 =
      (List.range p.size).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p (q * r) n i) 0 := by
  rw [diagonalSum_eq_degree_bound (p * q) r n]
  rw [diagonalSum_eq_degree_bound p (q * r) n]
  let F : Nat → Nat → S := fun j k => p.coeff j * q.coeff k * r.coeff (n - (j + k))
  have hleft :
      (List.range (n + 1)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm (p * q) r n i) 0 =
        (List.range (n + 1)).foldl
          (fun acc i =>
            acc + (List.range (i + 1)).foldl (fun acc j => acc + F j (i - j)) 0)
          0 := by
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    rw [diagonal_mul_left_expand p q r n i hi']
    apply fold_add_congr
    intro j hj
    have hj' : j < i + 1 := List.mem_range.mp hj
    simp [F]
    have hidx : n - i = n - (j + (i - j)) := by omega
    rw [hidx]
  have hright :
      (List.range (n + 1)).foldl
          (fun acc j => acc + diagonalMulCoeffTerm p (q * r) n j) 0 =
        (List.range (n + 1)).foldl
          (fun acc j =>
            acc + (List.range (n - j + 1)).foldl (fun acc k => acc + F j k) 0)
          0 := by
    apply fold_add_congr
    intro j hj
    have hj' : j < n + 1 := List.mem_range.mp hj
    rw [diagonal_mul_right_expand p q r n j hj']
    apply fold_add_congr
    intro k hk
    have hk' : k < n - j + 1 := List.mem_range.mp hk
    simp [F]
    have hidx : n - (j + k) = n - j - k := by omega
    rw [hidx]
    grind
  rw [hleft, hright]
  exact triangular_fold_reindex_commring F n

theorem mul_assoc_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    (p * q) * r = p * (q * r) := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_diagonal (p * q) r n]
  rw [mulCoeffSum_eq_diagonal p (q * r) n]
  exact fold_diagonal_mul_assoc p q r n

theorem mul_add_right_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    p * (q + r) = p * q + p * r := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_mul, coeff_add (p * q) (p * r) n hzero_add, coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_diagonal p (q + r) n]
  rw [mulCoeffSum_eq_diagonal p q n, mulCoeffSum_eq_diagonal p r n]
  exact fold_diagonal_add_right p q r n

theorem mul_add_left_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q r : DensePoly S) :
    (p + q) * r = p * r + q * r := by
  rw [mul_comm_poly (p + q) r, mul_add_right_poly r p q,
    mul_comm_poly r p, mul_comm_poly r q]

theorem mul_one_right_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p * 1 = p := by
  apply ext_coeff
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal]
  exact fold_diagonal_one_right p n

theorem neg_mul_right_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) :
    (0 - p) * q = 0 - p * q := by
  rw [mul_comm_poly (0 - p) q, mul_sub_zero_comm q p]

theorem add_mul_sub_cancel_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p t q r : DensePoly S) :
    (p + t) * q + (r - t * q) = p * q + r := by
  rw [mul_add_left_poly]
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_add (p * q + t * q) (r - t * q) n hzero_add]
  rw [coeff_add (p * q) (t * q) n hzero_add]
  rw [coeff_sub r (t * q) n hzero_sub]
  rw [coeff_add (p * q) r n hzero_add]
  grind

/-- One long-division reconstruction step preserves the accumulated identity
`quot * q + rem`. -/
theorem divMod_reconstruction_step {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (quot term q rem : DensePoly S) :
    (quot + term) * q + (rem - term * q) = quot * q + rem := by
  exact add_mul_sub_cancel_right quot term q rem

/-- The polynomial-level reading of one step of the array-based long-division
remainder update: subtracting `coeff * q * x^shift` from `rem`, in coefficient
form, matches the in-place `subtractScaledShift` array update whenever the
update window stays within `rem`. -/
private theorem ofCoeffs_subtractScaledShift_eq_sub_monomial_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (rem q : Array S) (shift : Nat) (coeff : S)
    (hbound : ∀ j, j < q.size → shift + j < rem.size) :
    ofCoeffs (subtractScaledShift rem q shift coeff) =
      ofCoeffs rem - monomial shift coeff * ofCoeffs q := by
  apply ext_coeff
  intro n
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_ofCoeffs]
  rw [coeff_sub (ofCoeffs rem) (monomial shift coeff * ofCoeffs q) n hzero_sub]
  rw [coeff_ofCoeffs]
  rw [coeff_mul]
  rw [mulCoeffSum_eq_diagonal]
  rw [diagonalSum_eq_degree_bound]
  rw [subtractScaledShift_getD rem q shift coeff n hbound]
  -- Compute each diagonal term using the monomial's coefficient law.
  have hterm : ∀ i,
      diagonalMulCoeffTerm (monomial shift coeff) (ofCoeffs q) n i =
        if i = shift ∧ shift ≤ n
          then coeff * q.getD (n - shift) (Zero.zero : S)
          else 0 := by
    intro i
    unfold diagonalMulCoeffTerm
    rw [coeff_monomial, coeff_ofCoeffs]
    by_cases hni : n < i
    · by_cases hieq : i = shift
      · subst i
        have hshift_gt : ¬ shift ≤ n := by omega
        simp [hni, hshift_gt]
      · simp [hni, hieq]
    · have hile : i ≤ n := by omega
      by_cases hieq : i = shift
      · subst i
        simp [hni, hile]
      · simp [hni, hieq]
        exact Lean.Grind.Semiring.zero_mul _
  -- Lift the term-by-term rewrite to the foldl.
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i =>
          acc + diagonalMulCoeffTerm (monomial shift coeff) (ofCoeffs q) n i) acc =
        xs.foldl (fun acc i =>
          acc + if i = shift ∧ shift ≤ n
            then coeff * q.getD (n - shift) (Zero.zero : S)
            else 0) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [hterm i]
        exact ih _
  rw [hfold (List.range (n + 1)) 0]
  by_cases hshift : shift ≤ n
  · -- Collapse the conjunction `i = shift ∧ shift ≤ n` to `i = shift`.
    have hsimp : ∀ i,
        (if i = shift ∧ shift ≤ n
            then coeff * q.getD (n - shift) (Zero.zero : S)
            else 0) =
        (if i = shift
            then coeff * q.getD (n - shift) (Zero.zero : S)
            else 0) := by
      intro i
      simp [hshift]
    have hfold2 : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else 0) acc =
          xs.foldl (fun acc i =>
            acc + if i = shift
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else 0) acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          rw [hsimp i]
          exact ih _
    rw [hfold2 (List.range (n + 1)) 0]
    rw [fold_single_index]
    have hshift_lt : shift < n + 1 := by omega
    rw [if_pos hshift_lt]
    by_cases hsize : n - shift < q.size
    · rw [if_pos ⟨hshift, hsize⟩]
    · have hand : ¬ (shift ≤ n ∧ n - shift < q.size) := fun ⟨_, h⟩ => hsize h
      rw [if_neg hand]
      have hq0 : q.getD (n - shift) (Zero.zero : S) = (0 : S) := by
        unfold Array.getD
        rw [dif_neg (Nat.not_lt.mpr (Nat.le_of_not_lt hsize))]
        rfl
      rw [hq0]
      grind
  · -- All terms are zero; the fold yields zero.
    have hzero_fold : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else 0) acc = acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have h0 : (if i = shift ∧ shift ≤ n
              then coeff * q.getD (n - shift) (Zero.zero : S)
              else (0 : S)) = 0 := by
            simp [hshift]
          rw [h0]
          rw [show acc + (0 : S) = acc by grind]
          exact ih _
    rw [hzero_fold (List.range (n + 1)) 0]
    have hand : ¬ (shift ≤ n ∧ n - shift < q.size) := fun ⟨h, _⟩ => hshift h
    rw [if_neg hand]
    grind

theorem zero_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    (0 : DensePoly S) * p = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_mul]
  simp [mulCoeffSum]
  rfl

theorem zero_add {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    (0 : DensePoly S) + p = p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add 0 p n hzero_add, coeff_zero]
  grind

/-- Recursive reconstruction invariant for the array-backed long-division loop.
Under the cancellation hypothesis for the leading-coefficient scaling function
together with sparsity bounds on `quot` and `rem`, each step of `divModArrayAux`
preserves the polynomial-level identity `quot * q + rem`. The bound parameter `B`
is chosen freshly per recursive call so that strict descent of the loop's pivot
position keeps the slot of `quot` about to be written zero. -/
private theorem divModArrayAux_reconstruction {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (q : Array S) (qDegree : Nat) (scaleLead : S → S)
    (fuel : Nat) (quot rem : Array S) (B : Nat)
    (hsize_q : q.size = qDegree + 1)
    (hcancel :
      ∀ a : S, a - scaleLead a * q.getD qDegree (Zero.zero : S) = (Zero.zero : S))
    (hzero_rem :
      ∀ i, qDegree + B ≤ i → rem.getD i (Zero.zero : S) = (Zero.zero : S))
    (hzero_quot :
      ∀ i, i < B → quot.getD i (Zero.zero : S) = (Zero.zero : S))
    (hsize_match : rem.size ≤ qDegree + quot.size) :
    (ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).1 : DensePoly S) *
        ofCoeffs q +
      ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).2 =
      ofCoeffs quot * ofCoeffs q + ofCoeffs rem := by
  induction fuel generalizing quot rem B with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold divModArrayAux
      cases hdeg : arrayDegree? rem with
      | none => rfl
      | some rd =>
          by_cases hrd_lt : rd < qDegree
          · simp [hrd_lt]
          · simp [hrd_lt]
            simp only [← Array.set!_eq_setIfInBounds, ← Array.getD_eq_getD_getElem?]
            have hrd_nonzero : rem.getD rd (Zero.zero : S) ≠ (Zero.zero : S) :=
              arrayDegree?_some_coeff_ne_zero hdeg
            have hrd_lt_size : rd < rem.size := arrayDegree?_some_lt hdeg
            have hrd_ge : qDegree ≤ rd := Nat.le_of_not_lt hrd_lt
            have hrd_lt_B : rd < qDegree + B := by
              rcases Nat.lt_or_ge rd (qDegree + B) with hlt | hge
              · exact hlt
              · exact absurd (hzero_rem rd hge) hrd_nonzero
            have hshift_eq : (rd - qDegree) + qDegree = rd := by omega
            have hshift_lt_B : rd - qDegree < B := by omega
            have hshift_lt_quot : rd - qDegree < quot.size := by
              have h1 : rd < qDegree + quot.size :=
                Nat.lt_of_lt_of_le hrd_lt_size hsize_match
              omega
            have hquot_shift_zero :
                quot.getD (rd - qDegree) (Zero.zero : S) = (Zero.zero : S) :=
              hzero_quot _ hshift_lt_B
            have hbound_rem :
                ∀ j, j < q.size → rd - qDegree + j < rem.size := by
              intro j hj
              have hj_le : j ≤ qDegree := by omega
              calc rd - qDegree + j
                  ≤ rd - qDegree + qDegree := Nat.add_le_add_left hj_le _
                _ = rd := hshift_eq
                _ < rem.size := hrd_lt_size
            have hzero_rem_new : ∀ i, qDegree + (rd - qDegree) ≤ i →
                (subtractScaledShift rem q (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).getD i
                  (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              have hi_ge_rd : rd ≤ i := by omega
              rcases Nat.lt_or_eq_of_le hi_ge_rd with hgt | heq
              · rw [subtractScaledShift_getD_above_last rem q (rd - qDegree) qDegree
                  (scaleLead (rem.getD rd (Zero.zero : S))) i hsize_q
                  (by rw [hshift_eq]; exact hgt)]
                exact arrayDegree?_some_above_eq_zero hdeg hgt
              · have hi_eq : i = (rd - qDegree) + qDegree := by omega
                rw [hi_eq]
                apply subtractScaledShift_getD_last_cancel rem q (rd - qDegree) qDegree
                  (scaleLead (rem.getD rd (Zero.zero : S))) hsize_q
                · rw [hshift_eq]; exact hrd_lt_size
                · rw [hshift_eq]
                  exact hcancel (rem.getD rd (Zero.zero : S))
            have hzero_quot_new : ∀ i, i < rd - qDegree →
                (quot.set! (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).getD i
                  (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              rw [array_getD_set!_ne quot i (rd - qDegree) _ (by omega)]
              exact hzero_quot i (Nat.lt_trans hi hshift_lt_B)
            have hsize_match_new :
                (subtractScaledShift rem q (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).size ≤
                  qDegree + (quot.set! (rd - qDegree)
                    (scaleLead (rem.getD rd (Zero.zero : S)))).size := by
              have hrem_size : (subtractScaledShift rem q (rd - qDegree)
                  (scaleLead (rem.getD rd (Zero.zero : S)))).size = rem.size := by
                unfold subtractScaledShift
                exact subtractScaledShift_fold_size rem q (rd - qDegree) _
                  (List.range q.size)
              have hquot_size : (quot.set! (rd - qDegree)
                  (scaleLead (rem.getD rd (Zero.zero : S)))).size = quot.size := by
                simp [Array.set!_eq_setIfInBounds]
              rw [hrem_size, hquot_size]
              exact hsize_match
            have ih_result := ih
              (quot := quot.set! (rd - qDegree)
                (scaleLead (rem.getD rd (Zero.zero : S))))
              (rem := subtractScaledShift rem q (rd - qDegree)
                (scaleLead (rem.getD rd (Zero.zero : S))))
              (B := rd - qDegree)
              hzero_rem_new hzero_quot_new hsize_match_new
            rw [ih_result]
            rw [ofCoeffs_set!_eq_add_monomial quot (rd - qDegree)
              (scaleLead (rem.getD rd (Zero.zero : S))) hshift_lt_quot
              hquot_shift_zero]
            rw [ofCoeffs_subtractScaledShift_eq_sub_monomial_mul rem q (rd - qDegree)
              (scaleLead (rem.getD rd (Zero.zero : S))) hbound_rem]
            exact divMod_reconstruction_step (ofCoeffs quot)
              (monomial (rd - qDegree)
                (scaleLead (rem.getD rd (Zero.zero : S))))
              (ofCoeffs q) (ofCoeffs rem)

/-- Reconstruction identity for array-backed long division: under the cancellation
hypothesis for `scaleLead` against the divisor's leading coefficient, the
quotient/remainder pair returned by `divModArray p q scaleLead` satisfies
`q' * q + r' = p`. -/
theorem divModArray_reconstruction {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (scaleLead : S → S)
    (hcancel : ∀ a : S, a - scaleLead a * q.leadingCoeff = (Zero.zero : S)) :
    (divModArray p q scaleLead).1 * q + (divModArray p q scaleLead).2 = p := by
  unfold divModArray
  by_cases hqzero : q.isZero
  · simp [hqzero]
    rw [zero_mul, zero_add]
  · rw [if_neg hqzero]
    have hqpos : 0 < q.size := by
      have hcoeffs : q.coeffs.size ≠ 0 := by
        simpa [isZero, Array.isEmpty_iff_size_eq_zero] using hqzero
      simpa [size, Nat.pos_iff_ne_zero] using hcoeffs
    have hqsize : q.toArray.size = (q.size - 1) + 1 := by
      have hraw : q.coeffs.size = (q.coeffs.size - 1) + 1 := by
        have hcoeffpos : 0 < q.coeffs.size := by simpa [size] using hqpos
        omega
      simpa [toArray, size] using hraw
    have hlead : q.toArray.getD (q.size - 1) (Zero.zero : S) = q.leadingCoeff := by
      unfold leadingCoeff toArray
      change q.coeffs.getD (q.coeffs.size - 1) (Zero.zero : S) =
        q.coeffs.back?.getD (Zero.zero : S)
      have hcoeffpos : 0 < q.coeffs.size := by simpa [size] using hqpos
      have hidx : q.coeffs.size - 1 < q.coeffs.size :=
        Nat.sub_one_lt_of_lt hcoeffpos
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hidx]
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem hidx]
    have hcancel_array :
        ∀ a, a - scaleLead a * q.toArray.getD (q.size - 1) (Zero.zero : S) =
          (Zero.zero : S) := by
      intro a
      rw [hlead]
      exact hcancel a
    have hzero_rem : ∀ i, (q.size - 1) + p.size ≤ i →
        p.toArray.getD i (Zero.zero : S) = (Zero.zero : S) := by
      intro i hi
      unfold toArray Array.getD
      have hle : p.coeffs.size ≤ i := by
        simpa [size] using (by omega : p.size ≤ i)
      rw [dif_neg (Nat.not_lt.mpr hle)]
    have hzero_quot : ∀ i, i < p.size →
        (Array.replicate (p.size - (q.size - 1)) (Zero.zero : S)).getD i
          (Zero.zero : S) = (Zero.zero : S) := by
      intro i _
      simp [Array.getD]
    have hsize_match : p.toArray.size ≤
        (q.size - 1) + (Array.replicate (p.size - (q.size - 1))
          (Zero.zero : S)).size := by
      have hpsize : p.toArray.size = p.size := by simp [toArray, size]
      have hqsize_replicate :
          (Array.replicate (p.size - (q.size - 1)) (Zero.zero : S)).size =
            p.size - (q.size - 1) := Array.size_replicate
      rw [hpsize, hqsize_replicate]
      omega
    have hreconstr := divModArrayAux_reconstruction
      q.toArray (q.size - 1) scaleLead p.size
      (Array.replicate (p.size - (q.size - 1)) (Zero.zero : S))
      p.toArray p.size hqsize hcancel_array hzero_rem hzero_quot hsize_match
    -- Convert array-level identity to the polynomial-level conclusion.
    have hofq : (ofCoeffs q.toArray : DensePoly S) = q := ofCoeffs_toArray q
    have hofp : (ofCoeffs p.toArray : DensePoly S) = p := ofCoeffs_toArray p
    have hofquot : (ofCoeffs (Array.replicate (p.size - (q.size - 1))
        (Zero.zero : S)) : DensePoly S) = 0 :=
      ofCoeffs_replicate_zero _
    rw [hofq, hofp, hofquot, zero_mul, zero_add] at hreconstr
    exact hreconstr

/-- The nonnegative gcd of the coefficients of an integer polynomial. -/
private def contentNat (p : DensePoly Int) : Nat :=
  p.toArray.toList.foldl (fun acc coeff => Nat.gcd acc coeff.natAbs) 0

/-- The integer content of a polynomial. This is always nonnegative. -/
def content (p : DensePoly Int) : Int :=
  Int.ofNat (contentNat p)

/-- The primitive part obtained by dividing every coefficient by the content. -/
def primitivePart (p : DensePoly Int) : DensePoly Int :=
  let cNat := contentNat p
  if cNat = 0 then
    0
  else
    let c := Int.ofNat cNat
    ofCoeffs <|
      p.toArray.toList.map (fun coeff => coeff / c) |>.toArray

private theorem foldl_gcd_dvd_acc (xs : List Nat) (acc : Nat) :
    xs.foldl (fun g x => Nat.gcd g x) acc ∣ acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      exact Nat.dvd_trans (ih (Nat.gcd acc x)) (Nat.gcd_dvd_left acc x)

private theorem foldl_gcd_dvd_of_mem {xs : List Nat} {x acc : Nat}
    (hx : x ∈ xs) :
    xs.foldl (fun g x => Nat.gcd g x) acc ∣ x := by
  induction xs generalizing acc with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp at hx
      cases hx with
      | inl hxy =>
          subst hxy
          exact Nat.dvd_trans (foldl_gcd_dvd_acc ys (Nat.gcd acc x))
            (Nat.gcd_dvd_right acc x)
      | inr hy =>
          exact ih (acc := Nat.gcd acc y) hy

private theorem contentNat_dvd_coeff (p : DensePoly Int) (n : Nat) :
    (contentNat p : Int) ∣ p.coeff n := by
  by_cases hn : n < p.size
  · rw [Int.ofNat_dvd_left]
    unfold contentNat coeff toArray
    have hmem : p.coeffs[n].natAbs ∈ p.coeffs.toList.map Int.natAbs := by
      apply List.mem_map.mpr
      refine ⟨p.coeffs[n], ?_, rfl⟩
      rw [List.mem_iff_getElem]
      exact ⟨n, by simpa [size] using hn, by simp [Array.getElem_toList]; rfl⟩
    have hfold := foldl_gcd_dvd_of_mem (acc := 0) hmem
    have hcoeff : (p.coeffs.getD n (Zero.zero : Int)).natAbs = p.coeffs[n].natAbs := by
      change (p.coeffs.getD n (0 : Int)).natAbs = p.coeffs[n].natAbs
      rw [Array.getElem_eq_getD (0 : Int)]
    rw [hcoeff]
    simpa only [List.foldl_map] using hfold
  · have hnle : p.size ≤ n := Nat.le_of_not_gt hn
    rw [coeff_eq_zero_of_size_le p hnle]
    exact ⟨0, by rw [Int.mul_zero]; rfl⟩

private theorem dvd_foldl_gcd_of_dvd_mem (xs : List Nat) (d acc : Nat)
    (hacc : d ∣ acc) (hxs : ∀ x, x ∈ xs → d ∣ x) :
    d ∣ xs.foldl (fun g x => Nat.gcd g x) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact Nat.dvd_gcd hacc (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

private theorem dvd_contentNat_of_dvd_coeff (p : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ p.coeff n) :
    d ∣ contentNat p := by
  unfold contentNat
  rw [← List.foldl_map]
  apply dvd_foldl_gcd_of_dvd_mem
  · exact Nat.dvd_zero d
  · intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨coeff, hcoeff, rfl⟩
    rw [List.mem_iff_getElem] at hcoeff
    rcases hcoeff with ⟨n, hn, hget⟩
    have hcoeff_eq : p.coeff n = coeff := by
      have hnArray : n < p.coeffs.size := by
        simpa [toArray] using hn
      have hgetArray : p.coeffs[n] = coeff := by
        simpa [toArray, Array.getElem_toList] using hget
      change p.coeffs.getD n (0 : Int) = coeff
      rw [← Array.getElem_eq_getD (0 : Int)]
      exact hgetArray
    have hdiv := h n
    rw [hcoeff_eq] at hdiv
    rwa [Int.ofNat_dvd_left] at hdiv

private theorem list_getD_map_ediv_zero (c : Int) (coeffs : List Int) (n : Nat) :
    (coeffs.map fun coeff => coeff / c).getD n (Zero.zero : Int) =
      coeffs.getD n (Zero.zero : Int) / c := by
  induction coeffs generalizing n with
  | nil =>
      exact (Int.zero_ediv c).symm
  | cons coeff coeffs ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simpa using ih n

theorem content_mul_primitivePart (p : DensePoly Int) :
    scale (content p) (primitivePart p) = p := by
  apply ext_coeff
  intro n
  calc
    (scale (content p) (primitivePart p)).coeff n =
        content p * (primitivePart p).coeff n := by
          exact coeff_scale (content p) (primitivePart p) n (Int.mul_zero _)
    _ = p.coeff n := by
      by_cases hc : contentNat p = 0
      · have hdiv := contentNat_dvd_coeff p n
        rw [hc] at hdiv
        rcases hdiv with ⟨k, hk⟩
        have hpzero : p.coeff n = 0 := by
          simpa using hk
        simp [content, primitivePart, hc, hpzero]
      · have hpart :
            (primitivePart p).coeff n = p.coeff n / content p := by
          unfold primitivePart content
          rw [if_neg hc]
          rw [coeff_ofCoeffs_list]
          rw [list_getD_map_ediv_zero]
          unfold coeff toArray Array.getD
          by_cases hn : n < p.coeffs.size
          · simp [hn]
          · simp [hn]
        have hmul : content p * (p.coeff n / content p) = p.coeff n := by
          unfold content
          exact Int.mul_ediv_cancel' (contentNat_dvd_coeff p n)
        rw [hpart, hmul]

theorem content_scale_neg_one (p : DensePoly Int) :
    content (scale (-1 : Int) p) = content p := by
  unfold content
  apply congrArg Int.ofNat
  apply Nat.dvd_antisymm
  · apply dvd_contentNat_of_dvd_coeff
    intro n
    have hcoeff := contentNat_dvd_coeff (scale (-1 : Int) p) n
    rw [coeff_scale (-1 : Int) p n (Int.mul_zero (-1 : Int))] at hcoeff
    rcases hcoeff with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have hneg : p.coeff n = -((-1 : Int) * p.coeff n) := by grind
    rw [hneg, hk]
    grind
  · apply dvd_contentNat_of_dvd_coeff
    intro n
    rw [coeff_scale (-1 : Int) p n (Int.mul_zero (-1 : Int))]
    have hcoeff := contentNat_dvd_coeff p n
    rcases hcoeff with ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [hk]
    grind

theorem scale_neg_one_zero :
    scale (-1 : Int) (0 : DensePoly Int) = 0 := by
  apply ext_coeff
  intro n
  rw [coeff_scale (-1 : Int) (0 : DensePoly Int) n (Int.mul_zero (-1 : Int))]
  simp

theorem content_zero :
    content (0 : DensePoly Int) = 0 := by
  rfl

theorem content_C (c : Int) :
    content (C c) = Int.ofNat c.natAbs := by
  unfold content contentNat toArray
  by_cases hc : c = 0
  · simp [hc]
  · rw [coeffs_C_of_ne_zero hc]
    simp

theorem primitivePart_eq_zero_of_content_eq_zero (p : DensePoly Int) (h : content p = 0) :
    primitivePart p = 0 := by
  have hc : contentNat p = 0 := by
    rw [← Int.natCast_eq_zero]
    simpa [content] using h
  simp [primitivePart, hc]

/-- The primitive part of a polynomial with nonzero content has content `1`. -/
theorem primitivePart_primitive (p : DensePoly Int) (h : content p ≠ 0) :
    content (primitivePart p) = 1 := by
  unfold content
  let c := contentNat p
  let q := primitivePart p
  let cp := contentNat q
  have hc : c ≠ 0 := by
    intro hc0
    apply h
    simpa [content, c] using congrArg Int.ofNat hc0
  have hscale : scale (content p) q = p := by
    simpa [q] using content_mul_primitivePart p
  have hmul_dvd_coeff : ∀ n, ((c * cp : Nat) : Int) ∣ p.coeff n := by
    intro n
    have hcoeff := congrArg (fun r : DensePoly Int => r.coeff n) hscale
    change (scale (content p) q).coeff n = p.coeff n at hcoeff
    rw [coeff_scale (content p) q n (Int.mul_zero _)] at hcoeff
    have hcp : (cp : Int) ∣ q.coeff n := by
      simpa [cp, q] using contentNat_dvd_coeff q n
    rcases hcp with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hcoeff, hk]
    simp [content, c, cp]
    grind
  have hmul_dvd_c : c * cp ∣ c := by
    simpa [c, cp] using dvd_contentNat_of_dvd_coeff p (c * cp) hmul_dvd_coeff
  rcases hmul_dvd_c with ⟨k, hk⟩
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc
  have hcp_one : cp = 1 := by
    have hcancel : cp * k = 1 := by
      have hk' : c * 1 = c * (cp * k) := by
        simpa [Nat.mul_assoc] using hk
      exact Nat.eq_of_mul_eq_mul_left hcpos hk'.symm
    exact Nat.eq_one_of_mul_eq_one_right hcancel
  change (cp : Int) = 1
  rw [hcp_one]
  rfl

/-- Construct a polynomial with prescribed residues modulo coprime factors. -/
def polyCRT {S : Type _} [Zero S] [DecidableEq S] [One S] [Add S] [Mul S]
    (a b u v s t : DensePoly S) : DensePoly S :=
  u * t * b + v * s * a

/-- `Congr p q m` means `p` and `q` differ by a multiple of `m`. -/
def Congr {S : Type _} [Zero S] [DecidableEq S] [Add S] [Sub S] [Mul S]
    (p q m : DensePoly S) : Prop :=
  m ∣ (p - q)

private theorem mod_sub_self_eq_mul_neg_div {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p m : DensePoly S) :
    p % m - p = m * (0 - p / m) := by
  have hdiv : (p / m) * m + (p % m) = p := div_mul_add_mod p m
  apply ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly S => x.coeff n) hdiv
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  change (((p / m) * m + (p % m)).coeff n = p.coeff n) at hcoeff
  rw [coeff_add ((p / m) * m) (p % m) n hzero_add] at hcoeff
  rw [coeff_sub (p % m) p n hzero_sub]
  rw [mul_sub_zero_comm m (p / m), coeff_sub 0 ((p / m) * m) n hzero_sub]
  rw [coeff_zero]
  grind

private theorem congr_mod_core {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p m : DensePoly S) :
    m ∣ (p % m - p) := by
  exact ⟨0 - p / m, mod_sub_self_eq_mul_neg_div p m⟩

/-- Reduction modulo the modulus is congruent to the original polynomial over a lawful
coefficient ring. -/
theorem congr_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    (p m : DensePoly S) :
    Congr (p % m) p m := by
  exact congr_mod_core p m

private theorem eq_add_mul_of_sub_eq_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {p q m r : DensePoly S} :
    p - q = m * r -> p = q + m * r := by
  intro hsub
  apply ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly S => x.coeff n) hsub
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  change (p - q).coeff n = (m * r).coeff n at hcoeff
  rw [coeff_sub p q n hzero_sub] at hcoeff
  rw [coeff_add q (m * r) n hzero_add]
  grind

private theorem add_zero_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p + 0 = p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add p 0 n hzero_add]
  simp
  grind

private theorem zero_mul_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    (0 : DensePoly S) * p = 0 := by
  change mul 0 p = 0
  have hzero : (0 : DensePoly S).coeffs = #[] := rfl
  simp [mul, isZero, hzero]

private theorem mod_self_eq_zero {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m : DensePoly S) :
    m % m = 0 := by
  exact DivModLaws.mod_self_eq_zero m

private theorem zero_mod_eq_zero {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m : DensePoly S) :
    (0 : DensePoly S) % m = 0 := by
  change (divMod (0 : DensePoly S) m).2 = 0
  unfold divMod
  have hzero : (0 : DensePoly S).coeffs = #[] := rfl
  have hdeg_zero : (0 : DensePoly S).degree?.getD 0 = 0 := by
    simp [degree?, size, hzero]
  rw [hdeg_zero]
  by_cases hpos : 0 < m.degree?.getD 0
  · simp [hpos]
  · rw [if_neg hpos]
    unfold divModArray
    simp [hzero, isZero, size, toArray, divModArrayAux]
    by_cases hm : m.coeffs = #[]
    · rw [if_pos hm]
    · rw [if_neg hm]
      change (ofCoeffs #[] : DensePoly S) = 0
      rfl

private theorem mod_eq_mod_of_dvd_sub {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    {p q m : DensePoly S} :
    m ∣ (p - q) -> p % m = q % m := by
  exact DivModLaws.mod_eq_mod_of_congr p q m

/-- Congruent polynomials have the same canonical remainder once the divisor law package
supplies the executable `%` invariants. -/
theorem mod_eq_mod_of_congr {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    {p q m : DensePoly S} :
    Congr p q m -> p % m = q % m := by
  exact mod_eq_mod_of_dvd_sub

/-- Reducing both summands before addition preserves the canonical remainder. -/
theorem mod_add_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    (p q m : DensePoly S) :
    (p + q) % m = ((p % m) + (q % m)) % m := by
  exact DivModLaws.mod_add_mod p q m

/-- Reducing both factors before multiplication preserves the canonical remainder. -/
theorem mod_mul_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    (p q m : DensePoly S) :
    (p * q) % m = ((p % m) * (q % m)) % m := by
  exact DivModLaws.mod_mul_mod p q m

private theorem mod_mul_self_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m r : DensePoly S) :
    (m * r) % m = 0 := by
  rw [mod_mul_mod]
  rw [mod_self_eq_zero]
  rw [zero_mul_left]
  rw [zero_mod_eq_zero]

private theorem mod_add_mul_self {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (q m r : DensePoly S) :
    (q + m * r) % m = q % m := by
  apply mod_eq_mod_of_congr
  exact ⟨r, by
    apply ext_coeff
    intro n
    have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
    have hzero_add : (0 : S) + (0 : S) = 0 := by grind
    rw [coeff_sub (q + m * r) q n hzero_sub]
    rw [coeff_add q (m * r) n hzero_add]
    rw [coeff_mul]
    grind⟩

private theorem polyCRT_sub_left_factor {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (a b u v s t : DensePoly S) :
    s * a + t * b = 1 ->
    polyCRT a b u v s t - u = a * (v * s + (0 - u * s)) := by
  intro hbez
  have hu_bez : u * (s * a + t * b) = u := by
    rw [hbez, mul_one_right_poly]
  calc
    polyCRT a b u v s t - u =
        (u * t * b + v * s * a) - u * (s * a + t * b) := by
          rw [hu_bez]
          rfl
    _ = (u * t * b + v * s * a) - (u * (s * a) + u * (t * b)) := by
          rw [mul_add_right_poly]
    _ = (u * t * b + v * s * a) - (u * s * a + u * t * b) := by
          rw [← mul_assoc_poly u s a, ← mul_assoc_poly u t b]
    _ = v * s * a + (0 - u * s * a) := by
          rw [add_sub_add_swap (u * t * b) (v * s * a) (u * s * a)]
    _ = (v * s + (0 - u * s)) * a := by
          rw [mul_add_left_poly, neg_mul_right_poly]
    _ = a * (v * s + (0 - u * s)) := by
          rw [mul_comm_poly]

private theorem polyCRT_sub_right_factor {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (a b u v s t : DensePoly S) :
    s * a + t * b = 1 ->
    polyCRT a b u v s t - v = b * (u * t + (0 - v * t)) := by
  intro hbez
  have hv_bez : v * (s * a + t * b) = v := by
    rw [hbez, mul_one_right_poly]
  calc
    polyCRT a b u v s t - v =
        (u * t * b + v * s * a) - v * (s * a + t * b) := by
          rw [hv_bez]
          rfl
    _ = (u * t * b + v * s * a) - (v * (s * a) + v * (t * b)) := by
          rw [mul_add_right_poly]
    _ = (u * t * b + v * s * a) - (v * s * a + v * t * b) := by
          rw [← mul_assoc_poly v s a, ← mul_assoc_poly v t b]
    _ = (v * s * a + u * t * b) - (v * s * a + v * t * b) := by
          rw [add_comm_poly (u * t * b) (v * s * a)]
    _ = u * t * b + (0 - v * t * b) := by
          rw [add_sub_add_left (v * s * a) (u * t * b) (v * t * b)]
    _ = (u * t + (0 - v * t)) * b := by
          rw [mul_add_left_poly, neg_mul_right_poly]
    _ = b * (u * t + (0 - v * t)) := by
          rw [mul_comm_poly]

private theorem polyCRT_congr_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> s * a + t * b = 1 ->
    Congr (polyCRT a b u v s t) u a := by
  intro S _ _ a b u v s t hbez
  unfold Congr polyCRT
  refine ⟨v * s + (0 - u * s), ?_⟩
  exact polyCRT_sub_left_factor a b u v s t hbez

private theorem polyCRT_congr_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> s * a + t * b = 1 ->
    Congr (polyCRT a b u v s t) v b := by
  intro S _ _ a b u v s t hbez
  unfold Congr polyCRT
  refine ⟨u * t + (0 - v * t), ?_⟩
  exact polyCRT_sub_right_factor a b u v s t hbez

/-- The CRT witness reduces to the prescribed first residue modulo `a` via monic reduction. -/
theorem polyCRT_modByMonic_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) a ha = modByMonic u a ha := by
  intro S _ _ _ _ a b u v s t ha hbez
  rw [modByMonic_eq_mod]
  rw [modByMonic_eq_mod]
  exact mod_eq_mod_of_congr (polyCRT_congr_fst a b u v s t hbez)

/-- The CRT witness reduces to the prescribed first residue modulo `a`. -/
theorem polyCRT_mod_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % a = u % a := by
  intro S _ _ _ _ a b u v s t ha hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_fst a b u v s t ha hbez

/-- The CRT witness reduces to the prescribed second residue modulo `b` via monic reduction. -/
theorem polyCRT_modByMonic_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) b hb = modByMonic v b hb := by
  intro S _ _ _ _ a b u v s t hb hbez
  rw [modByMonic_eq_mod]
  rw [modByMonic_eq_mod]
  exact mod_eq_mod_of_congr (polyCRT_congr_snd a b u v s t hbez)

/-- The CRT witness reduces to the prescribed second residue modulo `b`. -/
theorem polyCRT_mod_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % b = v % b := by
  intro S _ _ _ _ a b u v s t hb hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_snd a b u v s t hb hbez

end DensePoly
end Hex
