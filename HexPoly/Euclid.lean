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

/-- For a nonzero normalized dense polynomial, `leadingCoeff` is the coefficient
at the last stored index. -/
theorem leadingCoeff_eq_coeff_last (p : DensePoly R) (hpos : 0 < p.size) :
    p.leadingCoeff = p.coeff (p.size - 1) := by
  unfold leadingCoeff coeff
  change p.coeffs.back?.getD (Zero.zero : R) =
    p.coeffs.getD (p.coeffs.size - 1) (Zero.zero : R)
  rw [Array.back?_eq_getElem?]
  have hidx : p.coeffs.size - 1 < p.coeffs.size := by
    simpa [size] using Nat.sub_one_lt_of_lt hpos
  rw [Array.getD_eq_getD_getElem?]

/-- The leading coefficient of a nonzero normalized dense polynomial is nonzero. -/
theorem leadingCoeff_ne_zero_of_pos_size (p : DensePoly R) (hpos : 0 < p.size) :
    p.leadingCoeff ≠ (Zero.zero : R) := by
  rw [leadingCoeff_eq_coeff_last p hpos]
  exact coeff_last_ne_zero_of_pos_size p hpos

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

/-- For a positive-degree divisor and any scaling function that cancels the leading coefficient,
the array-backed long-division loop returns a remainder strictly smaller in degree than the
divisor. -/
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

/-- For a positive-degree divisor, the field-style `divMod` returns a remainder strictly smaller
in degree, given an explicit cancellation hypothesis for the coefficient ring. Concrete coefficient
libraries discharge `hcancel` once and re-export this as the unconditional
`divMod_remainder_degree_lt_of_pos_degree` via the `DivModLaws` instance. -/
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

/-- For a size-one (degree-zero, nonzero) divisor, the field-style `divMod` returns zero
remainder, given an explicit cancellation hypothesis for the coefficient ring. Concrete coefficient
libraries discharge `hcancel` once and re-export the result via the `DivModLaws` instance. -/
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

/-- Dividing by a size-zero (zero) polynomial returns the dividend as remainder.
The companion `divMod_eq_zero_self_of_size_zero_core` gives the full quotient-and-remainder pair. -/
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

/-- Dividing by a size-zero dense polynomial returns zero quotient and the
original dividend as remainder. -/
theorem divMod_eq_zero_self_of_size_zero_core [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) (hqsize : q.size = 0) :
    divMod p q = (0, p) := by
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

/-- The `/` notation on dense polynomials dispatches to `DensePoly.div`. -/
instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Div (DensePoly R) where
  div := div

/-- The `%` notation on dense polynomials dispatches to `DensePoly.mod`. -/
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

/-- The gcd component returned by `xgcd` is the executable gcd. -/
theorem xgcd_gcd_eq_gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    (xgcd p q).gcd = gcd p q := rfl

/-- The executable gcd of two zero dense polynomials is zero. -/
@[simp] theorem gcd_zero_zero [One R] [Add R] [Sub R] [Mul R] [Div R] :
    gcd (0 : DensePoly R) (0 : DensePoly R) = 0 := by
  rfl

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

/-- Euclidean division spec: the field-style quotient and remainder reconstruct the dividend. -/
theorem divMod_spec [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  exact DivModLaws.divMod_spec p q

/-- The polynomial gcd divides the left argument. -/
theorem gcd_dvd_left [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    gcd p q ∣ p := by
  exact GcdLaws.gcd_dvd_left p q

/-- The polynomial gcd divides the right argument. -/
theorem gcd_dvd_right [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    gcd p q ∣ q := by
  exact GcdLaws.gcd_dvd_right p q

/-- Every common divisor of `p` and `q` divides `gcd p q`. -/
theorem dvd_gcd [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (d p q : DensePoly R) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  exact GcdLaws.dvd_gcd d p q

/-- Bezout identity: the extended-gcd coefficients reconstruct the gcd as
`left * p + right * q`. -/
theorem xgcd_bezout [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  exact GcdLaws.xgcd_bezout p q

/-- `modByMonic` is definitionally the second component of `divModMonic`. -/
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

/-- The `%` notation unfolds to the second component of `divMod`. -/
theorem mod_eq_divMod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p % q = (divMod p q).2 := by
  rfl

/-- Zero has zero remainder for the executable division algorithm. -/
theorem zero_mod_eq_zero_core {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
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

/-- If the dividend already has degree strictly below the divisor, `divMod` short-circuits to
`(0, p)` without entering the long-division loop. -/
theorem divMod_eq_zero_self_of_degree_lt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p.degree?.getD 0 < q.degree?.getD 0 → divMod p q = (0, p) := by
  intro hdeg
  simp [divMod, hdeg]

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

/-- The array-backed long-division loop also short-circuits to `(0, p)` when the dividend
already has degree below the divisor. -/
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

/-- Euclidean division identity: `(p / q) * q + (p % q) = p`. -/
theorem div_mul_add_mod [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    (p / q) * q + (p % q) = p := by
  simpa [DensePoly.div, DensePoly.mod] using divMod_spec p q

/-- If `q ∣ p`, then `p % q = 0`. -/
theorem mod_eq_zero_of_dvd [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    q ∣ p → p % q = 0 := by
  exact DivModLaws.mod_eq_zero_of_dvd p q

/-- Monic division and the generic `%` notation agree when the divisor is monic. -/
theorem modByMonic_eq_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) (hq : Monic q) :
    modByMonic p q hq = p % q := by
  rw [modByMonic_eq_divModMonic, mod_eq_divMod, divModMonic_eq_divMod_of_monic p q hq]

/-- The remainder modulo `q` is idempotent under `% q`. -/
@[simp] theorem mod_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
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

private theorem rat_fold_add_range_succ (A : Nat → Rat) (m : Nat) :
    (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl (fun acc i => acc + A i) 0 + A m := by
  rw [List.range_succ, List.foldl_append]
  simp

private theorem rat_weighted_diagonal_fold_aux
    (A : Nat → Rat) (m : Nat) :
    ((m : Nat) : Rat) *
        (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl
          (fun acc i => acc + ((i + 1 : Nat) : Rat) * A (i + 1)) 0 +
        (List.range m).foldl
          (fun acc i => acc + ((m - i : Nat) : Rat) * A i) 0 := by
  induction m with
  | zero =>
      simp
      grind
  | succ m ih =>
      rw [rat_fold_add_range_succ A (m + 1)]
      have hsplit :
          (((m + 1 : Nat) : Rat) *
              ((List.range (m + 1)).foldl (fun acc i => acc + A i) 0 + A (m + 1))) =
            ((m : Nat) : Rat) *
                (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              ((m + 1 : Nat) : Rat) * A (m + 1) := by
        have hnat : ((m + 1 : Nat) : Rat) = ((m : Nat) : Rat) + 1 := by
          simp
        rw [hnat]
        grind
      rw [hsplit, ih]
      rw [rat_fold_add_range_succ
        (fun i => ((i + 1 : Nat) : Rat) * A (i + 1)) m]
      rw [rat_fold_add_range_succ
        (fun i => ((m + 1 - i : Nat) : Rat) * A i) m]
      rw [rat_fold_add_range_succ A m]
      have htail : ((m + 1 - m : Nat) : Rat) * A m = A m := by
        simp
      rw [htail]
      have hcoeff :
          (List.range m).foldl
              (fun acc i => acc + ((m - i : Nat) : Rat) * A i) 0 +
            (List.range m).foldl (fun acc i => acc + A i) 0 =
          (List.range m).foldl
              (fun acc i => acc + ((m + 1 - i : Nat) : Rat) * A i) 0 := by
        rw [← fold_add_pair_commring (S := Rat) (List.range m)
          (fun i => ((m - i : Nat) : Rat) * A i) (fun i => A i) 0 0]
        rw [show (0 : Rat) + 0 = 0 by grind]
        apply fold_add_congr
        intro i hi
        have hi' : i < m := List.mem_range.mp hi
        have hnat : ((m + 1 - i : Nat) : Rat) =
            ((m - i : Nat) : Rat) + 1 := by
          have h : m + 1 - i = m - i + 1 := by omega
          rw [h]
          simp
        rw [hnat]
        grind
      rw [← hcoeff]
      grind

private theorem rat_weighted_diagonal_fold
    (A : Nat → Rat) (n : Nat) :
    ((n + 1 : Nat) : Rat) *
        (List.range (n + 2)).foldl (fun acc i => acc + A i) 0 =
      (List.range (n + 1)).foldl
          (fun acc i => acc + ((i + 1 : Nat) : Rat) * A (i + 1)) 0 +
        (List.range (n + 1)).foldl
          (fun acc i => acc + ((n - i + 1 : Nat) : Rat) * A i) 0 := by
  have h := rat_weighted_diagonal_fold_aux A (n + 1)
  rw [show n + 1 + 1 = n + 2 by omega] at h
  exact h.trans (by
    congr 1
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hidx : n + 1 - i = n - i + 1 := by omega
    rw [hidx])

private theorem rat_coeff_derivative_generic (p : DensePoly Rat) (n : Nat) :
    (derivative p).coeff n = ((n + 1 : Nat) : Rat) * p.coeff (n + 1) := by
  unfold derivative
  rw [coeff_ofCoeffs_list]
  change
    ((List.range (p.size - 1)).map
        (fun i => ((i + 1 : Nat) : Rat) * p.coeff (i + 1))).getD n 0 =
      ((n + 1 : Nat) : Rat) * p.coeff (n + 1)
  by_cases hn : n < p.size - 1
  · simp [hn, List.getD]
  · have hp : p.size ≤ n + 1 := by omega
    have hcoeff : p.coeff (n + 1) = 0 :=
      coeff_eq_zero_of_size_le p hp
    simp [hn, List.getD, hcoeff]

theorem rat_mulCoeffSum_derivative_product_rule
    (p q : DensePoly Rat) (n : Nat) :
    ((n + 1 : Nat) : Rat) * mulCoeffSum p q (n + 1) =
      mulCoeffSum (derivative p) q n + mulCoeffSum p (derivative q) n := by
  rw [mulCoeffSum_eq_diagonal p q (n + 1)]
  rw [diagonalSum_eq_degree_bound p q (n + 1)]
  rw [mulCoeffSum_eq_diagonal (derivative p) q n]
  rw [diagonalSum_eq_degree_bound (derivative p) q n]
  rw [mulCoeffSum_eq_diagonal p (derivative q) n]
  rw [diagonalSum_eq_degree_bound p (derivative q) n]
  have hleft :
      (List.range (n + 2)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm p q (n + 1) i) 0 =
        (List.range (n + 2)).foldl
          (fun acc i => acc + p.coeff i * q.coeff (n + 1 - i)) 0 := by
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 2 := List.mem_range.mp hi
    have hnot : ¬ n + 1 < i := by omega
    simp [diagonalMulCoeffTerm, hnot]
  rw [hleft]
  rw [rat_weighted_diagonal_fold (fun i => p.coeff i * q.coeff (n + 1 - i)) n]
  congr 1
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, rat_coeff_derivative_generic p i]
    have hidx : n - i = n + 1 - (i + 1) := by omega
    rw [hidx]
    grind
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, rat_coeff_derivative_generic q (n - i)]
    have hidx : n - i + 1 = n + 1 - i := by omega
    rw [hidx]
    grind

section CommRingDerivative

variable {S : Type _} [Lean.Grind.CommRing S]

attribute [local instance 1100] Lean.Grind.Semiring.natCast

private theorem fold_add_range_succ_commring (A : Nat → S) (m : Nat) :
    (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl (fun acc i => acc + A i) 0 + A m := by
  rw [List.range_succ, List.foldl_append]
  simp

private theorem weighted_diagonal_fold_aux_commring
    (A : Nat → S) (m : Nat) :
    ((m : Nat) : S) *
        (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 =
      (List.range m).foldl
          (fun acc i => acc + ((i + 1 : Nat) : S) * A (i + 1)) 0 +
        (List.range m).foldl
          (fun acc i => acc + ((m - i : Nat) : S) * A i) 0 := by
  induction m with
  | zero =>
      simp
      have h0 : ((0 : Nat) : S) = 0 := Lean.Grind.Semiring.natCast_zero
      grind
  | succ m ih =>
      rw [fold_add_range_succ_commring A (m + 1)]
      have hsplit :
          (((m + 1 : Nat) : S) *
              ((List.range (m + 1)).foldl (fun acc i => acc + A i) 0 + A (m + 1))) =
            ((m : Nat) : S) *
                (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              (List.range (m + 1)).foldl (fun acc i => acc + A i) 0 +
              ((m + 1 : Nat) : S) * A (m + 1) := by
        rw [Lean.Grind.Semiring.natCast_succ]
        grind
      rw [hsplit, ih]
      rw [fold_add_range_succ_commring
        (fun i => ((i + 1 : Nat) : S) * A (i + 1)) m]
      rw [fold_add_range_succ_commring
        (fun i => ((m + 1 - i : Nat) : S) * A i) m]
      rw [fold_add_range_succ_commring A m]
      have htail : ((m + 1 - m : Nat) : S) * A m = A m := by
        have hsub : m + 1 - m = 1 := by omega
        rw [hsub, Lean.Grind.Semiring.natCast_one]
        grind
      rw [htail]
      have hcoeff :
          (List.range m).foldl
              (fun acc i => acc + ((m - i : Nat) : S) * A i) 0 +
            (List.range m).foldl (fun acc i => acc + A i) 0 =
          (List.range m).foldl
              (fun acc i => acc + ((m + 1 - i : Nat) : S) * A i) 0 := by
        rw [← fold_add_pair_commring (S := S) (List.range m)
          (fun i => ((m - i : Nat) : S) * A i) (fun i => A i) 0 0]
        rw [show (0 : S) + 0 = 0 by grind]
        apply fold_add_congr
        intro i hi
        have hi' : i < m := List.mem_range.mp hi
        have hnat : ((m + 1 - i : Nat) : S) =
            ((m - i : Nat) : S) + 1 := by
          have h : m + 1 - i = m - i + 1 := by omega
          rw [h, Lean.Grind.Semiring.natCast_succ]
        rw [hnat]
        grind
      rw [← hcoeff]
      grind

private theorem weighted_diagonal_fold_commring
    (A : Nat → S) (n : Nat) :
    ((n + 1 : Nat) : S) *
        (List.range (n + 2)).foldl (fun acc i => acc + A i) 0 =
      (List.range (n + 1)).foldl
          (fun acc i => acc + ((i + 1 : Nat) : S) * A (i + 1)) 0 +
        (List.range (n + 1)).foldl
          (fun acc i => acc + ((n - i + 1 : Nat) : S) * A i) 0 := by
  have h := weighted_diagonal_fold_aux_commring A (n + 1)
  rw [show n + 1 + 1 = n + 2 by omega] at h
  exact h.trans (by
    congr 1
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hidx : n + 1 - i = n - i + 1 := by omega
    rw [hidx])

theorem mulCoeffSum_derivative_product_rule [DecidableEq S]
    (p q : DensePoly S) (n : Nat) :
    ((n + 1 : Nat) : S) * mulCoeffSum p q (n + 1) =
      mulCoeffSum (derivative p) q n + mulCoeffSum p (derivative q) n := by
  rw [mulCoeffSum_eq_diagonal p q (n + 1)]
  rw [diagonalSum_eq_degree_bound p q (n + 1)]
  rw [mulCoeffSum_eq_diagonal (derivative p) q n]
  rw [diagonalSum_eq_degree_bound (derivative p) q n]
  rw [mulCoeffSum_eq_diagonal p (derivative q) n]
  rw [diagonalSum_eq_degree_bound p (derivative q) n]
  have hleft :
      (List.range (n + 2)).foldl
          (fun acc i => acc + diagonalMulCoeffTerm p q (n + 1) i) 0 =
        (List.range (n + 2)).foldl
          (fun acc i => acc + p.coeff i * q.coeff (n + 1 - i)) 0 := by
    apply fold_add_congr
    intro i hi
    have hi' : i < n + 2 := List.mem_range.mp hi
    have hnot : ¬ n + 1 < i := by omega
    simp [diagonalMulCoeffTerm, hnot]
  rw [hleft]
  rw [weighted_diagonal_fold_commring (fun i => p.coeff i * q.coeff (n + 1 - i)) n]
  congr 1
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, coeff_derivative_semiring p i]
    have hidx : n - i = n + 1 - (i + 1) := by omega
    rw [hidx]
    grind
  · apply fold_add_congr
    intro i hi
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hnot : ¬ n < i := by omega
    unfold diagonalMulCoeffTerm
    simp [hnot, coeff_derivative_semiring q (n - i)]
    have hidx : n - i + 1 = n + 1 - i := by omega
    rw [hidx]
    grind

theorem derivative_mul [DecidableEq S]
    (p q : DensePoly S) :
    derivative (p * q) =
      derivative p * q + p * derivative q := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_derivative_semiring]
  rw [coeff_mul p q (n + 1)]
  rw [coeff_add (derivative p * q) (p * derivative q) n
    (Lean.Grind.Semiring.add_zero (0 : S))]
  rw [coeff_mul (derivative p) q n]
  rw [coeff_mul p (derivative q) n]
  exact mulCoeffSum_derivative_product_rule p q n

end CommRingDerivative

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

/-- Product of two monomials: `xⁱ * cⱼ * xʲ = cᵢcⱼ * xⁱ⁺ʲ`. -/
theorem monomial_mul_monomial {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (m k : Nat) (c d : S) :
    (monomial m c) * (monomial k d) = monomial (m + k) (c * d) := by
  apply ext_coeff
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound]
  rw [coeff_monomial]
  have hterm : ∀ i,
      diagonalMulCoeffTerm (monomial m c) (monomial k d) n i =
        if i = m ∧ n = m + k then c * d else 0 := by
    intro i
    unfold diagonalMulCoeffTerm
    rw [coeff_monomial, coeff_monomial]
    by_cases hni : n < i
    · have hcond : ¬ (i = m ∧ n = m + k) := by
        intro ⟨h1, h2⟩; omega
      rw [if_pos hni, if_neg hcond]
    · have hile : i ≤ n := Nat.le_of_not_gt hni
      rw [if_neg hni]
      by_cases him : i = m
      · subst i
        rw [if_pos rfl]
        by_cases hnmk : n - m = k
        · have hn : n = m + k := by omega
          rw [if_pos hnmk]
          simp [hn]
        · have hn : n ≠ m + k := by omega
          rw [if_neg hnmk]
          have hcond : ¬ (m = m ∧ n = m + k) := fun ⟨_, h⟩ => hn h
          rw [if_neg hcond]
          -- c * Zero.zero = 0.
          show c * (Zero.zero : S) = 0
          have : (Zero.zero : S) = 0 := rfl
          rw [this]
          grind
      · rw [if_neg him]
        have hcond : ¬ (i = m ∧ n = m + k) := fun ⟨h, _⟩ => him h
        rw [if_neg hcond]
        -- Zero.zero * anything = 0.
        exact Lean.Grind.Semiring.zero_mul _
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i =>
          acc + diagonalMulCoeffTerm (monomial m c) (monomial k d) n i) acc =
        xs.foldl (fun acc i =>
          acc + if i = m ∧ n = m + k then c * d else 0) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [hterm i]
        exact ih _
  rw [hfold (List.range (n + 1)) 0]
  by_cases hnmk : n = m + k
  · have hsimp : ∀ i,
        (if i = m ∧ n = m + k then c * d else 0) =
          (if i = m then c * d else 0) := fun i => by simp [hnmk]
    have hfold2 : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i => acc + if i = m ∧ n = m + k then c * d else 0) acc =
          xs.foldl (fun acc i => acc + if i = m then c * d else 0) acc := by
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
    have hm_lt : m < n + 1 := by omega
    rw [if_pos hm_lt, if_pos hnmk]
  · have hzero_fold : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i => acc + if i = m ∧ n = m + k then c * d else 0) acc = acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have hcond : ¬ (i = m ∧ n = m + k) := fun ⟨_, h⟩ => hnmk h
          rw [if_neg hcond]
          rw [show acc + (0 : S) = acc by grind]
          exact ih _
    rw [hzero_fold]
    rw [if_neg hnmk]
    rfl

/-- Multiplication by a unit-coefficient monomial shifts coefficients upward. -/
theorem monomial_one_mul_poly_eq_shift {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (shift : Nat) (q : DensePoly S) :
    monomial shift 1 * q = DensePoly.shift shift q := by
  apply ext_coeff
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound]
  rw [coeff_shift]
  have hterm : ∀ i,
      diagonalMulCoeffTerm (monomial shift 1) q n i =
        if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0 := by
    intro i
    unfold diagonalMulCoeffTerm
    rw [coeff_monomial]
    by_cases hni : n < i
    · have hcond : ¬(i = shift ∧ shift ≤ n) := by
        intro h
        omega
      simp [hni, hcond]
    · have hile : i ≤ n := by omega
      by_cases hishift : i = shift
      · subst i
        simp [hni, hile]
        grind
      · simp [hni, hishift]
        exact Lean.Grind.Semiring.zero_mul _
  have hfold : ∀ (xs : List Nat) (acc : S),
      xs.foldl (fun acc i =>
          acc + diagonalMulCoeffTerm (monomial shift 1) q n i) acc =
        xs.foldl (fun acc i =>
          acc + if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [hterm i]
        exact ih _
  rw [hfold (List.range (n + 1)) 0]
  by_cases hshift : shift ≤ n
  · rw [if_neg (by omega : ¬n < shift)]
    have hsimp : ∀ i,
        (if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) =
          if i = shift then q.coeff (n - shift) else 0 := by
      intro i
      simp [hshift]
    have hfold2 : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) acc =
          xs.foldl (fun acc i =>
            acc + if i = shift then q.coeff (n - shift) else 0) acc := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          rw [hsimp i]
          exact ih _
    rw [hfold2 (List.range (n + 1)) 0]
    rw [fold_single_index]
    rw [if_pos (by omega : shift < n + 1)]
  · rw [if_pos (by omega : n < shift)]
    have hzero_fold : ∀ (xs : List Nat) (acc : S),
        xs.foldl (fun acc i =>
            acc + if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) acc = acc := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          rfl
      | cons i xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have hzero :
              (if i = shift ∧ shift ≤ n then q.coeff (n - shift) else 0) = 0 := by
            simp [hshift]
          rw [hzero]
          rw [show acc + (0 : S) = acc by grind]
          exact ih _
    rw [hzero_fold]
    rfl

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

private theorem eq_zero_of_isZero_true {S : Type _} [Zero S] [DecidableEq S]
    (p : DensePoly S) (h : p.isZero = true) :
    p = 0 := by
  apply ext_coeff
  intro n
  have hsize : p.size = 0 := by
    simpa [isZero, size, Array.isEmpty_iff_size_eq_zero] using h
  rw [coeff_zero]
  exact coeff_eq_zero_of_size_le p (by omega)

private theorem isZero_zero {S : Type _} [Zero S] [DecidableEq S] :
    (0 : DensePoly S).isZero = true := by
  rfl

private theorem degree_getD_lt_size_add_one {S : Type _} [Zero S] [DecidableEq S]
    (p : DensePoly S) :
    p.degree?.getD 0 < p.size + 1 := by
  by_cases hsize : p.size = 0
  · simp [degree?, hsize]
  · have hdeg : p.degree?.getD 0 = p.size - 1 := by
      simp [degree?, hsize]
    omega

theorem dvd_refl_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p ∣ p := by
  exact ⟨1, (mul_one_right_poly p).symm⟩

theorem dvd_zero_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p ∣ 0 := by
  exact ⟨0, by rw [mul_comm_poly p 0, zero_mul]⟩

theorem dvd_mul_left_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {d p : DensePoly S} (q : DensePoly S) :
    d ∣ p → d ∣ q * p := by
  intro h
  rcases h with ⟨a, ha⟩
  refine ⟨q * a, ?_⟩
  rw [ha, ← mul_assoc_poly q d a, mul_comm_poly q d, mul_assoc_poly d q a]

theorem dvd_add_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {d p q : DensePoly S} :
    d ∣ p → d ∣ q → d ∣ p + q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [ha, hb, mul_add_right_poly]

theorem dvd_sub_poly {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {d p q : DensePoly S} :
    d ∣ p → d ∣ q → d ∣ p - q := by
  intro hp hq
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  refine ⟨a + (0 - b), ?_⟩
  rw [sub_eq_add_neg_poly, ha, hb, mul_add_right_poly, mul_sub_zero_comm, mul_comm_poly b d]

private theorem xgcdAux_gcd_eq_left_of_right_zero {S : Type _}
    [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat) (hr₁ : r₁ = 0) :
    (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd = r₀ := by
  cases fuel with
  | zero =>
      simp [xgcdAux]
  | succ fuel =>
      simp [xgcdAux, hr₁, isZero_zero]

private theorem xgcd_bezout_step {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (a s₀ t₀ s₁ t₁ p q : DensePoly S) :
    (s₀ - a * s₁) * p + (t₀ - a * t₁) * q =
      (s₀ * p + t₀ * q) - a * (s₁ * p + t₁ * q) := by
  rw [sub_eq_add_neg_poly s₀ (a * s₁), sub_eq_add_neg_poly t₀ (a * t₁)]
  rw [mul_add_left_poly, mul_add_left_poly]
  rw [neg_mul_right_poly, neg_mul_right_poly]
  rw [mul_assoc_poly a s₁ p, mul_assoc_poly a t₁ q]
  rw [mul_add_right_poly]
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  rw [coeff_add (s₀ * p + (0 - a * (s₁ * p))) (t₀ * q + (0 - a * (t₁ * q))) n
    hzero_add]
  rw [coeff_add (s₀ * p) (0 - a * (s₁ * p)) n hzero_add]
  rw [coeff_sub 0 (a * (s₁ * p)) n hzero_sub, coeff_zero]
  rw [coeff_add (t₀ * q) (0 - a * (t₁ * q)) n hzero_add]
  rw [coeff_sub 0 (a * (t₁ * q)) n hzero_sub, coeff_zero]
  rw [coeff_sub (s₀ * p + t₀ * q) (a * (s₁ * p) + a * (t₁ * q)) n hzero_sub]
  rw [coeff_add (s₀ * p) (t₀ * q) n hzero_add]
  rw [coeff_add (a * (s₁ * p)) (a * (t₁ * q)) n hzero_add]
  grind

private theorem xgcdAux_bezout {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p q r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat)
    (hr₀ : s₀ * p + t₀ * q = r₀)
    (hr₁ : s₁ * p + t₁ * q = r₁) :
    let r := xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel
    r.left * p + r.right * q = r.gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      simpa [xgcdAux] using hr₀
  | succ fuel ih =>
      unfold xgcdAux
      by_cases hr₁zero : r₁.isZero
      · simp [hr₁zero, hr₀]
      · simp [hr₁zero]
        let qr := divMod r₀ r₁
        let r := qr.2
        let s := s₀ - qr.1 * s₁
        let t := t₀ - qr.1 * t₁
        apply ih r₁ s₁ t₁ r s t
        · exact hr₁
        · have hspec : qr.1 * r₁ + qr.2 = r₀ := by
            simpa [qr] using DivModLaws.divMod_spec r₀ r₁
          calc
            s * p + t * q
                = (s₀ * p + t₀ * q) - qr.1 * (s₁ * p + t₁ * q) := by
                  exact xgcd_bezout_step qr.1 s₀ t₀ s₁ t₁ p q
            _ = r₀ - qr.1 * r₁ := by rw [hr₀, hr₁]
            _ = qr.2 := by
              have h : r₀ = qr.1 * r₁ + qr.2 := hspec.symm
              rw [h]
              apply ext_coeff
              intro n
              have hzero_add : (0 : S) + (0 : S) = 0 := by grind
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              rw [coeff_sub]
              · rw [coeff_add]
                · grind
                · exact hzero_add
              · exact hzero_sub

theorem xgcd_bezout_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p q : DensePoly S) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  unfold xgcd
  apply xgcdAux_bezout p q
  · rw [mul_comm_poly (1 : DensePoly S) p, mul_one_right_poly, zero_mul, add_zero_poly]
  · rw [zero_mul, mul_comm_poly (1 : DensePoly S) q, mul_one_right_poly, zero_add]

private theorem xgcdAux_common_dvd_gcd {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (d r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat)
    (hr₀ : d ∣ r₀) (hr₁ : d ∣ r₁) :
    d ∣ (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      simpa [xgcdAux] using hr₀
  | succ fuel ih =>
      unfold xgcdAux
      by_cases hr₁zero : r₁.isZero
      · simp [hr₁zero, hr₀]
      · simp [hr₁zero]
        let qr := divMod r₀ r₁
        let rem := qr.2
        apply ih
        · exact hr₁
        · have hspec : qr.1 * r₁ + rem = r₀ := by
            simpa [qr, rem] using DivModLaws.divMod_spec r₀ r₁
          have hrem : rem = r₀ - qr.1 * r₁ := by
            rw [← hspec]
            apply ext_coeff
            intro n
            have hzero_add : (0 : S) + (0 : S) = 0 := by grind
            have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
            rw [coeff_sub]
            · rw [coeff_add]
              · grind
              · exact hzero_add
            · exact hzero_sub
          change d ∣ rem
          rw [hrem]
          exact dvd_sub_poly hr₀ (dvd_mul_left_poly qr.1 hr₁)

private theorem xgcdAux_gcd_dvd_inputs {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (hsmall :
      ∀ p q : DensePoly S,
        q.isZero = false → ¬ 0 < q.degree?.getD 0 → (divMod p q).2 = 0)
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly S) (fuel : Nat)
    (hfuel : r₁.degree?.getD 0 < fuel) :
    (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd ∣ r₀ ∧
      (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd ∣ r₁ := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      omega
  | succ fuel ih =>
      unfold xgcdAux
      by_cases hr₁zero : r₁.isZero
      · simp only [hr₁zero, ↓reduceDIte]
        exact ⟨dvd_refl_poly r₀, by
          rw [eq_zero_of_isZero_true r₁ hr₁zero]
          exact dvd_zero_poly r₀⟩
      · simp only [hr₁zero]
        let qr := divMod r₀ r₁
        let rem := qr.2
        have hr₁false : r₁.isZero = false := by
          cases h : r₁.isZero <;> simp [h] at hr₁zero ⊢
        change (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) fuel).gcd ∣ r₀ ∧
          (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) fuel).gcd ∣ r₁
        by_cases hpos : 0 < r₁.degree?.getD 0
        · have hrem_degree : rem.degree?.getD 0 < r₁.degree?.getD 0 := by
            simpa [qr, rem] using
              DivModLaws.divMod_remainder_degree_lt_of_pos_degree r₀ r₁ hpos
          have hrem_fuel : rem.degree?.getD 0 < fuel := by omega
          have hrec := ih r₁ s₁ t₁ rem (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) hrem_fuel
          have hg_r₁ : (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁)
              (t₀ - qr.1 * t₁) fuel).gcd ∣ r₁ := hrec.1
          have hg_rem : (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁)
              (t₀ - qr.1 * t₁) fuel).gcd ∣ rem := hrec.2
          constructor
          · have hspec : qr.1 * r₁ + rem = r₀ := by
              simpa [qr, rem] using DivModLaws.divMod_spec r₀ r₁
            rw [← hspec]
            exact dvd_add_poly (dvd_mul_left_poly qr.1 hg_r₁) hg_rem
          · exact hg_r₁
        · have hrem_zero : rem = 0 := by
            simpa [qr, rem] using hsmall r₀ r₁ hr₁false hpos
          have hg_eq : (xgcdAux r₁ s₁ t₁ rem (s₀ - qr.1 * s₁)
              (t₀ - qr.1 * t₁) fuel).gcd = r₁ := by
            exact xgcdAux_gcd_eq_left_of_right_zero r₁ s₁ t₁ rem
              (s₀ - qr.1 * s₁) (t₀ - qr.1 * t₁) fuel hrem_zero
          constructor
          · rw [hg_eq]
            have hspec : qr.1 * r₁ + rem = r₀ := by
              simpa [qr, rem] using DivModLaws.divMod_spec r₀ r₁
            rw [hrem_zero, add_zero_poly] at hspec
            rw [← hspec]
            exact dvd_mul_left_poly qr.1 (dvd_refl_poly r₁)
          · rw [hg_eq]
            exact dvd_refl_poly r₁

theorem gcd_dvd_left_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (hsmall :
      ∀ p q : DensePoly S,
        q.isZero = false → ¬ 0 < q.degree?.getD 0 → (divMod p q).2 = 0)
    (p q : DensePoly S) :
    gcd p q ∣ p := by
  unfold gcd xgcd
  exact (xgcdAux_gcd_dvd_inputs hsmall p 1 0 q 0 1 (p.size + q.size + 1)
    (by
      have hq := degree_getD_lt_size_add_one q
      omega)).1

theorem gcd_dvd_right_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (hsmall :
      ∀ p q : DensePoly S,
        q.isZero = false → ¬ 0 < q.degree?.getD 0 → (divMod p q).2 = 0)
    (p q : DensePoly S) :
    gcd p q ∣ q := by
  unfold gcd xgcd
  exact (xgcdAux_gcd_dvd_inputs hsmall p 1 0 q 0 1 (p.size + q.size + 1)
    (by
      have hq := degree_getD_lt_size_add_one q
      omega)).2

theorem dvd_gcd_of_divModLaws {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (d p q : DensePoly S) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  intro hdp hdq
  unfold gcd xgcd
  exact xgcdAux_common_dvd_gcd d p 1 0 q 0 1 (p.size + q.size + 1) hdp hdq

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

/-- Reconstruction identity for the executable long division wrapper. -/
theorem divMod_reconstruction {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (p q : DensePoly S)
    (hcancel : ∀ a : S, a - (a / q.leadingCoeff) * q.leadingCoeff = (Zero.zero : S)) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  unfold divMod
  by_cases hdeg : p.degree?.getD 0 < q.degree?.getD 0
  · simp [hdeg]
    rw [zero_mul, zero_add]
  · simp [hdeg]
    exact divModArray_reconstruction p q (fun coeff => coeff / q.leadingCoeff) hcancel

private theorem foldl_add_general_eq_last_of_below_zero {S : Type _}
    [Lean.Grind.CommRing S]
    (g : Nat → S) (k : Nat)
    (h : ∀ i, i < k → g i = 0) :
    (List.range (k + 1)).foldl (fun acc i => acc + g i) 0 = g k := by
  have hzero : ∀ m, m ≤ k →
      (List.range m).foldl (fun acc i => acc + g i) 0 = 0 := by
    intro m hm
    induction m with
    | zero => simp
    | succ m' ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (Nat.le_of_succ_le hm)]
        have hg : g m' = 0 := h m' (Nat.lt_of_succ_le hm)
        rw [hg]
        grind
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hzero k (Nat.le_refl k)]
  grind

private theorem foldl_add_general_eq_at_predecessor {S : Type _}
    [Lean.Grind.CommRing S]
    (g : Nat → S) (psize : Nat) (hpsize : 0 < psize)
    (h : ∀ i, i < psize - 1 → g i = 0) :
    (List.range psize).foldl (fun acc i => acc + g i) 0 = g (psize - 1) := by
  have hpsize_eq : psize - 1 + 1 = psize := by omega
  rw [← hpsize_eq]
  exact foldl_add_general_eq_last_of_below_zero g (psize - 1) h

private theorem foldl_add_general_eq_zero_of_forall_zero {S : Type _}
    [Lean.Grind.CommRing S]
    (g : Nat → S) (xs : List Nat) (acc : S)
    (h : ∀ i, i ∈ xs → g i = 0) :
    xs.foldl (fun acc i => acc + g i) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hi : g i = 0 := h i List.mem_cons_self
      rw [hi]
      have hadd : acc + (0 : S) = acc := by grind
      rw [hadd]
      exact ih acc (fun j hj => h j (List.mem_cons_of_mem i hj))

/-- The top coefficient of a product of nonzero dense polynomials over any
commutative ring is the product of their top coefficients. -/
private theorem coeff_mul_top_general {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S)
    (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).coeff (p.size - 1 + (q.size - 1)) =
      p.coeff (p.size - 1) * q.coeff (q.size - 1) := by
  rw [coeff_mul, mulCoeffSum_eq_diagonal]
  rw [foldl_add_general_eq_at_predecessor _ p.size hp]
  · unfold diagonalMulCoeffTerm
    have hno : ¬ p.size - 1 + (q.size - 1) < p.size - 1 := by omega
    rw [if_neg hno]
    have hsub : p.size - 1 + (q.size - 1) - (p.size - 1) = q.size - 1 := by omega
    rw [hsub]
  · intro i hi
    unfold diagonalMulCoeffTerm
    have hno : ¬ p.size - 1 + (q.size - 1) < i := by omega
    rw [if_neg hno]
    have hsub : q.size ≤ p.size - 1 + (q.size - 1) - i := by omega
    rw [coeff_eq_zero_of_size_le q hsub]
    show p.coeff i * (Zero.zero : S) = 0
    have hzero_eq : (Zero.zero : S) = 0 := rfl
    rw [hzero_eq]
    grind

/-- Above the degree-sum top, the product of dense polynomials over any
commutative ring vanishes. -/
private theorem coeff_mul_above_top_general {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) {i : Nat}
    (hp : 0 < p.size) (hq : 0 < q.size)
    (hi : p.size - 1 + (q.size - 1) < i) :
    (p * q).coeff i = 0 := by
  rw [coeff_mul, mulCoeffSum_eq_diagonal]
  apply foldl_add_general_eq_zero_of_forall_zero
  intro k hk
  have hk_lt : k < p.size := List.mem_range.mp hk
  unfold diagonalMulCoeffTerm
  by_cases hlt : i < k
  · simp [hlt]
  · have hsub_ge : q.size ≤ i - k := by omega
    rw [if_neg hlt, coeff_eq_zero_of_size_le q hsub_ge]
    show p.coeff k * (Zero.zero : S) = 0
    have hzero_eq : (Zero.zero : S) = 0 := rfl
    rw [hzero_eq]
    grind

/-- If a polynomial's coefficients are all zero from some index onward, its
stored size is bounded by that index. -/
private theorem size_le_of_coeff_zero_above {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {p : DensePoly S} {N : Nat}
    (h : ∀ i, N ≤ i → p.coeff i = 0) :
    p.size ≤ N := by
  by_cases hle : p.size ≤ N
  · exact hle
  · exfalso
    have hlt : N < p.size := Nat.lt_of_not_ge hle
    have hpos : 0 < p.size := by omega
    have hpos' : N ≤ p.size - 1 := by omega
    have hzero : p.coeff (p.size - 1) = 0 := h (p.size - 1) hpos'
    have hne : p.coeff (p.size - 1) ≠ (Zero.zero : S) :=
      coeff_last_ne_zero_of_pos_size p hpos
    exact hne hzero

/-- Array-level "polynomial-multiple" reconstruction-and-termination identity
for `divModArrayAux`. When the running remainder coincides at the polynomial
level with `m * q` for some `DensePoly` factor `m`, and the leading-coefficient
scaling function exactly recovers any `a` from `a * lc`, the loop terminates
with a clean quotient `quot + m` and zero remainder.

This is the structural lemma used to derive the non-monic exact-multiple
public divMod identity in `HexPolyZ`. -/
private theorem divModArrayAux_eq_of_polynomial_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (q : Array S) (qDegree : Nat)
    (hsize_q : q.size = qDegree + 1)
    (hq_lc_ne : q.getD qDegree (Zero.zero : S) ≠ (Zero.zero : S))
    (scaleLead : S → S)
    (hexact : ∀ a : S, scaleLead (a * q.getD qDegree (Zero.zero : S)) = a)
    (h_top_ne : ∀ a : S, a ≠ (Zero.zero : S) →
        a * q.getD qDegree (Zero.zero : S) ≠ (Zero.zero : S))
    (fuel : Nat) (quot rem : Array S) (B : Nat) (m : DensePoly S)
    (hsize_match : rem.size ≤ qDegree + quot.size)
    (hzero_quot : ∀ i, i < B → quot.getD i (Zero.zero : S) = (Zero.zero : S))
    (hzero_rem : ∀ i, qDegree + B ≤ i → rem.getD i (Zero.zero : S) = (Zero.zero : S))
    (hm_size_le : m.size ≤ B)
    (h_inv : (ofCoeffs rem : DensePoly S) = m * ofCoeffs q)
    (hfuel : B ≤ fuel) :
    ((ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).1 : DensePoly S) =
        ofCoeffs quot + m) ∧
      ((ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot rem).2 : DensePoly S) =
        (0 : DensePoly S)) := by
  -- Structural facts about ofCoeffs q: its size is qDegree + 1 and its leading
  -- coefficient is q.getD qDegree 0.
  have hofq_coeff : ∀ i, (ofCoeffs q : DensePoly S).coeff i = q.getD i (Zero.zero : S) :=
    fun i => coeff_ofCoeffs q i
  have hofq_size : (ofCoeffs q : DensePoly S).size = qDegree + 1 := by
    apply Nat.le_antisymm
    · apply size_le_of_coeff_zero_above
      intro i hi
      rw [hofq_coeff]
      unfold Array.getD
      have hnot : ¬ i < q.size := by omega
      exact dif_neg hnot
    · by_cases hge : qDegree + 1 ≤ (ofCoeffs q : DensePoly S).size
      · exact hge
      · exfalso
        have hle : (ofCoeffs q : DensePoly S).size ≤ qDegree := by omega
        have hzero : (ofCoeffs q : DensePoly S).coeff qDegree = 0 :=
          coeff_eq_zero_of_size_le _ hle
        rw [hofq_coeff] at hzero
        exact hq_lc_ne hzero
  -- Algebraic top-coefficient computation: (m * ofCoeffs q).coeff (m.size - 1 + qDegree)
  -- = m.leadingCoeff * q.getD qDegree 0 whenever m is nonzero.
  have hcoeff_top : ∀ (m' : DensePoly S), 0 < m'.size →
      (m' * ofCoeffs q).coeff (m'.size - 1 + qDegree) =
        m'.coeff (m'.size - 1) * q.getD qDegree (Zero.zero : S) := by
    intro m' hm'_pos
    have hofq_pos : 0 < (ofCoeffs q : DensePoly S).size := by rw [hofq_size]; omega
    have htop := coeff_mul_top_general m' (ofCoeffs q) hm'_pos hofq_pos
    rw [hofq_size] at htop
    have hsub_qd : qDegree + 1 - 1 = qDegree := by omega
    rw [hsub_qd, hofq_coeff] at htop
    exact htop
  -- Above-top vanishing: (m * ofCoeffs q).coeff i = 0 for i > m.size - 1 + qDegree.
  have hcoeff_above : ∀ (m' : DensePoly S) (i : Nat), 0 < m'.size →
      m'.size - 1 + qDegree < i → (m' * ofCoeffs q).coeff i = 0 := by
    intro m' i hm'_pos hi
    have hofq_pos : 0 < (ofCoeffs q : DensePoly S).size := by rw [hofq_size]; omega
    apply coeff_mul_above_top_general m' (ofCoeffs q) hm'_pos hofq_pos
    rw [hofq_size]; omega
  induction fuel generalizing quot rem B m with
  | zero =>
      -- B ≤ 0 forces B = 0, so m.size = 0, so m = 0.
      have hB_zero : B = 0 := by omega
      have hm_size : m.size = 0 := by omega
      have hm_zero : m = 0 := by
        apply ext_coeff
        intro i
        rw [coeff_zero]
        exact coeff_eq_zero_of_size_le m (by omega)
      have hrem_zero : (ofCoeffs rem : DensePoly S) = 0 := by
        rw [h_inv, hm_zero, zero_mul]
      refine ⟨?_, hrem_zero⟩
      simp [divModArrayAux]
      rw [hm_zero, add_zero_poly]
  | succ fuel ih =>
      unfold divModArrayAux
      cases hdeg : arrayDegree? rem with
      | none =>
          -- All entries of rem are zero, so m * ofCoeffs q = 0; this forces m = 0.
          have hrem_arr_zero : ∀ i, rem.getD i (Zero.zero : S) = (Zero.zero : S) :=
            fun i => arrayDegree?_none_getD_eq_zero hdeg
          have hrem_zero : (ofCoeffs rem : DensePoly S) = 0 := by
            apply ext_coeff
            intro i
            rw [coeff_ofCoeffs, coeff_zero]
            exact hrem_arr_zero i
          have hm_zero : m = 0 := by
            by_cases hmz : m = 0
            · exact hmz
            · exfalso
              have hm_pos : 0 < m.size := by
                by_cases h : 0 < m.size
                · exact h
                · exfalso
                  apply hmz
                  apply ext_coeff
                  intro i
                  rw [coeff_zero]
                  exact coeff_eq_zero_of_size_le m (by omega)
              have hlead_ne : m.coeff (m.size - 1) ≠ 0 :=
                coeff_last_ne_zero_of_pos_size m hm_pos
              have hprod_ne :
                  m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) ≠
                    (Zero.zero : S) :=
                h_top_ne _ hlead_ne
              have hkey : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) ≠ 0 := by
                rw [hcoeff_top m hm_pos]; exact hprod_ne
              have hzero_at : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) = 0 := by
                rw [← h_inv, hrem_zero, coeff_zero]
              exact hkey hzero_at
          refine ⟨?_, hrem_zero⟩
          rw [hm_zero, add_zero_poly]
      | some rd =>
          have hrd_lt : rd < rem.size := arrayDegree?_some_lt hdeg
          have hrd_nonzero : rem.getD rd (Zero.zero : S) ≠ (Zero.zero : S) :=
            arrayDegree?_some_coeff_ne_zero hdeg
          have hrd_lt_B : rd < qDegree + B := by
            rcases Nat.lt_or_ge rd (qDegree + B) with hlt | hge
            · exact hlt
            · exact absurd (hzero_rem rd hge) hrd_nonzero
          by_cases hrd_lt_q : rd < qDegree
          · -- Loop exits: must show m = 0 (otherwise contradicting arrayDegree above bound).
            have hm_zero : m = 0 := by
              by_cases hmz : m = 0
              · exact hmz
              · exfalso
                have hm_pos : 0 < m.size := by
                  by_cases h : 0 < m.size
                  · exact h
                  · exfalso
                    apply hmz
                    apply ext_coeff
                    intro i
                    rw [coeff_zero]
                    exact coeff_eq_zero_of_size_le m (by omega)
                have hlead_ne : m.coeff (m.size - 1) ≠ 0 :=
                  coeff_last_ne_zero_of_pos_size m hm_pos
                have hprod_ne :
                    m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) ≠
                      (Zero.zero : S) :=
                  h_top_ne _ hlead_ne
                have hkey : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) ≠ 0 := by
                  rw [hcoeff_top m hm_pos]; exact hprod_ne
                have hrem_coeff_ne :
                    rem.getD (m.size - 1 + qDegree) (Zero.zero : S) ≠ 0 := by
                  rw [← coeff_ofCoeffs, h_inv]; exact hkey
                -- m.size - 1 + qDegree ≥ qDegree > rd, so this is above the topmost
                -- nonzero entry, contradicting arrayDegree's contract.
                have habove : rd < m.size - 1 + qDegree := by omega
                exact hrem_coeff_ne (arrayDegree?_some_above_eq_zero hdeg habove)
            have hrem_zero : (ofCoeffs rem : DensePoly S) = 0 := by
              rw [h_inv, hm_zero, zero_mul]
            refine ⟨?_, ?_⟩
            · simp [hrd_lt_q]
              rw [hm_zero, add_zero_poly]
            · simp [hrd_lt_q]
              exact hrem_zero
          · -- Recursive step: m must be nonzero, rd = qDegree + m.size - 1, and we
            -- peel off the leading monomial of m.
            have hm_ne : m ≠ 0 := by
              intro hmz
              apply hrd_nonzero
              have hzero : (ofCoeffs rem : DensePoly S) = 0 := by
                rw [h_inv, hmz, zero_mul]
              have h := congrArg (fun p : DensePoly S => p.coeff rd) hzero
              change (ofCoeffs rem).coeff rd = (0 : DensePoly S).coeff rd at h
              rw [coeff_ofCoeffs, coeff_zero] at h
              exact h
            have hm_pos : 0 < m.size := by
              by_cases h : 0 < m.size
              · exact h
              · exfalso
                apply hm_ne
                apply ext_coeff
                intro i
                rw [coeff_zero]
                exact coeff_eq_zero_of_size_le m (by omega)
            -- Establish rd = qDegree + m.size - 1.
            have hrd_ge : qDegree + m.size - 1 ≤ rd := by
              have hlead_ne : m.coeff (m.size - 1) ≠ 0 :=
                coeff_last_ne_zero_of_pos_size m hm_pos
              have hprod_ne :
                  m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) ≠
                    (Zero.zero : S) :=
                h_top_ne _ hlead_ne
              have hkey : (m * ofCoeffs q).coeff (m.size - 1 + qDegree) ≠ 0 := by
                rw [hcoeff_top m hm_pos]; exact hprod_ne
              have hrem_ne_at :
                  rem.getD (m.size - 1 + qDegree) (Zero.zero : S) ≠ 0 := by
                rw [← coeff_ofCoeffs, h_inv]; exact hkey
              by_cases hle : m.size - 1 + qDegree ≤ rd
              · omega
              · exfalso
                have hgt : rd < m.size - 1 + qDegree := by omega
                exact hrem_ne_at (arrayDegree?_some_above_eq_zero hdeg hgt)
            have hrd_le : rd ≤ qDegree + m.size - 1 := by
              by_cases hle : rd ≤ qDegree + m.size - 1
              · exact hle
              · exfalso
                have hgt : m.size - 1 + qDegree < rd := by omega
                have habove := hcoeff_above m rd hm_pos hgt
                have hrem_eq : rem.getD rd (Zero.zero : S) = 0 := by
                  rw [← coeff_ofCoeffs, h_inv]; exact habove
                exact hrd_nonzero hrem_eq
            have hrd_eq : rd = qDegree + m.size - 1 := by omega
            have hshift_eq : rd - qDegree = m.size - 1 := by omega
            -- Compute coeff = scaleLead(rem.getD rd 0) = m.leadingCoeff.
            have hrem_at_rd :
                rem.getD rd (Zero.zero : S) =
                  m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S) := by
              rw [← coeff_ofCoeffs, h_inv]
              have hrd_alt : rd = m.size - 1 + qDegree := by omega
              rw [hrd_alt]
              exact hcoeff_top m hm_pos
            have hscale :
                scaleLead (rem.getD rd (Zero.zero : S)) = m.coeff (m.size - 1) := by
              rw [hrem_at_rd]
              exact hexact (m.coeff (m.size - 1))
            -- Abbreviations: shift := rd - qDegree, coeff := scaleLead (rem.getD rd 0).
            -- We use let-bindings so the names appear in the IH instantiation.
            let shift : Nat := rd - qDegree
            let coeff : S := scaleLead (rem.getD rd (Zero.zero : S))
            let m_new : DensePoly S := m - monomial shift coeff
            let quot' : Array S := quot.set! shift coeff
            let rem' : Array S := subtractScaledShift rem q shift coeff
            have hcoeff_eq : coeff = m.coeff (m.size - 1) := hscale
            have hshift_eq_size : shift = m.size - 1 := by
              show rd - qDegree = m.size - 1; omega
            have hshift_lt_quot : shift < quot.size := by
              show rd - qDegree < quot.size
              have h1 : rd < qDegree + quot.size :=
                Nat.lt_of_lt_of_le hrd_lt hsize_match
              omega
            have hquot_shift_zero :
                quot.getD shift (Zero.zero : S) = (Zero.zero : S) := by
              apply hzero_quot
              show rd - qDegree < B; omega
            have hbound_rem : ∀ j, j < q.size → shift + j < rem.size := by
              intro j hj
              have hj_le : j ≤ qDegree := by omega
              show rd - qDegree + j < rem.size
              calc rd - qDegree + j
                  ≤ rd - qDegree + qDegree := Nat.add_le_add_left hj_le _
                _ = rd := by omega
                _ < rem.size := hrd_lt
            have hm_new_size : m_new.size ≤ shift := by
              apply size_le_of_coeff_zero_above
              intro i hi
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              show (m - monomial shift coeff).coeff i = 0
              rw [coeff_sub m (monomial shift coeff) i hzero_sub]
              rw [coeff_monomial]
              by_cases hi_eq : i = shift
              · subst i
                rw [if_pos rfl, hcoeff_eq, hshift_eq_size]
                grind
              · rw [if_neg hi_eq]
                have hi_gt : shift < i := by omega
                have hi_ge_size : m.size ≤ i := by
                  have hsize_lt : m.size - 1 < i := by
                    rw [← hshift_eq_size]; exact hi_gt
                  omega
                rw [coeff_eq_zero_of_size_le m hi_ge_size]
                grind
            have hrem'_invariant :
                (ofCoeffs rem' : DensePoly S) = m_new * ofCoeffs q := by
              show (ofCoeffs (subtractScaledShift rem q shift coeff) : DensePoly S) =
                (m - monomial shift coeff) * ofCoeffs q
              rw [ofCoeffs_subtractScaledShift_eq_sub_monomial_mul rem q shift coeff hbound_rem]
              rw [h_inv]
              apply ext_coeff
              intro n
              have hzero_add : (0 : S) + (0 : S) = 0 := by grind
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              rw [coeff_sub (m * ofCoeffs q) (monomial shift coeff * ofCoeffs q) n hzero_sub]
              -- Use add_mul_sub_cancel_right with r = 0 to derive the distributive law.
              have hcancel :
                  (m - monomial shift coeff) + monomial shift coeff = m := by
                apply ext_coeff
                intro k
                rw [coeff_add (m - monomial shift coeff) (monomial shift coeff) k hzero_add]
                rw [coeff_sub m (monomial shift coeff) k hzero_sub]
                grind
              have hrhs := congrArg (fun p : DensePoly S => p.coeff n)
                (add_mul_sub_cancel_right (m - monomial shift coeff)
                  (monomial shift coeff) (ofCoeffs q) 0)
              rw [hcancel] at hrhs
              change ((m * ofCoeffs q + (0 - monomial shift coeff * ofCoeffs q)).coeff n =
                ((m - monomial shift coeff) * ofCoeffs q + 0).coeff n) at hrhs
              rw [coeff_add (m * ofCoeffs q) (0 - monomial shift coeff * ofCoeffs q) n hzero_add] at hrhs
              rw [coeff_sub 0 (monomial shift coeff * ofCoeffs q) n hzero_sub,
                coeff_zero] at hrhs
              rw [coeff_add ((m - monomial shift coeff) * ofCoeffs q) 0 n hzero_add,
                coeff_zero] at hrhs
              grind
            have hquot'_size : quot'.size = quot.size := by
              show (quot.set! shift coeff).size = quot.size
              simp [Array.set!_eq_setIfInBounds]
            have hrem'_size : rem'.size = rem.size := by
              show (subtractScaledShift rem q shift coeff).size = rem.size
              unfold subtractScaledShift
              exact subtractScaledShift_fold_size rem q shift coeff (List.range q.size)
            have hsize_match' : rem'.size ≤ qDegree + quot'.size := by
              rw [hrem'_size, hquot'_size]; exact hsize_match
            have hzero_quot' : ∀ i, i < shift →
                quot'.getD i (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              show (quot.set! shift coeff).getD i (Zero.zero : S) = (Zero.zero : S)
              rw [array_getD_set!_ne quot i shift coeff (by omega)]
              apply hzero_quot
              show i < B
              have h1 : shift < B := by show rd - qDegree < B; omega
              omega
            have hzero_rem' : ∀ i, qDegree + shift ≤ i →
                rem'.getD i (Zero.zero : S) = (Zero.zero : S) := by
              intro i hi
              have hi_ge_rd : rd ≤ i := by
                have hsum : qDegree + shift = rd := by show qDegree + (rd - qDegree) = rd; omega
                omega
              show (subtractScaledShift rem q shift coeff).getD i (Zero.zero : S) =
                (Zero.zero : S)
              rcases Nat.lt_or_eq_of_le hi_ge_rd with hgt | heq
              · rw [subtractScaledShift_getD_above_last rem q shift qDegree coeff i
                  hsize_q (by show shift + qDegree < i; omega)]
                exact arrayDegree?_some_above_eq_zero hdeg hgt
              · have hi_eq : i = shift + qDegree := by
                  show i = (rd - qDegree) + qDegree; omega
                rw [hi_eq]
                apply subtractScaledShift_getD_last_cancel rem q shift qDegree coeff
                  hsize_q
                · show shift + qDegree < rem.size
                  show (rd - qDegree) + qDegree < rem.size
                  have : (rd - qDegree) + qDegree = rd := by omega
                  rw [this]; exact hrd_lt
                · -- rem.getD (shift + qDegree) - coeff * q.getD qDegree 0 = 0
                  have hidx_eq : shift + qDegree = rd := by
                    show (rd - qDegree) + qDegree = rd; omega
                  rw [hidx_eq, hrem_at_rd, hcoeff_eq]
                  show (m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S)) -
                    (m.coeff (m.size - 1) * q.getD qDegree (Zero.zero : S)) =
                      (Zero.zero : S)
                  have hzero_eq : (Zero.zero : S) = (0 : S) := rfl
                  rw [hzero_eq]
                  exact Lean.Grind.AddCommGroup.sub_self _
            have hfuel' : shift ≤ fuel := by show rd - qDegree ≤ fuel; omega
            -- Apply IH.
            have hih := ih quot' rem' shift m_new
              hsize_match' hzero_quot' hzero_rem' hm_new_size hrem'_invariant hfuel'
            -- After unfolding divModArrayAux and the some/¬lt branch, the goal is about
            -- divModArrayAux q qDegree scaleLead fuel quot' rem'.
            refine ⟨?_, ?_⟩
            · simp [hrd_lt_q]
              simp only [← Array.set!_eq_setIfInBounds, ← Array.getD_eq_getD_getElem?]
              -- Goal: ofCoeffs (divModArrayAux _ _ _ fuel quot' rem').1 = ofCoeffs quot + m
              -- From hih.1: ofCoeffs (... rem').1 = ofCoeffs quot' + m_new
              show (ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot' rem').1
                  : DensePoly S) = ofCoeffs quot + m
              rw [hih.1]
              -- Now show ofCoeffs quot' + m_new = ofCoeffs quot + m.
              have hquot'_expand : (ofCoeffs quot' : DensePoly S) =
                  ofCoeffs quot + monomial shift coeff := by
                show (ofCoeffs (quot.set! shift coeff) : DensePoly S) =
                  ofCoeffs quot + monomial shift coeff
                exact ofCoeffs_set!_eq_add_monomial quot shift coeff hshift_lt_quot
                  hquot_shift_zero
              rw [hquot'_expand]
              show (ofCoeffs quot + monomial shift coeff) + (m - monomial shift coeff) =
                ofCoeffs quot + m
              apply ext_coeff
              intro n
              have hzero_add : (0 : S) + (0 : S) = 0 := by grind
              have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
              rw [coeff_add (ofCoeffs quot + monomial shift coeff)
                (m - monomial shift coeff) n hzero_add]
              rw [coeff_add (ofCoeffs quot) (monomial shift coeff) n hzero_add]
              rw [coeff_sub m (monomial shift coeff) n hzero_sub]
              rw [coeff_add (ofCoeffs quot) m n hzero_add]
              grind
            · simp [hrd_lt_q]
              simp only [← Array.set!_eq_setIfInBounds, ← Array.getD_eq_getD_getElem?]
              show (ofCoeffs (divModArrayAux q qDegree scaleLead fuel quot' rem').2
                  : DensePoly S) = (0 : DensePoly S)
              exact hih.2

/-- Size of a product is bounded above by the sum of sizes minus one. Generic to
any commutative ring; the bound is loose for non-domains where the leading-
coefficient product may cancel. -/
private theorem mul_size_le_top_succ_general {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p q : DensePoly S) (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).size ≤ p.size + q.size - 1 := by
  apply size_le_of_coeff_zero_above
  intro i hi
  exact coeff_mul_above_top_general p q hp hq (by omega)

/-- Public `divMod` identity for non-monic exact-multiple inputs: if `qq * q = p`,
the scaling function `(· / q.leadingCoeff)` exactly recovers any `a` from
`a * q.leadingCoeff`, and the leading-coefficient product never cancels, then
`divMod p q = (qq, 0)`. The exactness and no-zero-divisor hypotheses replace the
global cancellation invariant `∀ a, a - (a / q.leadingCoeff) * q.leadingCoeff = 0`
required by `divMod_reconstruction` (which only holds in the monic case over
`Int`). -/
theorem divMod_eq_of_polynomial_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (p q qq : DensePoly S)
    (hdegree : 0 < q.degree?.getD 0)
    (hexact : ∀ a : S, (a * q.leadingCoeff) / q.leadingCoeff = a)
    (h_top_ne : ∀ a : S, a ≠ (Zero.zero : S) →
        a * q.leadingCoeff ≠ (Zero.zero : S))
    (hmul : qq * q = p) :
    divMod p q = (qq, 0) := by
  -- Structural facts about q.
  have hq_pos : 0 < q.size := by
    unfold degree? at hdegree
    by_cases h : q.size = 0
    · simp [h] at hdegree
    · omega
  have hq_size_ge_two : 2 ≤ q.size := by
    unfold degree? at hdegree
    by_cases h : q.size = 0
    · simp [h] at hdegree
    · simp [h] at hdegree; omega
  have hq_lead_ne : q.leadingCoeff ≠ (Zero.zero : S) :=
    leadingCoeff_ne_zero_of_pos_size q hq_pos
  have hq_isZero : q.isZero = false := by
    have hq_size_ne_zero : q.coeffs.size ≠ 0 := by change q.size ≠ 0; omega
    simpa [isZero, Array.isEmpty_iff_size_eq_zero] using hq_size_ne_zero
  -- Helper: if qq ≠ 0, then p.size ≥ qq.size + q.size - 1.
  have hp_size_lower : qq ≠ 0 → qq.size + q.size - 1 ≤ p.size := by
    intro hqq_ne
    have hqq_pos : 0 < qq.size := by
      by_cases h : 0 < qq.size
      · exact h
      · exfalso; apply hqq_ne
        apply ext_coeff
        intro i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le qq (by omega)
    have hqq_lead_ne : qq.coeff (qq.size - 1) ≠ 0 :=
      coeff_last_ne_zero_of_pos_size qq hqq_pos
    have hprod_ne :
        qq.coeff (qq.size - 1) * q.leadingCoeff ≠ (Zero.zero : S) :=
      h_top_ne _ hqq_lead_ne
    have hp_top :
        p.coeff (qq.size - 1 + (q.size - 1)) =
          qq.coeff (qq.size - 1) * q.coeff (q.size - 1) := by
      rw [← hmul]
      exact coeff_mul_top_general qq q hqq_pos hq_pos
    have hp_top_ne :
        p.coeff (qq.size - 1 + (q.size - 1)) ≠ 0 := by
      rw [hp_top, ← leadingCoeff_eq_coeff_last q hq_pos]
      exact hprod_ne
    by_cases hle : qq.size + q.size - 1 ≤ p.size
    · exact hle
    · exfalso
      have hidx_ge : p.size ≤ qq.size - 1 + (q.size - 1) := by omega
      exact hp_top_ne (coeff_eq_zero_of_size_le p hidx_ge)
  -- Helper: qq.size ≤ p.size always.
  have hqq_size_le_p : qq.size ≤ p.size := by
    by_cases hqq_zero : qq = 0
    · have hp_zero : p = 0 := by rw [← hmul, hqq_zero, zero_mul]
      have hqq_size : qq.size = 0 := by rw [hqq_zero]; rfl
      have hp_size : p.size = 0 := by rw [hp_zero]; rfl
      omega
    · have h := hp_size_lower hqq_zero; omega
  unfold divMod
  by_cases hdeg_short : p.degree?.getD 0 < q.degree?.getD 0
  · -- Short circuit: must show qq = 0 and p = 0.
    rw [if_pos hdeg_short]
    have hp_size_lt_q : p.size < q.size := by
      unfold degree? at hdeg_short
      have hq_ne : q.size ≠ 0 := by omega
      by_cases hp_zero_size : p.size = 0
      · omega
      · simp [hp_zero_size, hq_ne] at hdeg_short
        omega
    have hqq_zero : qq = 0 := by
      by_cases h : qq = 0
      · exact h
      · exfalso
        have h_lower := hp_size_lower h
        have hqq_pos : 0 < qq.size := by
          by_cases hp : 0 < qq.size
          · exact hp
          · exfalso; apply h
            apply ext_coeff
            intro i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le qq (by omega)
        omega
    have hp_zero : p = 0 := by rw [← hmul, hqq_zero, zero_mul]
    rw [hp_zero, hqq_zero]
  · rw [if_neg hdeg_short]
    -- Apply the array-level lemma via divModArray.
    unfold divModArray
    rw [if_neg (by simp [hq_isZero])]
    -- Bookkeeping to feed divModArrayAux_eq_of_polynomial_mul.
    let qDeg := q.size - 1
    let scaleLead : S → S := fun coeff => coeff / q.leadingCoeff
    let quot0 : Array S := Array.replicate (p.size - qDeg) (Zero.zero : S)
    -- q.toArray characterization.
    have hq_toArray_size : q.toArray.size = q.size := by unfold toArray size; rfl
    have hq_lead_at_arr : q.toArray.getD qDeg (Zero.zero : S) = q.leadingCoeff := by
      show q.toArray.getD (q.size - 1) (Zero.zero : S) = q.leadingCoeff
      rw [leadingCoeff_eq_coeff_last q hq_pos]
      unfold coeff toArray; rfl
    have hsize_q : q.toArray.size = qDeg + 1 := by
      show q.toArray.size = q.size - 1 + 1
      rw [hq_toArray_size]; omega
    have hqArr_lc_ne : q.toArray.getD qDeg (Zero.zero : S) ≠ (Zero.zero : S) := by
      rw [hq_lead_at_arr]; exact hq_lead_ne
    have hexact' :
        ∀ a : S, scaleLead (a * q.toArray.getD qDeg (Zero.zero : S)) = a := by
      intro a
      show (a * q.toArray.getD qDeg (Zero.zero : S)) / q.leadingCoeff = a
      rw [hq_lead_at_arr]; exact hexact a
    have h_top_ne' :
        ∀ a : S, a ≠ (Zero.zero : S) →
          a * q.toArray.getD qDeg (Zero.zero : S) ≠ (Zero.zero : S) := by
      intro a ha
      rw [hq_lead_at_arr]; exact h_top_ne a ha
    -- p.degree ≥ q.degree in this branch, so p.size ≥ qDeg + 1.
    have hp_size_ge : qDeg + 1 ≤ p.size := by
      unfold degree? at hdeg_short
      have hq_ne : q.size ≠ 0 := by omega
      by_cases hp_zero_size : p.size = 0
      · simp [hp_zero_size, hq_ne] at hdeg_short
        omega
      · simp [hp_zero_size, hq_ne] at hdeg_short
        show q.size - 1 + 1 ≤ p.size
        omega
    have hp_toArray_size : p.toArray.size = p.size := by unfold toArray size; rfl
    -- Preconditions for the array lemma, with B = qq.size.
    have hsize_match : p.toArray.size ≤ qDeg + quot0.size := by
      show p.toArray.size ≤ qDeg + (Array.replicate (p.size - qDeg) (Zero.zero : S)).size
      rw [hp_toArray_size, Array.size_replicate]
      omega
    have hzero_quot : ∀ i, i < qq.size →
        quot0.getD i (Zero.zero : S) = (Zero.zero : S) := by
      intro i _
      show (Array.replicate (p.size - qDeg) (Zero.zero : S)).getD i (Zero.zero : S) =
        (Zero.zero : S)
      simp [Array.getD]
    have hzero_rem : ∀ i, qDeg + qq.size ≤ i →
        p.toArray.getD i (Zero.zero : S) = (Zero.zero : S) := by
      intro i hi
      have hp_le_i : p.size ≤ i := by
        by_cases hqq_zero : qq = 0
        · have hp_zero : p = 0 := by rw [← hmul, hqq_zero, zero_mul]
          have hp_size : p.size = 0 := by rw [hp_zero]; rfl
          omega
        · have hqq_pos : 0 < qq.size := by
            by_cases hp : 0 < qq.size
            · exact hp
            · exfalso; apply hqq_zero
              apply ext_coeff
              intro i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le qq (by omega)
          have hp_eq : p = qq * q := hmul.symm
          have hp_size_le : p.size ≤ qq.size + q.size - 1 := by
            rw [hp_eq]
            exact mul_size_le_top_succ_general qq q hqq_pos hq_pos
          show p.size ≤ i
          show p.size ≤ i
          omega
      unfold toArray Array.getD
      have hcoeffs_le : p.coeffs.size ≤ i := by change p.size ≤ i; exact hp_le_i
      rw [dif_neg (Nat.not_lt.mpr hcoeffs_le)]
    have hm_size_le : qq.size ≤ qq.size := Nat.le_refl _
    have h_inv : (ofCoeffs p.toArray : DensePoly S) = qq * ofCoeffs q.toArray := by
      rw [ofCoeffs_toArray p, ofCoeffs_toArray q]
      exact hmul.symm
    have hfuel : qq.size ≤ p.size := hqq_size_le_p
    have hresult := divModArrayAux_eq_of_polynomial_mul q.toArray qDeg hsize_q
      hqArr_lc_ne scaleLead hexact' h_top_ne' p.size quot0 p.toArray qq.size qq
      hsize_match hzero_quot hzero_rem hm_size_le h_inv hfuel
    -- Translate the array-level conclusion into pair equality.
    have hquot_zero : (ofCoeffs quot0 : DensePoly S) = 0 := by
      show (ofCoeffs (Array.replicate (p.size - qDeg) (Zero.zero : S)) : DensePoly S) = 0
      exact ofCoeffs_replicate_zero (p.size - qDeg)
    have hresult1 := hresult.1
    rw [hquot_zero, zero_add] at hresult1
    have hresult2 := hresult.2
    -- Goal: (ofCoeffs result.1, ofCoeffs result.2) = (qq, 0).
    show ((ofCoeffs (divModArrayAux q.toArray (q.size - 1) scaleLead p.size quot0
        p.toArray).1 : DensePoly S),
      (ofCoeffs (divModArrayAux q.toArray (q.size - 1) scaleLead p.size quot0
        p.toArray).2 : DensePoly S)) = (qq, 0)
    rw [hresult1, hresult2]

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

/-- The content of an integer polynomial divides every coefficient. -/
theorem content_dvd_coeff (p : DensePoly Int) (n : Nat) :
    content p ∣ p.coeff n := by
  simpa [content] using contentNat_dvd_coeff p n

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

private theorem int_natAbs_signed_mul (a : Int) :
    ∃ s : Int, s * a = Int.ofNat a.natAbs := by
  rcases Int.natAbs_eq a with ha | ha
  · exact ⟨1, by rw [ha]; grind⟩
  · exact ⟨-1, by rw [ha]; grind⟩

private theorem nat_gcd_bezout (a b : Nat) :
    ∃ x y : Int, x * (a : Int) + y * (b : Int) = (Nat.gcd a b : Int) := by
  induction a, b using Nat.gcd.induction with
  | H0 b =>
      exact ⟨0, 1, by simp [Nat.gcd_zero_left]⟩
  | H1 a b hpos ih =>
      rcases ih with ⟨x, y, hxy⟩
      refine ⟨y - x * (b / a : Nat), x, ?_⟩
      have hmod : ((b % a : Nat) : Int) = (b : Int) - (b / a : Nat) * (a : Int) := by
        have h := congrArg (fun n : Nat => (n : Int)) (Nat.mod_add_div b a)
        change ((b % a : Nat) : Int) + ((a * (b / a) : Nat) : Int) = (b : Int) at h
        rw [Int.natCast_mul] at h
        rw [Int.mul_comm ((a : Int)) ((b / a : Nat) : Int)] at h
        omega
      rw [Nat.gcd_rec]
      rw [← hxy]
      calc
        (y - x * (b / a : Nat)) * (a : Int) + x * (b : Int) =
            x * ((b : Int) - (b / a : Nat) * (a : Int)) + y * (a : Int) := by
              grind
        _ = x * (b % a : Nat) + y * (a : Int) := by
              rw [← hmod]

private theorem list_foldl_add_int (xs : List Int) (z : Int) :
    xs.foldl (fun s t => s + t) z = z + xs.foldl (fun s t => s + t) 0 := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (z + x), ih (0 + x)]
      grind

private theorem dvd_list_foldl_add_int_of_forall
    (d : Int) (xs : List Int) (h : ∀ x ∈ xs, d ∣ x) :
    d ∣ xs.foldl (fun s t => s + t) 0 := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [list_foldl_add_int xs (0 + x)]
      simpa using Int.dvd_add (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem dvd_list_foldl_add_term_of_forall
    (d : Int) (xs : List Nat) (term : Nat → Int)
    (h : ∀ x ∈ xs, d ∣ term x) :
    d ∣ xs.foldl (fun s x => s + term x) 0 := by
  have hmap : ∀ y ∈ xs.map term, d ∣ y := by
    intro y hy
    rw [List.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h x hx
  simpa [List.foldl_map] using dvd_list_foldl_add_int_of_forall d (xs.map term) hmap

private theorem list_foldl_add_term_int
    (xs : List Nat) (term : Nat → Int) (z : Int) :
    xs.foldl (fun s x => s + term x) z =
      z + xs.foldl (fun s x => s + term x) 0 := by
  simpa [List.foldl_map] using list_foldl_add_int (xs.map term) z

private theorem foldl_add_int_sub_terms
    (xs : List Nat) (f g : Nat → Int) :
    xs.foldl (fun s x => s + f x) 0 -
      xs.foldl (fun s x => s + g x) 0 =
    xs.foldl (fun s x => s + (f x - g x)) 0 := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [list_foldl_add_term_int xs f (0 + f x)]
      rw [list_foldl_add_term_int xs g (0 + g x)]
      rw [list_foldl_add_term_int xs (fun x => f x - g x) (0 + (f x - g x))]
      rw [← ih]
      grind

private theorem dvd_foldl_add_term_of_dvd_congr
    (d : Int) (xs : List Nat) (f g : Nat → Int)
    (hf : d ∣ xs.foldl (fun s x => s + f x) 0)
    (hcongr : ∀ x ∈ xs, d ∣ f x - g x) :
    d ∣ xs.foldl (fun s x => s + g x) 0 := by
  have hdiff : d ∣ xs.foldl (fun s x => s + (f x - g x)) 0 :=
    dvd_list_foldl_add_term_of_forall d xs (fun x => f x - g x) hcongr
  have hsub : d ∣
      xs.foldl (fun s x => s + f x) 0 -
        xs.foldl (fun s x => s + (f x - g x)) 0 :=
    Int.dvd_sub hf hdiff
  have hrewrite :
      xs.foldl (fun s x => s + f x) 0 -
        xs.foldl (fun s x => s + (f x - g x)) 0 =
      xs.foldl (fun s x => s + g x) 0 := by
    have hfg := foldl_add_int_sub_terms xs f g
    grind
  rwa [hrewrite] at hsub

private theorem dvd_term_of_dvd_foldl_add_of_dvd_others
    (d : Int) :
    ∀ (xs : List Nat) (term : Nat → Int) (idx : Nat),
      xs.Nodup →
      idx ∈ xs →
      d ∣ xs.foldl (fun s x => s + term x) 0 →
      (∀ r, r ∈ xs → r ≠ idx → d ∣ term r) →
      d ∣ term idx
  | [], _term, _idx, _hnodup, hmem, _hsum, _hothers => by
      cases hmem
  | x :: xs, term, idx, hnodup, hmem, hsum, hothers => by
      simp only [List.foldl_cons] at hsum
      have hfold :
          xs.foldl (fun s x => s + term x) (0 + term x) =
            term x + xs.foldl (fun s x => s + term x) 0 := by
        simpa [List.foldl_map] using list_foldl_add_int (xs.map term) (0 + term x)
      rw [hfold] at hsum
      have hnodup_tail : xs.Nodup := hnodup.tail
      have hx_not_mem : x ∉ xs := by
        rw [List.nodup_cons] at hnodup
        exact hnodup.1
      by_cases hxidx : x = idx
      · subst idx
        have htail : d ∣ xs.foldl (fun s x => s + term x) 0 := by
          apply dvd_list_foldl_add_term_of_forall
          intro y hy
          exact hothers y (List.mem_cons_of_mem x hy) (by
            intro hyx
            exact hx_not_mem (by simpa [hyx] using hy))
        have hdiff := Int.dvd_sub hsum htail
        simpa using hdiff
      · have hxdiv : d ∣ term x :=
          hothers x List.mem_cons_self hxidx
        have htail_sum : d ∣ xs.foldl (fun s x => s + term x) 0 := by
          have hdiff := Int.dvd_sub hsum hxdiv
          have heq :
              term x + xs.foldl (fun s x => s + term x) 0 - term x =
                xs.foldl (fun s x => s + term x) 0 := by
            grind
          rwa [heq] at hdiff
        have hidx_mem_tail : idx ∈ xs := by
          rcases List.mem_cons.mp hmem with hidx | htail
          · exact False.elim (hxidx hidx.symm)
          · exact htail
        exact dvd_term_of_dvd_foldl_add_of_dvd_others d xs term idx
          hnodup_tail hidx_mem_tail htail_sum
          (fun r hr hri => hothers r (List.mem_cons_of_mem x hr) hri)

private def finiteCoeffConvolution (pCoeff qCoeff : Nat → Int) (n : Nat) : Int :=
  (List.range (n + 1)).foldl (fun acc r => acc + pCoeff r * qCoeff (n - r)) 0

private def finiteCoeffFamilyPoly (coeff : Nat → Int) (bound : Nat) : DensePoly Int :=
  ofCoeffs ((List.range (bound + 1)).map coeff).toArray

private theorem finiteCoeffFamilyPoly_coeff_of_le
    (coeff : Nat → Int) (bound i : Nat) (hi : i ≤ bound) :
    (finiteCoeffFamilyPoly coeff bound).coeff i = coeff i := by
  unfold finiteCoeffFamilyPoly
  rw [coeff_ofCoeffs_list]
  simp [hi, Nat.lt_succ_iff]

private theorem finiteCoeffFamilyPoly_coeff_of_lt
    (coeff : Nat → Int) (bound i : Nat) (hi : bound < i) :
    (finiteCoeffFamilyPoly coeff bound).coeff i = 0 := by
  unfold finiteCoeffFamilyPoly
  rw [coeff_ofCoeffs_list]
  simp [hi, Nat.lt_succ_iff]
  rfl

private theorem dvd_finiteCoeffConvolution_term_of_dvd_others
    (pCoeff qCoeff : Nat → Int) (d n i : Nat)
    (hi : i < n + 1)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hothers : ∀ r, r < n + 1 → r ≠ i → (d : Int) ∣ pCoeff r * qCoeff (n - r)) :
    (d : Int) ∣ pCoeff i * qCoeff (n - i) := by
  exact dvd_term_of_dvd_foldl_add_of_dvd_others (d : Int) (List.range (n + 1))
    (fun r => pCoeff r * qCoeff (n - r)) i
    List.nodup_range (List.mem_range.mpr hi) hprod
    (fun r hr hri => hothers r (List.mem_range.mp hr) hri)

private theorem dvd_coeff_product_of_dvd_finiteCoeffConvolution_of_dvd_other_terms
    (pCoeff qCoeff : Nat → Int) (d i j : Nat)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff (i + j))
    (hothers :
      ∀ r s, r + s = i + j → r ≠ i → (d : Int) ∣ pCoeff r * qCoeff s) :
    (d : Int) ∣ pCoeff i * qCoeff j := by
  have hterm :
      (d : Int) ∣ pCoeff i * qCoeff (i + j - i) :=
    dvd_finiteCoeffConvolution_term_of_dvd_others
      pCoeff qCoeff d (i + j) i (by omega) hprod (by
        intro r hr hri
        exact hothers r (i + j - r) (by omega) hri)
  have hsub : i + j - i = j := by omega
  simpa [hsub] using hterm

private theorem dvd_coeff_product_last_of_dvd_finiteCoeffConvolution_of_dvd_larger_left_products
    (pCoeff qCoeff : Nat → Int) (d i k : Nat)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff (i + k))
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hlarger :
      ∀ r, i < r → (d : Int) ∣ pCoeff r * qCoeff (i + k - r)) :
    (d : Int) ∣ pCoeff i * qCoeff k := by
  exact dvd_coeff_product_of_dvd_finiteCoeffConvolution_of_dvd_other_terms
    pCoeff qCoeff d i k hprod (by
      intro r s hrs hri
      by_cases hri_lt : r < i
      · have hks : k < s := by omega
        exact Int.dvd_mul_of_dvd_right (hqAbove s hks)
      · have hir : i < r := by omega
        have hs : s = i + k - r := by omega
        simpa [hs] using hlarger r hir)

private theorem dvd_finiteCoeffConvolution_last_of_boundaries_and_larger_left
    (pCoeff qCoeff : Nat → Int) (d bound i k : Nat)
    (hprod : (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff (i + k))
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s)
    (hlarger :
      ∀ r, i < r → r ≤ bound → (d : Int) ∣ pCoeff r * qCoeff (i + k - r)) :
    (d : Int) ∣ pCoeff i * qCoeff k := by
  exact dvd_coeff_product_of_dvd_finiteCoeffConvolution_of_dvd_other_terms
    pCoeff qCoeff d i k hprod (by
      intro r s hrs hri
      by_cases hri_lt : r < i
      · have hks : k < s := by omega
        exact Int.dvd_mul_of_dvd_right (hqAbove s hks)
      · have hir : i < r := by omega
        by_cases hr : r ≤ bound
        · have hs : s = i + k - r := by omega
          simpa [hs] using hlarger r hir hr
        · exact hleft r s (Nat.lt_of_not_ge hr))

private theorem finiteToeplitzMcCoyRow_of_larger_left_products
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod : ∀ n, n ≤ bound + k → (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s)
    (hlarger :
      ∀ i, i ≤ bound →
        ∀ r, i < r → r ≤ bound → (d : Int) ∣ pCoeff r * qCoeff (i + k - r)) :
    ∀ i, i ≤ bound → (d : Int) ∣ pCoeff i * qCoeff k := by
  intro i hi
  exact dvd_finiteCoeffConvolution_last_of_boundaries_and_larger_left
    pCoeff qCoeff d bound i k (hprod (i + k) (by omega)) hqAbove hleft
    (hlarger i hi)

private theorem dvd_diagonalMulCoeffTerm_of_dvd_mul_coeff_of_dvd_other_diagonal_terms
    (p q : DensePoly Int) (d n i : Nat)
    (hprod : (d : Int) ∣ (p * q).coeff n)
    (hothers : ∀ r, r ≠ i → (d : Int) ∣ diagonalMulCoeffTerm p q n r) :
    (d : Int) ∣ diagonalMulCoeffTerm p q n i := by
  by_cases hi : i < n + 1
  · have hsum :
        (d : Int) ∣ (List.range (n + 1)).foldl
          (fun s r => s + diagonalMulCoeffTerm p q n r) 0 := by
      rw [← diagonalSum_eq_degree_bound p q n]
      rw [← mulCoeffSum_eq_diagonal p q n]
      rw [← coeff_mul p q n]
      exact hprod
    exact dvd_term_of_dvd_foldl_add_of_dvd_others (d : Int) (List.range (n + 1))
      (fun r => diagonalMulCoeffTerm p q n r) i
      List.nodup_range (List.mem_range.mpr hi) hsum
      (fun r _hr hri => hothers r hri)
  · have hni : n < i := by omega
    rw [diagonalMulCoeffTerm_eq_zero_of_degree_lt p q n i hni]
    simp

private theorem dvd_coeff_mul_of_dvd_mul_coeff_of_dvd_other_diagonal_products
    (p q : DensePoly Int) (d i j : Nat)
    (hprod : (d : Int) ∣ (p * q).coeff (i + j))
    (hothers :
      ∀ r s, r + s = i + j → r ≠ i → (d : Int) ∣ p.coeff r * q.coeff s) :
    (d : Int) ∣ p.coeff i * q.coeff j := by
  have hterm :
      (d : Int) ∣ diagonalMulCoeffTerm p q (i + j) i :=
    dvd_diagonalMulCoeffTerm_of_dvd_mul_coeff_of_dvd_other_diagonal_terms
      p q d (i + j) i hprod (by
        intro r hri
        unfold diagonalMulCoeffTerm
        by_cases hr : i + j < r
        · simp [hr]
        · simp [hr]
          exact hothers r (i + j - r) (by omega) hri)
  unfold diagonalMulCoeffTerm at hterm
  have hnot : ¬ i + j < i := by omega
  simpa [hnot] using hterm

private theorem dvd_coeff_mul_last_of_dvd_mul_coeff_of_dvd_larger_left_products
    (p q : DensePoly Int) (d i k : Nat)
    (hprod : (d : Int) ∣ (p * q).coeff (i + k))
    (hqAbove : ∀ s, k < s → (d : Int) ∣ q.coeff s)
    (hlarger :
      ∀ r, i < r → (d : Int) ∣ p.coeff r * q.coeff (i + k - r)) :
    (d : Int) ∣ p.coeff i * q.coeff k := by
  exact dvd_coeff_mul_of_dvd_mul_coeff_of_dvd_other_diagonal_products
    p q d i k hprod (by
      intro r s hrs hri
      by_cases hri_lt : r < i
      · have hks : k < s := by omega
        exact Int.dvd_mul_of_dvd_right (hqAbove s hks)
      · have hir : i < r := by omega
        have hs : s = i + k - r := by omega
        simpa [hs] using hlarger r hir)

private theorem mcCoy_grid_band_descent
    (D : Nat → Nat → Prop) (bound k : Nat)
    (hRight : ∀ r s, bound < r → D r s)
    (hstep : ∀ i j, i ≤ bound → j ≤ k →
      (∀ r, i < r → D r (i + j - r)) → D i j) :
    ∀ i j, j ≤ k → D i j := by
  intro i
  by_cases hi : i ≤ bound
  · let m := bound - i
    have hm : bound - i = m := rfl
    clear_value m
    revert i
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro i hi hm j hj
        exact hstep i j hi hj (by
          intro r hir
          by_cases hr : r ≤ bound
          · have hltm : bound - r < m := by omega
            exact ih (bound - r) hltm r hr rfl (i + j - r) (by omega)
          · exact hRight r (i + j - r) (Nat.lt_of_not_ge hr))
  · intro j _hj
    exact hRight i j (Nat.lt_of_not_ge hi)

private theorem mcCoy_top_row_descent
    (D : Nat → Nat → Prop) (bound k : Nat)
    (hRight : ∀ r s, bound < r → D r s)
    (hstep : ∀ i j, i ≤ bound → j ≤ k →
      (∀ r, i < r → D r (i + j - r)) → D i j) :
    ∀ i, D i k := by
  intro i
  exact mcCoy_grid_band_descent D bound k hRight hstep i k (Nat.le_refl k)

private theorem list_natAbs_gcd_bezout_aux (xs : List Int) (acc : Nat) :
    ∃ a : Int, ∃ weights : List Int,
      weights.length = xs.length ∧
      a * (acc : Int) +
          (List.zipWith (fun w c : Int => w * c) weights xs).foldl (fun s t => s + t) 0 =
        ((xs.foldl (fun (g : Nat) (x : Int) => Nat.gcd g x.natAbs) acc : Nat) : Int) := by
  induction xs generalizing acc with
  | nil =>
      exact ⟨1, [], by simp⟩
  | cons x xs ih =>
      rcases nat_gcd_bezout acc x.natAbs with ⟨u, v, huv⟩
      rcases int_natAbs_signed_mul x with ⟨sgn, hsgn⟩
      rcases ih (Nat.gcd acc x.natAbs) with ⟨a, weights, hlen, hsum⟩
      refine ⟨a * u, (a * v * sgn) :: weights, ?_, ?_⟩
      · simp [hlen]
      · simp only [List.zipWith_cons_cons, List.foldl_cons, List.foldl_cons]
        rw [← hsum]
        rw [← huv]
        rw [list_foldl_add_int]
        have hterm : a * v * sgn * x = a * v * Int.ofNat x.natAbs := by
          rw [← hsgn]
          grind
        rw [hterm]
        grind

private theorem list_natAbs_gcd_bezout (xs : List Int) :
    ∃ weights : List Int,
      weights.length = xs.length ∧
      (List.zipWith (fun w c : Int => w * c) weights xs).foldl (fun s t => s + t) 0 =
        ((xs.foldl (fun (g : Nat) (x : Int) => Nat.gcd g x.natAbs) 0 : Nat) : Int) := by
  rcases list_natAbs_gcd_bezout_aux xs 0 with ⟨_a, weights, hlen, hsum⟩
  refine ⟨weights, hlen, ?_⟩
  simpa using hsum

private theorem exists_linear_combination_coeffs_eq_one_of_content_eq_one
    (p : DensePoly Int) (hp : content p = 1) :
    ∃ weights : List Int,
      weights.length = p.toArray.toList.length ∧
      (List.zipWith (fun w c : Int => w * c) weights p.toArray.toList).foldl
          (fun s t => s + t) 0 = 1 := by
  rcases list_natAbs_gcd_bezout p.toArray.toList with ⟨weights, hlen, hsum⟩
  refine ⟨weights, hlen, ?_⟩
  unfold content contentNat at hp
  rw [hsum]
  exact hp

theorem dvd_content_of_nat_dvd_coeff (p : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ p.coeff n) :
    (d : Int) ∣ content p := by
  rw [content]
  rw [Int.ofNat_dvd_left]
  exact dvd_contentNat_of_dvd_coeff p d h

/-- If a natural number divides every coefficient, then it divides the content. -/
theorem natCast_dvd_content_of_dvd_coeff (p : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ p.coeff n) :
    (d : Int) ∣ content p := by
  exact dvd_content_of_nat_dvd_coeff p d h

theorem nat_eq_one_of_content_eq_one_of_nat_dvd_coeff (p : DensePoly Int) (d : Nat)
    (hp : content p = 1) (h : ∀ n, (d : Int) ∣ p.coeff n) :
    d = 1 := by
  have hdvd : (d : Int) ∣ (1 : Int) := by
    simpa [hp] using dvd_content_of_nat_dvd_coeff p d h
  rw [Int.ofNat_dvd_left] at hdvd
  exact Nat.dvd_one.mp hdvd

private theorem foldl_zipWith_mul_scale_int
    (a : Int) (weights values : List Int) :
    a * (List.zipWith (fun w c : Int => w * c) weights values).foldl
          (fun s t => s + t) 0 =
      (List.zipWith (fun w c : Int => w * (a * c)) weights values).foldl
          (fun s t => s + t) 0 := by
  induction weights generalizing values with
  | nil => simp
  | cons w ws ih =>
      cases values with
      | nil => simp
      | cons c cs =>
          simp only [List.zipWith_cons_cons, List.foldl_cons]
          rw [list_foldl_add_int (List.zipWith (fun w c : Int => w * c) ws cs)
                (0 + w * c)]
          rw [list_foldl_add_int (List.zipWith (fun w c : Int => w * (a * c)) ws cs)
                (0 + w * (a * c))]
          rw [← ih cs]
          grind

private theorem dvd_foldl_zipWith_scale_mul
    (d : Int) (a : Int) (weights values : List Int)
    (h : ∀ c ∈ values, d ∣ a * c) :
    d ∣ (List.zipWith (fun w c : Int => w * (a * c)) weights values).foldl
          (fun s t => s + t) 0 := by
  induction weights generalizing values with
  | nil => simp
  | cons w ws ih =>
      cases values with
      | nil => simp
      | cons c cs =>
          simp only [List.zipWith_cons_cons, List.foldl_cons]
          rw [list_foldl_add_int]
          have hac : d ∣ a * c := h c List.mem_cons_self
          have hrest : ∀ c' ∈ cs, d ∣ a * c' :=
            fun c' hc' => h c' (List.mem_cons.mpr (Or.inr hc'))
          have hwac : d ∣ w * (a * c) := Int.dvd_mul_of_dvd_right hac
          have h0wac : d ∣ (0 + w * (a * c) : Int) := by simpa using hwac
          exact Int.dvd_add h0wac (ih cs hrest)

/-- Scalar annihilator for primitive integer polynomials: if `d` divides every
coefficient of `a * p` and `p` is primitive (content one), then `d` already
divides `a`. -/
theorem nat_dvd_of_scalar_mul_primitive_coeff_dvd
    (p : DensePoly Int) (d : Nat) (a : Int)
    (hp : content p = 1)
    (h : ∀ n, (d : Int) ∣ a * p.coeff n) :
    (d : Int) ∣ a := by
  rcases exists_linear_combination_coeffs_eq_one_of_content_eq_one p hp with
    ⟨weights, _hlen, hsum⟩
  have hval_dvd : ∀ c ∈ p.toArray.toList, (d : Int) ∣ a * c := by
    intro c hc
    rw [List.mem_iff_getElem] at hc
    rcases hc with ⟨i, hi, hget⟩
    have hcoeff_eq : p.coeff i = c := by
      have hgetArray : p.coeffs[i] = c := by
        simpa [toArray, Array.getElem_toList] using hget
      change p.coeffs.getD i (0 : Int) = c
      rw [← Array.getElem_eq_getD (0 : Int)]
      exact hgetArray
    rw [← hcoeff_eq]
    exact h i
  have hexp :
      a = (List.zipWith (fun w c : Int => w * (a * c)) weights p.toArray.toList).foldl
            (fun s t => s + t) 0 := by
    have key := foldl_zipWith_mul_scale_int a weights p.toArray.toList
    rw [hsum, Int.mul_one] at key
    exact key
  rw [hexp]
  exact dvd_foldl_zipWith_scale_mul (d : Int) a weights p.toArray.toList hval_dvd

private theorem exists_max_prop_below
    (P : Nat → Prop) [DecidablePred P] :
    ∀ N, (∃ n, n < N ∧ P n) →
      ∃ k, k < N ∧ P k ∧ ∀ j, k < j → j < N → ¬ P j
  | 0, h => by
      rcases h with ⟨n, hn, _⟩
      omega
  | N + 1, h => by
      by_cases hN : P N
      · exact ⟨N, by omega, hN, by
          intro j hj hjN
          omega⟩
      · have hbelow : ∃ n, n < N ∧ P n := by
          rcases h with ⟨n, hn, hp⟩
          by_cases hnN : n = N
          · subst n
            exact False.elim (hN hp)
          · exact ⟨n, by omega, hp⟩
        rcases exists_max_prop_below P N hbelow with ⟨k, hkN, hkP, hmax⟩
        exact ⟨k, by omega, hkP, by
          intro j hkj hjNsucc
          by_cases hj : j = N
          · subst j
            exact hN
          · exact hmax j hkj (by omega)⟩

private theorem exists_last_not_natCast_dvd_coeff
    (q : DensePoly Int) (d : Nat)
    (hq : ∃ n, ¬ (d : Int) ∣ q.coeff n) :
    ∃ k, (¬ (d : Int) ∣ q.coeff k) ∧
      ∀ j, k < j → (d : Int) ∣ q.coeff j := by
  have hbelow : ∃ n, n < q.size ∧ ¬ (d : Int) ∣ q.coeff n := by
    rcases hq with ⟨n, hn⟩
    by_cases hsize : n < q.size
    · exact ⟨n, hsize, hn⟩
    · have hcoeff : q.coeff n = 0 := coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hsize)
      have hdvd : (d : Int) ∣ q.coeff n := by
        rw [hcoeff]
        exact ⟨0, by simp⟩
      exact False.elim (hn hdvd)
  rcases exists_max_prop_below (fun n => ¬ (d : Int) ∣ q.coeff n) q.size hbelow with
    ⟨k, _hkSize, hk, hmax⟩
  exact ⟨k, hk, by
    intro j hkj
    by_cases hjSize : j < q.size
    · exact Classical.byContradiction (fun hnot => hmax j hkj hjSize hnot)
    · have hcoeff : q.coeff j = 0 := coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hjSize)
      rw [hcoeff]
      exact ⟨0, by simp⟩⟩

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

private theorem foldl_gcd_natAbs_mul_const_int (c : Int) (xs : List Int) (acc : Nat) :
    xs.foldl (fun g x => Nat.gcd g (c * x).natAbs) (c.natAbs * acc) =
      c.natAbs * xs.foldl (fun g x => Nat.gcd g x.natAbs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih =>
      simp only [List.foldl_cons]
      rw [Int.natAbs_mul, Nat.gcd_mul_left]
      exact ih (Nat.gcd acc x.natAbs)

private theorem foldl_gcd_natAbs_of_all_zero (xs : List Int) (acc : Nat)
    (hzero : ∀ y ∈ xs, y = (0 : Int)) :
    xs.foldl (fun g x => Nat.gcd g x.natAbs) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih =>
      have hx : x = 0 := hzero x List.mem_cons_self
      have hxs' : ∀ y ∈ xs', y = (0 : Int) :=
        fun y hy => hzero y (List.mem_cons_of_mem x hy)
      simp only [List.foldl_cons, hx, Int.natAbs_zero, Nat.gcd_zero_right]
      exact ih acc hxs'

private theorem trimTrailingZerosList_cons_int (x : Int) (xs : List Int) :
    trimTrailingZerosList (x :: xs) =
      if trimTrailingZerosList xs = [] ∧ x = (0 : Int) then ([] : List Int)
      else x :: trimTrailingZerosList xs := rfl

private theorem all_zero_of_trimTrailingZerosList_nil (xs : List Int)
    (htrim : trimTrailingZerosList xs = []) :
    ∀ y ∈ xs, y = (0 : Int) := by
  induction xs with
  | nil => intro y hy; cases hy
  | cons x xs' ih =>
      rw [trimTrailingZerosList_cons_int] at htrim
      by_cases hinner : trimTrailingZerosList xs' = [] ∧ x = (0 : Int)
      · rw [if_pos hinner] at htrim
        intro y hy
        rcases List.mem_cons.mp hy with hyx | hyxs
        · rw [hyx]; exact hinner.2
        · exact ih hinner.1 y hyxs
      · rw [if_neg hinner] at htrim
        exact absurd htrim (List.cons_ne_nil _ _)

private theorem foldl_gcd_natAbs_trim_eq (xs : List Int) (acc : Nat) :
    (trimTrailingZerosList xs).foldl (fun g x => Nat.gcd g x.natAbs) acc =
      xs.foldl (fun g x => Nat.gcd g x.natAbs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs' ih =>
      rw [trimTrailingZerosList_cons_int]
      by_cases hinner : trimTrailingZerosList xs' = [] ∧ x = (0 : Int)
      · rw [if_pos hinner]
        rw [List.foldl_nil, List.foldl_cons, hinner.2]
        simp only [Int.natAbs_zero, Nat.gcd_zero_right]
        have hzero : ∀ y ∈ xs', y = (0 : Int) :=
          all_zero_of_trimTrailingZerosList_nil xs' hinner.1
        exact (foldl_gcd_natAbs_of_all_zero xs' acc hzero).symm
      · rw [if_neg hinner]
        rw [List.foldl_cons, List.foldl_cons]
        exact ih (Nat.gcd acc x.natAbs)

/-- Content scales by the absolute value of the scaling integer. -/
theorem content_scale_int (c : Int) (p : DensePoly Int) :
    content (scale c p) = Int.ofNat c.natAbs * content p := by
  show Int.ofNat (contentNat (scale c p)) =
      Int.ofNat c.natAbs * Int.ofNat (contentNat p)
  show Int.ofNat (contentNat (scale c p)) =
      Int.ofNat (c.natAbs * contentNat p)
  apply congrArg Int.ofNat
  -- Goal: contentNat (scale c p) = c.natAbs * contentNat p.
  unfold contentNat
  have hscale_coeffs :
      (scale c p).toArray.toList =
        trimTrailingZerosList (p.toArray.toList.map (fun x => c * x)) := by
    unfold scale ofCoeffs toArray trimTrailingZeros
    simp
  rw [hscale_coeffs]
  rw [foldl_gcd_natAbs_trim_eq]
  rw [List.foldl_map]
  have h := foldl_gcd_natAbs_mul_const_int c p.toArray.toList 0
  rw [Nat.mul_zero] at h
  exact h

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

/-- A polynomial whose content is `1` equals its primitive part. -/
theorem primitivePart_eq_self_of_content_eq_one
    (p : DensePoly Int) (h : content p = 1) :
    primitivePart p = p := by
  have hscale : scale (content p) (primitivePart p) = p :=
    content_mul_primitivePart p
  apply ext_coeff
  intro n
  have hcoeff :
      (scale (content p) (primitivePart p)).coeff n = p.coeff n := by
    rw [hscale]
  rw [coeff_scale (content p) (primitivePart p) n (Int.mul_zero _)] at hcoeff
  rw [h] at hcoeff
  simpa using hcoeff

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

/-- Construct a polynomial with prescribed residues modulo coprime factors.

If `s * a + t * b = 1`, then `polyCRT a b u v s t` is congruent to `u`
modulo `a` and to `v` modulo `b`; see `polyCRT_congr_fst`,
`polyCRT_congr_snd`, `polyCRT_mod_fst`, and `polyCRT_mod_snd`. -/
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

/-- Reverse direction of `mod_eq_mod_of_congr`: equal canonical remainders force the
operands to be congruent modulo the divisor. -/
theorem dvd_of_mod_eq_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    {p q m : DensePoly S} (h : p % m = q % m) :
    m ∣ (p - q) := by
  refine ⟨(p / m) - (q / m), ?_⟩
  apply ext_coeff
  intro n
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hp := congrArg (fun x : DensePoly S => x.coeff n) (div_mul_add_mod p m)
  have hq := congrArg (fun x : DensePoly S => x.coeff n) (div_mul_add_mod q m)
  have hh := congrArg (fun x : DensePoly S => x.coeff n) h
  change ((p / m) * m + (p % m)).coeff n = p.coeff n at hp
  change ((q / m) * m + (q % m)).coeff n = q.coeff n at hq
  change (p % m).coeff n = (q % m).coeff n at hh
  rw [coeff_add ((p / m) * m) (p % m) n hzero_add] at hp
  rw [coeff_add ((q / m) * m) (q % m) n hzero_add] at hq
  rw [coeff_sub p q n hzero_sub]
  -- Reduce m * ((p/m) - (q/m)) via mul_sub_zero_comm-style manipulation.
  have hgoal :
      (m * ((p / m) - (q / m))).coeff n =
        ((p / m) * m).coeff n - ((q / m) * m).coeff n := by
    rw [show m * ((p / m) - (q / m)) = (p / m) * m + (0 - (q / m) * m) from ?_]
    · rw [coeff_add ((p / m) * m) (0 - (q / m) * m) n hzero_add]
      rw [coeff_sub 0 ((q / m) * m) n hzero_sub, coeff_zero]
      grind
    · -- m * (a - b) = a * m + (0 - b * m), via sub_eq_add_neg + mul_sub_zero_comm + mul_comm.
      rw [sub_eq_add_neg_poly]
      rw [mul_add_right_poly]
      rw [mul_sub_zero_comm m (q / m)]
      rw [mul_comm_poly m (p / m)]
  rw [hgoal]
  grind

/-- Equal canonical remainders produce polynomial congruence modulo the divisor. -/
theorem congr_of_mod_eq_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S]
    [Div S] [DivModLaws S]
    {p q m : DensePoly S} (h : p % m = q % m) :
    Congr p q m := by
  exact dvd_of_mod_eq_mod h

/-- Polynomial congruence modulo `m` is equivalent to equality of canonical remainders. -/
theorem mod_eq_mod_iff_congr {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S]
    [Div S] [DivModLaws S]
    {p q m : DensePoly S} :
    p % m = q % m ↔ Congr p q m := by
  constructor
  · exact congr_of_mod_eq_mod
  · exact mod_eq_mod_of_congr

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

/-- The CRT witness is congruent to the prescribed first residue modulo `a`. -/
theorem polyCRT_congr_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> s * a + t * b = 1 ->
    Congr (polyCRT a b u v s t) u a := by
  intro S _ _ a b u v s t hbez
  unfold Congr polyCRT
  refine ⟨v * s + (0 - u * s), ?_⟩
  exact polyCRT_sub_left_factor a b u v s t hbez

/-- The CRT witness is congruent to the prescribed second residue modulo `b`. -/
theorem polyCRT_congr_snd :
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

/-! ## Gauss's lemma on content multiplicativity for `DensePoly Int`. -/

/-- Local primality predicate for `Nat`. `HexPoly` is foundational and does not
import the `Hex.Nat.Prime` API; we keep a private copy of just enough machinery
to formulate Gauss's lemma on integer polynomial content. -/
private def NatPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

private theorem natPrime_coprime_of_not_dvd {p a : Nat} (hp : NatPrime p)
    (ha : ¬ p ∣ a) : Nat.Coprime p a := by
  rw [Nat.Coprime]
  have hgcd_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  rcases hp.2 (Nat.gcd p a) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exact absurd (hgcd ▸ Nat.gcd_dvd_right p a) ha

/-- Euclid's lemma for `Nat`. -/
private theorem natPrime_dvd_mul {p a b : Nat} (hp : NatPrime p)
    (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hb : p ∣ b
  · exact Or.inr hb
  · exact Or.inl ((natPrime_coprime_of_not_dvd hp hb).dvd_of_dvd_mul_right h)

/-- Euclid's lemma carried through `Int.natAbs`. -/
private theorem natPrime_dvd_mul_int {p : Nat} {a b : Int} (hp : NatPrime p)
    (h : (p : Int) ∣ a * b) : (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases natPrime_dvd_mul hp h with hN | hN
  · left; rw [Int.ofNat_dvd_left]; exact hN
  · right; rw [Int.ofNat_dvd_left]; exact hN

/-- Every natural number greater than `1` has a prime divisor. -/
private theorem exists_natPrime_dvd_of_one_lt :
    ∀ (n : Nat), 1 < n → ∃ r, NatPrime r ∧ r ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hn
      by_cases hprime : NatPrime n
      · exact ⟨n, hprime, Nat.dvd_refl n⟩
      · -- `n` is composite: extract a proper divisor manually (no `push_neg`).
        have h2 : 2 ≤ n := hn
        have hcomp : ∃ m : Nat, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
          apply Classical.byContradiction
          intro hno
          apply hprime
          refine ⟨h2, ?_⟩
          intro m hm
          apply Classical.byContradiction
          intro hcases
          apply hno
          refine ⟨m, hm, ?_, ?_⟩
          · intro hm1; exact hcases (Or.inl hm1)
          · intro hmn; exact hcases (Or.inr hmn)
        rcases hcomp with ⟨m, hmd, hm1, hmn⟩
        have hm0 : m ≠ 0 := by
          intro hm0
          subst hm0
          have hn_zero : n = 0 := Nat.eq_zero_of_zero_dvd hmd
          omega
        have hmlt : m < n := by
          have hpos : 0 < n := by omega
          have hle : m ≤ n := Nat.le_of_dvd hpos hmd
          omega
        have hm_one_lt : 1 < m := by
          cases m with
          | zero => exact absurd rfl hm0
          | succ m' =>
              cases m' with
              | zero => exact absurd rfl hm1
              | succ _ => omega
        rcases ih m hmlt hm_one_lt with ⟨r, hrp, hrm⟩
        exact ⟨r, hrp, Nat.dvd_trans hrm hmd⟩

/-- Polynomial Euclid's lemma. If a prime divides every coefficient of `p * q`,
then it divides every coefficient of `p` or every coefficient of `q`. -/
private theorem natPrime_dvd_all_or_all_of_dvd_mul_coeff
    {r : Nat} (hr : NatPrime r) (p q : DensePoly Int)
    (h : ∀ n, (r : Int) ∣ (p * q).coeff n) :
    (∀ i, (r : Int) ∣ p.coeff i) ∨ (∀ j, (r : Int) ∣ q.coeff j) := by
  apply Classical.byContradiction
  intro hno
  have hp_some : ∃ i, ¬ (r : Int) ∣ p.coeff i := by
    apply Classical.byContradiction
    intro hpno
    apply hno
    left
    intro i
    apply Classical.byContradiction
    intro hi
    exact hpno ⟨i, hi⟩
  have hq_some : ∃ j, ¬ (r : Int) ∣ q.coeff j := by
    apply Classical.byContradiction
    intro hqno
    apply hno
    right
    intro j
    apply Classical.byContradiction
    intro hj
    exact hqno ⟨j, hj⟩
  rcases exists_last_not_natCast_dvd_coeff p r hp_some with ⟨i0, hni0, hi_above⟩
  rcases exists_last_not_natCast_dvd_coeff q r hq_some with ⟨j0, hnj0, hj_above⟩
  have hsplit : (r : Int) ∣ p.coeff i0 * q.coeff j0 :=
    dvd_coeff_mul_last_of_dvd_mul_coeff_of_dvd_larger_left_products
      p q r i0 j0 (h (i0 + j0)) hj_above
      (fun a ha => Int.dvd_mul_of_dvd_left (hi_above a ha))
  rcases natPrime_dvd_mul_int hr hsplit with hpi | hqj
  · exact hni0 hpi
  · exact hnj0 hqj

/-- Content-level form of polynomial Euclid: if a prime divides every coefficient
of `p * q`, it divides the content of `p` or the content of `q`. -/
private theorem natPrime_dvd_contentNat_or_dvd_contentNat_of_dvd_mul
    {r : Nat} (hr : NatPrime r) (p q : DensePoly Int)
    (h : ∀ n, (r : Int) ∣ (p * q).coeff n) :
    r ∣ contentNat p ∨ r ∣ contentNat q := by
  rcases natPrime_dvd_all_or_all_of_dvd_mul_coeff hr p q h with hp | hq
  · exact Or.inl (dvd_contentNat_of_dvd_coeff p r hp)
  · exact Or.inr (dvd_contentNat_of_dvd_coeff q r hq)

/-- Helper: a foldl over `List.range (k+1)` whose terms vanish below `k`
collapses to the final term. -/
private theorem foldl_add_int_eq_last_of_below_zero
    (g : Nat → Int) (k : Nat)
    (h : ∀ i, i < k → g i = 0) :
    (List.range (k + 1)).foldl (fun acc i => acc + g i) 0 = g k := by
  have hzero : ∀ m, m ≤ k →
      (List.range m).foldl (fun acc i => acc + g i) 0 = 0 := by
    intro m hm
    induction m with
    | zero => simp
    | succ m' ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (Nat.le_of_succ_le hm)]
        have hg : g m' = 0 := h m' (Nat.lt_of_succ_le hm)
        rw [hg]
        grind
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hzero k (Nat.le_refl k)]
  grind

/-- Helper variant of `foldl_add_int_eq_last_of_below_zero` indexed by the
foldl bound rather than the (bound - 1). -/
private theorem foldl_add_int_eq_at_predecessor
    (g : Nat → Int) (psize : Nat) (hpsize : 0 < psize)
    (h : ∀ i, i < psize - 1 → g i = 0) :
    (List.range psize).foldl (fun acc i => acc + g i) 0 = g (psize - 1) := by
  have hpsize_eq : psize - 1 + 1 = psize := by omega
  rw [← hpsize_eq]
  exact foldl_add_int_eq_last_of_below_zero g (psize - 1) h

/-- The top coefficient of a product of nonzero integer polynomials is the product of
their leading coefficients. -/
theorem coeff_mul_top_int (p q : DensePoly Int)
    (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).coeff (p.size - 1 + (q.size - 1)) =
      p.coeff (p.size - 1) * q.coeff (q.size - 1) := by
  rw [coeff_mul, mulCoeffSum_eq_diagonal]
  rw [foldl_add_int_eq_at_predecessor _ p.size hp]
  · unfold diagonalMulCoeffTerm
    have hno : ¬ (p.size - 1 + (q.size - 1)) < p.size - 1 := by omega
    rw [if_neg hno]
    have hsub : p.size - 1 + (q.size - 1) - (p.size - 1) = q.size - 1 := by omega
    rw [hsub]
  · intro i hi
    unfold diagonalMulCoeffTerm
    have hno : ¬ (p.size - 1 + (q.size - 1)) < i := by omega
    rw [if_neg hno]
    have hsub : (p.size - 1 + (q.size - 1)) - i ≥ q.size := by omega
    rw [coeff_eq_zero_of_size_le q hsub]
    show p.coeff i * (0 : Int) = 0
    rw [Int.mul_zero]

/-- Integral domain property for integer polynomials. -/
theorem mul_ne_zero_int (p q : DensePoly Int)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 := by
  have hp_size : 0 < p.size := by
    rcases Nat.lt_or_ge 0 p.size with h | h
    · exact h
    · exfalso
      apply hp
      have hsize : p.size = 0 := by omega
      apply ext_coeff
      intro n
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le p (by omega)
  have hq_size : 0 < q.size := by
    rcases Nat.lt_or_ge 0 q.size with h | h
    · exact h
    · exfalso
      apply hq
      have hsize : q.size = 0 := by omega
      apply ext_coeff
      intro n
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le q (by omega)
  intro hpq0
  have htop := coeff_mul_top_int p q hp_size hq_size
  have hpq_top_zero : (p * q).coeff (p.size - 1 + (q.size - 1)) = 0 := by
    rw [hpq0]; exact coeff_zero _
  rw [hpq_top_zero] at htop
  -- 0 = lead(p) * lead(q), but both leading coefficients are nonzero
  have hlp_ne := coeff_last_ne_zero_of_pos_size p hp_size
  have hlq_ne := coeff_last_ne_zero_of_pos_size q hq_size
  rcases Int.mul_eq_zero.mp htop.symm with h | h
  · exact hlp_ne h
  · exact hlq_ne h

/-- Integral domain property: for primitive integer polynomials, the product
is nonzero. -/
private theorem mul_ne_zero_of_primitive (p q : DensePoly Int)
    (hp : content p = 1) (hq : content q = 1) :
    p * q ≠ 0 := by
  have hcp_ne_zero : content p ≠ 0 := by rw [hp]; decide
  have hcq_ne_zero : content q ≠ 0 := by rw [hq]; decide
  have hp_ne : p ≠ 0 := by
    intro hp0
    apply hcp_ne_zero
    rw [hp0, content_zero]
  have hq_ne : q ≠ 0 := by
    intro hq0
    apply hcq_ne_zero
    rw [hq0, content_zero]
  exact mul_ne_zero_int p q hp_ne hq_ne

/-- Factoring a constant out of a `diagonalMulCoeffTerm` foldl with `scale`'d
polynomials. -/
private theorem foldl_add_int_diagonal_scaled
    (a b : Int) (r s : DensePoly Int) (n : Nat) :
    ∀ m, (List.range m).foldl
        (fun acc i => acc + diagonalMulCoeffTerm (scale a r) (scale b s) n i) 0 =
      a * b * (List.range m).foldl
        (fun acc i => acc + diagonalMulCoeffTerm r s n i) 0
  | 0 => by simp
  | m' + 1 => by
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [foldl_add_int_diagonal_scaled a b r s n m']
      have hterm : diagonalMulCoeffTerm (scale a r) (scale b s) n m' =
          a * b * diagonalMulCoeffTerm r s n m' := by
        unfold diagonalMulCoeffTerm
        by_cases hn : n < m'
        · simp [hn]
        · rw [if_neg hn]
          rw [coeff_scale a r m' (Int.mul_zero a)]
          rw [coeff_scale b s (n - m') (Int.mul_zero b)]
          grind
      rw [hterm]
      grind

/-- Coefficient identity: scaling both factors of a product. -/
private theorem coeff_scale_mul_scale (a b : Int) (r s : DensePoly Int) (n : Nat) :
    ((scale a r) * (scale b s)).coeff n = a * b * (r * s).coeff n := by
  rw [coeff_mul (scale a r) (scale b s) n]
  rw [coeff_mul r s n]
  rw [mulCoeffSum_eq_diagonal (scale a r) (scale b s) n,
      mulCoeffSum_eq_diagonal r s n]
  rw [diagonalSum_eq_degree_bound (scale a r) (scale b s) n,
      diagonalSum_eq_degree_bound r s n]
  exact foldl_add_int_diagonal_scaled a b r s n (n + 1)

/-- Gauss's lemma for primitive integer polynomials: the product of two
primitive polynomials is primitive. -/
theorem content_mul_of_primitive (p q : DensePoly Int)
    (hp : content p = 1) (hq : content q = 1) :
    content (p * q) = 1 := by
  -- contentNat (p * q) is nonzero (since p * q ≠ 0 by integral domain).
  have hpq_ne : p * q ≠ 0 := mul_ne_zero_of_primitive p q hp hq
  have hpq_size : 0 < (p * q).size := by
    rcases Nat.lt_or_ge 0 (p * q).size with h | h
    · exact h
    · exfalso
      apply hpq_ne
      apply ext_coeff
      intro n
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le (p * q) (by omega)
  have hpq_top_ne : (p * q).coeff ((p * q).size - 1) ≠ 0 :=
    coeff_last_ne_zero_of_pos_size (p * q) hpq_size
  have hcontentNat_ne_zero : contentNat (p * q) ≠ 0 := by
    intro h0
    have hdvd : (contentNat (p * q) : Int) ∣ (p * q).coeff ((p * q).size - 1) :=
      contentNat_dvd_coeff _ _
    rw [h0] at hdvd
    apply hpq_top_ne
    rcases hdvd with ⟨k, hk⟩
    have hk0 : ((0 : Nat) : Int) * k = (0 : Int) := by
      rw [show ((0 : Nat) : Int) = 0 from rfl, Int.zero_mul]
    rw [hk0] at hk
    exact hk
  have hcp_one : contentNat p = 1 := by
    have h : Int.ofNat (contentNat p) = 1 := hp
    have h' : Int.ofNat (contentNat p) = Int.ofNat 1 := h
    exact Int.ofNat_inj.mp h'
  have hcq_one : contentNat q = 1 := by
    have h : Int.ofNat (contentNat q) = 1 := hq
    have h' : Int.ofNat (contentNat q) = Int.ofNat 1 := h
    exact Int.ofNat_inj.mp h'
  -- Suppose contentNat(pq) ≠ 1; derive contradiction.
  show Int.ofNat (contentNat (p * q)) = 1
  apply congrArg Int.ofNat
  apply Classical.byContradiction
  intro hne
  have h_gt_one : 1 < contentNat (p * q) := by
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hcontentNat_ne_zero) with heq | hlt
    · exact absurd heq.symm hne
    · exact hlt
  rcases exists_natPrime_dvd_of_one_lt _ h_gt_one with ⟨r, hr, hrd⟩
  have h_r_dvd_each : ∀ n, (r : Int) ∣ (p * q).coeff n := by
    intro n
    have hcontent_dvd : (contentNat (p * q) : Int) ∣ (p * q).coeff n :=
      contentNat_dvd_coeff _ n
    have hr_dvd_content : (r : Int) ∣ (contentNat (p * q) : Int) :=
      Int.ofNat_dvd.mpr hrd
    exact Int.dvd_trans hr_dvd_content hcontent_dvd
  rcases natPrime_dvd_contentNat_or_dvd_contentNat_of_dvd_mul hr p q h_r_dvd_each
    with hp_dvd | hq_dvd
  · rw [hcp_one] at hp_dvd
    have hr_le : r ≤ 1 := Nat.le_of_dvd (by omega) hp_dvd
    have hr_ge : 2 ≤ r := hr.1
    omega
  · rw [hcq_one] at hq_dvd
    have hr_le : r ≤ 1 := Nat.le_of_dvd (by omega) hq_dvd
    have hr_ge : 2 ≤ r := hr.1
    omega

/-- Gauss's lemma on content (multiplicative form): the content of a product
of integer polynomials is the product of their contents. Strengthens
`content_mul_of_primitive` to non-primitive inputs by decomposing each
factor into its content and primitive part. -/
theorem content_mul (p q : DensePoly Int) :
    content (p * q) = content p * content q := by
  by_cases hcp : content p = 0
  · have hp_zero : p = 0 := by
      apply ext_coeff
      intro n
      have hcnp : contentNat p = 0 := by
        have h' : Int.ofNat (contentNat p) = Int.ofNat 0 := hcp
        exact Int.ofNat_inj.mp h'
      have hdvd : (contentNat p : Int) ∣ p.coeff n := contentNat_dvd_coeff p n
      rw [hcnp] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [coeff_zero]
      simpa using hk
    rw [hp_zero, zero_mul, content_zero, Int.zero_mul]
  by_cases hcq : content q = 0
  · have hq_zero : q = 0 := by
      apply ext_coeff
      intro n
      have hcnq : contentNat q = 0 := by
        have h' : Int.ofNat (contentNat q) = Int.ofNat 0 := hcq
        exact Int.ofNat_inj.mp h'
      have hdvd : (contentNat q : Int) ∣ q.coeff n := contentNat_dvd_coeff q n
      rw [hcnq] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [coeff_zero]
      simpa using hk
    have hpzero : p * (0 : DensePoly Int) = 0 := by
      rw [mul_comm_poly p (0 : DensePoly Int)]
      exact zero_mul p
    rw [hq_zero, hpzero, content_zero, Int.mul_zero]
  have hp_prim : content (primitivePart p) = 1 := primitivePart_primitive p hcp
  have hq_prim : content (primitivePart q) = 1 := primitivePart_primitive q hcq
  have hpq_prim : content (primitivePart p * primitivePart q) = 1 :=
    content_mul_of_primitive _ _ hp_prim hq_prim
  have hpq_eq :
      p * q = scale (content p * content q) (primitivePart p * primitivePart q) := by
    apply ext_coeff
    intro n
    have hp_decomp : p = scale (content p) (primitivePart p) :=
      (content_mul_primitivePart p).symm
    have hq_decomp : q = scale (content q) (primitivePart q) :=
      (content_mul_primitivePart q).symm
    rw [show (p * q).coeff n = ((scale (content p) (primitivePart p)) *
          (scale (content q) (primitivePart q))).coeff n from by
        rw [← hp_decomp, ← hq_decomp]]
    rw [coeff_scale_mul_scale]
    rw [coeff_scale (content p * content q) (primitivePart p * primitivePart q) n
      (Int.mul_zero _)]
  rw [hpq_eq, content_scale_int, hpq_prim, Int.mul_one]
  -- The product `content p * content q` is nonneg (both are `Int.ofNat`-coerced),
  -- so its `natAbs` round-trip equals itself.
  show Int.ofNat (content p * content q).natAbs = content p * content q
  show Int.ofNat (Int.ofNat (contentNat p) * Int.ofNat (contentNat q)).natAbs =
    Int.ofNat (contentNat p) * Int.ofNat (contentNat q)
  rfl

/-- Gauss's lemma on content (divisibility form): if a natural number `d`
divides every coefficient of `p * q`, then it divides `contentNat p *
contentNat q`. This is the divisibility witness needed by the McCoy row
construction in #3440 and the downstream chain `#3440 → #3435 → #3389 →
#3346 → #3252`. -/
theorem dvd_contentNat_mul_of_dvd_mul_coeff
    (p q : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ (p * q).coeff n) :
    d ∣ contentNat p * contentNat q := by
  -- Edge cases where one factor has zero content collapse to `d ∣ 0`.
  by_cases hcp : contentNat p = 0
  · rw [hcp, Nat.zero_mul]; exact Nat.dvd_zero d
  by_cases hcq : contentNat q = 0
  · rw [hcq, Nat.mul_zero]; exact Nat.dvd_zero d
  -- Both contents are nonzero, so the primitive parts are primitive.
  have hcp_ne : content p ≠ 0 := by
    intro h0
    apply hcp
    have h' : Int.ofNat (contentNat p) = Int.ofNat 0 := h0
    exact Int.ofNat_inj.mp h'
  have hcq_ne : content q ≠ 0 := by
    intro h0
    apply hcq
    have h' : Int.ofNat (contentNat q) = Int.ofNat 0 := h0
    exact Int.ofNat_inj.mp h'
  have hp_prim : content (primitivePart p) = 1 := primitivePart_primitive p hcp_ne
  have hq_prim : content (primitivePart q) = 1 := primitivePart_primitive q hcq_ne
  -- Gauss: the product of primitives is primitive.
  have hpq_prim : content (primitivePart p * primitivePart q) = 1 :=
    content_mul_of_primitive _ _ hp_prim hq_prim
  -- Recover `p * q` as a scaled product of primitives.
  have hp_decomp : scale (content p) (primitivePart p) = p := content_mul_primitivePart p
  have hq_decomp : scale (content q) (primitivePart q) = q := content_mul_primitivePart q
  -- Recover `p * q` as a scaled product of primitives at the algebraic level.
  have hmul_eq : scale (content p) (primitivePart p) *
      scale (content q) (primitivePart q) = p * q := by
    rw [hp_decomp, hq_decomp]
  -- (p * q).coeff n = content p * content q * (p' * q').coeff n
  have hcoeff_eq : ∀ n, (p * q).coeff n =
      (content p * content q) *
        (primitivePart p * primitivePart q).coeff n := by
    intro n
    rw [← hmul_eq]
    exact coeff_scale_mul_scale (content p) (content q)
      (primitivePart p) (primitivePart q) n
  -- The scalar `content p * content q` is annihilated by `d`.
  have h_scaled_dvd : ∀ n, (d : Int) ∣
      (content p * content q) * (primitivePart p * primitivePart q).coeff n := by
    intro n
    rw [← hcoeff_eq]
    exact h n
  have h_int_dvd : (d : Int) ∣ content p * content q :=
    nat_dvd_of_scalar_mul_primitive_coeff_dvd _ d (content p * content q)
      hpq_prim h_scaled_dvd
  -- Convert Int divisibility to Nat divisibility on the natAbs.
  rw [Int.ofNat_dvd_left] at h_int_dvd
  have hnatAbs : (content p * content q).natAbs = contentNat p * contentNat q := by
    unfold content
    rfl
  rw [hnatAbs] at h_int_dvd
  exact h_int_dvd

private theorem dvd_coeff_mul_of_dvd_contentNat_mul
    (p q : DensePoly Int) (d i j : Nat)
    (hcontent : d ∣ contentNat p * contentNat q) :
    (d : Int) ∣ p.coeff i * q.coeff j := by
  have hpcoeff : (contentNat p : Int) ∣ p.coeff i := contentNat_dvd_coeff p i
  have hqcoeff : (contentNat q : Int) ∣ q.coeff j := contentNat_dvd_coeff q j
  rcases hpcoeff with ⟨a, ha⟩
  rcases hqcoeff with ⟨b, hb⟩
  have hcontent_int : (d : Int) ∣ ((contentNat p * contentNat q : Nat) : Int) :=
    Int.ofNat_dvd.mpr hcontent
  rcases hcontent_int with ⟨c, hc⟩
  refine ⟨c * (a * b), ?_⟩
  rw [ha, hb]
  have hc' : (contentNat p : Int) * (contentNat q : Int) = (d : Int) * c := by
    simpa using hc
  calc
    (contentNat p : Int) * a * ((contentNat q : Int) * b) =
        ((contentNat p : Int) * (contentNat q : Int)) * (a * b) := by
          grind
    _ = ((d : Int) * c) * (a * b) := by
          rw [hc']
    _ = (d : Int) * (c * (a * b)) := by
          grind

/-- Content/Gauss finite-row helper for McCoy-style coefficient arrays.

If `p` and `q` are finite polynomial packages for coefficient families
`pCoeff` and `qCoeff`, and every coefficient of `p * q` is divisible by
`d`, then Gauss's content divisibility forces the whole selected row
`pCoeff i * qCoeff k` to be divisible by `d`. -/
private theorem finiteCoeffMcCoyRow_of_truncated_product_coeff_dvd
    (pCoeff qCoeff : Nat → Int) (p q : DensePoly Int) (d bound k : Nat)
    (hpCoeff : ∀ i, i ≤ bound → p.coeff i = pCoeff i)
    (hqCoeff : q.coeff k = qCoeff k)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n) :
    ∀ i, i ≤ bound → (d : Int) ∣ pCoeff i * qCoeff k := by
  have hcontent : d ∣ contentNat p * contentNat q :=
    dvd_contentNat_mul_of_dvd_mul_coeff p q d hprod
  intro i hi
  have hrow := dvd_coeff_mul_of_dvd_contentNat_mul p q d i k hcontent
  simpa [hpCoeff i hi, hqCoeff] using hrow

/-- Coefficient-family version of the content/Gauss McCoy row helper.

This is the finite-array row step after callers have normalized the convolution
hypotheses into divisibility of the truncated product polynomial's
coefficients. -/
private theorem finiteCoeffMcCoyRow_of_truncated_product_coeff_family_dvd
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod :
      ∀ n, (d : Int) ∣
        (finiteCoeffFamilyPoly pCoeff bound * finiteCoeffFamilyPoly qCoeff k).coeff n) :
    ∀ i, i ≤ bound → (d : Int) ∣ pCoeff i * qCoeff k := by
  exact finiteCoeffMcCoyRow_of_truncated_product_coeff_dvd pCoeff qCoeff
    (finiteCoeffFamilyPoly pCoeff bound) (finiteCoeffFamilyPoly qCoeff k)
    d bound k
    (fun i hi => finiteCoeffFamilyPoly_coeff_of_le pCoeff bound i hi)
    (finiteCoeffFamilyPoly_coeff_of_le qCoeff k k (Nat.le_refl k))
    hprod

private theorem finiteCoeffFamilyPoly_mul_coeff_dvd_of_finiteCoeffConvolution
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod : ∀ n, n ≤ bound + k → (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s) :
    ∀ n, (d : Int) ∣
      (finiteCoeffFamilyPoly pCoeff bound * finiteCoeffFamilyPoly qCoeff k).coeff n := by
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound]
  by_cases hn : n ≤ bound + k
  · exact dvd_foldl_add_term_of_dvd_congr (d : Int) (List.range (n + 1))
      (fun r => pCoeff r * qCoeff (n - r))
      (fun r => diagonalMulCoeffTerm
        (finiteCoeffFamilyPoly pCoeff bound) (finiteCoeffFamilyPoly qCoeff k) n r)
      (hprod n hn) (by
        intro r hr
        have hrlt : r < n + 1 := List.mem_range.mp hr
        have hnot : ¬ n < r := by omega
        unfold diagonalMulCoeffTerm
        simp only [hnot, ↓reduceIte]
        by_cases hrBound : r ≤ bound
        · by_cases hsK : n - r ≤ k
          · have hp := finiteCoeffFamilyPoly_coeff_of_le pCoeff bound r hrBound
            have hq := finiteCoeffFamilyPoly_coeff_of_le qCoeff k (n - r) hsK
            rw [hp, hq]
            simp
          · have hk_lt : k < n - r := Nat.lt_of_not_ge hsK
            have hq := finiteCoeffFamilyPoly_coeff_of_lt qCoeff k (n - r) hk_lt
            rw [hq]
            simpa using Int.dvd_mul_of_dvd_right (hqAbove (n - r) hk_lt)
        · have hb_lt : bound < r := Nat.lt_of_not_ge hrBound
          have hp := finiteCoeffFamilyPoly_coeff_of_lt pCoeff bound r hb_lt
          rw [hp]
          simpa using hleft r (n - r) hb_lt)
  · apply dvd_list_foldl_add_term_of_forall
    intro r hr
    have hrlt : r < n + 1 := List.mem_range.mp hr
    have hnot : ¬ n < r := by omega
    unfold diagonalMulCoeffTerm
    simp only [hnot, ↓reduceIte]
    by_cases hrBound : r ≤ bound
    · have hk_lt : k < n - r := by
        have hnbk : bound + k < n := Nat.lt_of_not_ge hn
        omega
      have hq := finiteCoeffFamilyPoly_coeff_of_lt qCoeff k (n - r) hk_lt
      rw [hq]
      simp
    · have hb_lt : bound < r := Nat.lt_of_not_ge hrBound
      have hp := finiteCoeffFamilyPoly_coeff_of_lt pCoeff bound r hb_lt
      rw [hp]
      simp

/-- Finite coefficient-array McCoy annihilator over `Int`: if every relevant
finite convolution coefficient is divisible by `d`, all right coefficients
above `k` are divisible by `d`, and the left family is supported modulo `d`
through `bound`, then the `k`-th right coefficient annihilates every left
coefficient up to `bound`. -/
private theorem finiteCoeffMcCoyAnnihilator
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod : ∀ n, n ≤ bound + k → (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s) :
    ∀ i, i ≤ bound → (d : Int) ∣ qCoeff k * pCoeff i := by
  intro i hi
  let p := finiteCoeffFamilyPoly pCoeff bound
  let q := finiteCoeffFamilyPoly qCoeff k
  have hmul : ∀ n, (d : Int) ∣ (p * q).coeff n := by
    intro n
    simpa [p, q] using
      finiteCoeffFamilyPoly_mul_coeff_dvd_of_finiteCoeffConvolution
        pCoeff qCoeff d bound k hprod hqAbove hleft n
  have hrow := finiteCoeffMcCoyRow_of_truncated_product_coeff_family_dvd
    pCoeff qCoeff d bound k (by simpa [p, q] using hmul) i hi
  simpa [Int.mul_comm] using hrow

/-- McCoy annihilator for `DensePoly Int`: if every coefficient of `p * q` is
divisible by `d`, then `q.coeff k` annihilates every coefficient of `p` modulo
`d`. This is the polynomial instantiation of `finiteCoeffMcCoyAnnihilator`
when `pCoeff = p.coeff` and `qCoeff = q.coeff`; downstream callers couple it
with a "last non-divisible coefficient" witness, supplying `hqAbove`. -/
private theorem dvd_last_q_coeff_mul_p_coeff_of_dvd_mul_coeff_of_q_above
    (p q : DensePoly Int) (d k : Nat)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n)
    (_hqAbove : ∀ s, k < s → (d : Int) ∣ q.coeff s) :
    ∀ i, (d : Int) ∣ q.coeff k * p.coeff i := by
  intro i
  have hrow :=
    finiteCoeffMcCoyRow_of_truncated_product_coeff_dvd
      p.coeff q.coeff p q d i k
      (fun _ _ => rfl) rfl hprod i (Nat.le_refl i)
  simpa [Int.mul_comm] using hrow

/-- Public McCoy scalar-annihilator wrapper for integer dense polynomials.

If `d` divides every coefficient of `p * q` and some coefficient of `q` is not
divisible by `d`, then a non-`d`-divisible scalar annihilates all coefficients
of `p` modulo `d`. -/
theorem exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff
    (p q : DensePoly Int) (d : Nat)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n)
    (hq : ∃ n, ¬ (d : Int) ∣ q.coeff n) :
    ∃ a : Int, (¬ (d : Int) ∣ a) ∧
      ∀ i, (d : Int) ∣ a * p.coeff i := by
  rcases exists_last_not_natCast_dvd_coeff q d hq with ⟨k, hk, hqAbove⟩
  refine ⟨q.coeff k, hk, ?_⟩
  exact dvd_last_q_coeff_mul_p_coeff_of_dvd_mul_coeff_of_q_above p q d k hprod hqAbove

/-- Coefficient divisibility transfer for primitive products: if `p` is
primitive (content one) and a natural number `d` divides every coefficient of
`p * q`, then `d` divides every coefficient of `q`. Proved by contradiction
using the McCoy scalar annihilator
`exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff` and the
primitive scalar annihilator `nat_dvd_of_scalar_mul_primitive_coeff_dvd`. -/
theorem coeff_dvd_of_primitive_mul_coeff_dvd
    (p q : DensePoly Int) (d : Nat)
    (hp : content p = 1)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n) :
    ∀ n, (d : Int) ∣ q.coeff n := by
  intro n
  apply Classical.byContradiction
  intro hn
  rcases exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff
    p q d hprod ⟨n, hn⟩ with ⟨a, hna, ha⟩
  exact hna (nat_dvd_of_scalar_mul_primitive_coeff_dvd p d a hp ha)

end DensePoly
end Hex
