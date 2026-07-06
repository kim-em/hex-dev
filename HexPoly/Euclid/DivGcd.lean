/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Grind.Ring.Basic
public import Init.Data.List.Lemmas
public import HexPoly.Operations

public section
set_option backward.proofsInPublic true

/-!
Field-based long division, `modByMonic`, and the derived `gcd`/`xgcd`
algorithms for array-backed `DensePoly`, with their law-based
specification theorems (`divMod_spec`, `gcd_dvd_*`, `xgcd_bezout`).
-/
namespace Hex

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- The leading coefficient, or `0` for the zero polynomial. -/
@[expose]
def leadingCoeff (p : DensePoly R) : R :=
  -- Written as `getD (size - 1)` rather than the more natural `back?.getD 0`
  -- because `Array.back?` does not reduce in the kernel under the module
  -- system (lean4 Array.back? reducibility issue), which would break the
  -- `decide`/`rfl` defeq proofs downstream. Revert to `coeffs.back?.getD 0`
  -- once the upstream fix lands.
  p.coeffs.getD (p.coeffs.size - 1) (Zero.zero : R)

/-- The zero polynomial has leading coefficient `0`. Registered as a `simp`
normal form so callers reasoning about `leadingCoeff` discharge the zero case
automatically. -/
@[simp, grind =] theorem leadingCoeff_zero : (0 : DensePoly R).leadingCoeff = 0 := by
  unfold leadingCoeff
  rw [show (DensePoly.coeffs (0 : DensePoly R)) = #[] from rfl]
  rfl

/-- The constant polynomial `1`. -/
instance [One R] : One (DensePoly R) where
  one := C 1

/-- The leading coefficient of the constant polynomial `C c` is `c` itself,
covering both `c = 0` (the empty backing array) and `c ≠ 0`. The `simp` form
lets callers read the leading coefficient off any constant. -/
@[simp, grind =] theorem leadingCoeff_C (c : R) : (C c).leadingCoeff = c := by
  by_cases hc : c = (0 : R)
  · rw [hc]
    unfold leadingCoeff
    rw [coeffs_C_zero]
    rfl
  · unfold leadingCoeff
    rw [coeffs_C_of_ne_zero hc]
    rfl

/-- The constant polynomial `1` has leading coefficient `1`, hence is monic.
Specialises `leadingCoeff_C` and feeds the monicity facts about `1` that the
division and gcd routines rely on. -/
@[simp, grind =] theorem leadingCoeff_one [One R] : (1 : DensePoly R).leadingCoeff = 1 := by
  change (C (1 : R)).leadingCoeff = 1
  rw [leadingCoeff_C]

/-- A polynomial is monic when its leading coefficient is `1`. -/
@[expose]
def Monic [One R] (p : DensePoly R) : Prop :=
  p.leadingCoeff = 1

/-- A monic polynomial has leading coefficient `1`. Forwarding lemma so callers
do not need to unfold `Monic`. -/
theorem leadingCoeff_eq_one_of_monic [One R] {p : DensePoly R} (hp : p.Monic) :
    p.leadingCoeff = 1 := hp

/-- Characterization of `Monic` by the leading coefficient equation. -/
theorem monic_iff_leadingCoeff_eq_one [One R] {p : DensePoly R} :
    p.Monic ↔ p.leadingCoeff = 1 := Iff.rfl

/-- For a nonzero normalized dense polynomial, `leadingCoeff` is the coefficient
at the last stored index. -/
theorem leadingCoeff_eq_coeff_last (p : DensePoly R) (_hpos : 0 < p.size) :
    p.leadingCoeff = p.coeff (p.size - 1) := by
  simp only [leadingCoeff, coeff, size]

/-- The leading coefficient of a nonzero normalized dense polynomial is nonzero. -/
theorem leadingCoeff_ne_zero_of_pos_size (p : DensePoly R) (hpos : 0 < p.size) :
    p.leadingCoeff ≠ (Zero.zero : R) := by
  rw [leadingCoeff_eq_coeff_last p hpos]
  exact coeff_last_ne_zero_of_pos_size p hpos

/-- `arrayDegreeAux coeffs fuel` scans indices below `fuel` downward and returns the
greatest index whose coefficient is nonzero, or `none` if every coefficient below `fuel` is zero. -/
@[expose]
def arrayDegreeAux (coeffs : Array R) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      let i := fuel
      if coeffs.getD i (Zero.zero : R) = (Zero.zero : R) then
        arrayDegreeAux coeffs fuel
      else
        some i

/-- `arrayDegree? coeffs` is the highest index of a nonzero coefficient of `coeffs`, or `none`
when every coefficient is zero, computed by scanning from `coeffs.size` downward. -/
@[expose]
def arrayDegree? (coeffs : Array R) : Option Nat :=
  arrayDegreeAux coeffs coeffs.size

/-- A degree `arrayDegreeAux` reports lies strictly below the scan ceiling `fuel`. -/
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

/-- The coefficient at a degree `arrayDegreeAux` reports is nonzero. -/
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

/-- When `arrayDegreeAux` returns `none`, every coefficient at an index below `fuel` is zero. -/
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

/-- Every coefficient strictly above a degree `arrayDegreeAux` reports and below `fuel` is zero. -/
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

/-- A degree `arrayDegree?` reports lies strictly below `coeffs.size`. -/
private theorem arrayDegree?_some_lt {coeffs : Array R} {rd : Nat}
    (h : arrayDegree? coeffs = some rd) :
    rd < coeffs.size := by
  exact arrayDegreeAux_some_lt h

/-- The coefficient at a degree `arrayDegree?` reports is nonzero. -/
private theorem arrayDegree?_some_coeff_ne_zero {coeffs : Array R} {rd : Nat}
    (h : arrayDegree? coeffs = some rd) :
    coeffs.getD rd (Zero.zero : R) ≠ (Zero.zero : R) := by
  exact arrayDegreeAux_some_coeff_ne_zero h

/-- Every coefficient at an index above a degree `arrayDegree?` reports is zero. -/
private theorem arrayDegree?_some_above_eq_zero {coeffs : Array R} {rd i : Nat}
    (h : arrayDegree? coeffs = some rd) (hrd : rd < i) :
    coeffs.getD i (Zero.zero : R) = (Zero.zero : R) := by
  by_cases hi : i < coeffs.size
  · exact arrayDegreeAux_some_above_eq_zero h hrd hi
  · unfold Array.getD
    exact dif_neg hi

/-- When `arrayDegree?` returns `none`, every coefficient is zero. -/
private theorem arrayDegree?_none_getD_eq_zero {coeffs : Array R} {i : Nat}
    (h : arrayDegree? coeffs = none) :
    coeffs.getD i (Zero.zero : R) = (Zero.zero : R) := by
  by_cases hi : i < coeffs.size
  · exact arrayDegreeAux_none_getD_eq_zero h hi
  · unfold Array.getD
    exact dif_neg hi

/-- If every coefficient at an index `≥ bound` is zero (with `bound` positive), the normalized
degree of `ofCoeffs coeffs` is below `bound`. -/
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

/-- One coefficient of a long-division elimination step: subtract `coeff * q[j]` from
position `shift + j` of `next`, the inner action folded by `subtractScaledShift` to wipe
out the leading term of the current remainder. -/
@[expose]
def subtractScaledShiftStep [Sub R] [Mul R]
    (q : Array R) (shift : Nat) (coeff : R) (next : Array R) (j : Nat) : Array R :=
  let idx := shift + j
  next.set! idx (next.getD idx (Zero.zero : R) - coeff * q.getD j (Zero.zero : R))

/-- Subtract `coeff` times the divisor `q` shifted up by `shift` positions from the
remainder `rem`, i.e. one full long-division step `rem - coeff * xˢʰⁱᶠᵗ * q`, realised by
folding `subtractScaledShiftStep` over every index of `q`. -/
@[expose]
def subtractScaledShift [Sub R] [Mul R]
    (rem q : Array R) (shift : Nat) (coeff : R) : Array R :=
  (List.range q.size).foldl (subtractScaledShiftStep q shift coeff) rem

omit [DecidableEq R] in
/-- Reading back the value just written at an in-bounds index `n` of `xs.set! n v`
returns `v`, the in-bounds half of the `set!`/`getD` interaction used throughout the
array long-division getD characterisations. -/
private theorem array_getD_set!_same (xs : Array R) (n : Nat) (v : R)
    (hn : n < xs.size) :
    (xs.set! n v).getD n (Zero.zero : R) = v := by
  simp [Array.getD, hn]

omit [DecidableEq R] in
/-- Writing at index `k ≠ n` leaves the value read back at `n` of `xs.set! k v`
unchanged, the disjoint-index half of the `set!`/`getD` interaction used to show
`subtractScaledShift` only perturbs the elimination window. -/
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
/-- A fold of `subtractScaledShiftStep` over index list `xs` leaves position `n`
untouched whenever no step writes there (`shift + j ≠ n` for all `j ∈ xs`), the key
disjointness fact underpinning the `getD` characterisations below. -/
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
/-- Folding `subtractScaledShiftStep` preserves the array length, since each step is a
`set!` that never grows the array; needed to keep elimination-window bounds valid across
the fold. -/
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
/-- `subtractScaledShift` leaves position `n` unchanged when it lies outside the
elimination window (`shift + j ≠ n` for every `j < q.size`), specialising the fold
disjointness lemma to a full subtract step. -/
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
/-- Closed form for position `n` after folding `subtractScaledShiftStep` over
`List.range m`: indices inside the window `shift ≤ n < shift + m` get
`coeff * q[n - shift]` subtracted, all others are untouched; the engine behind the full
`subtractScaledShift_getD` characterisation. -/
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
/-- Full pointwise specification of `subtractScaledShift`: each position `n` in the
window `shift ≤ n < shift + q.size` has `coeff * q[n - shift]` subtracted and every other
position is unchanged, the definitive `getD` law callers reason with. -/
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
/-- At the top window position `shift + qDegree`, `subtractScaledShift` subtracts
`coeff` times the leading coefficient `q[qDegree]`; the case that, with the right
`coeff`, zeroes the remainder's leading term and drops its degree. -/
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
/-- Above the top window position (`shift + qDegree < n`), `subtractScaledShift` leaves
`rem[n]` unchanged, confirming the elimination step never touches coefficients strictly
higher than the remainder's current degree. -/
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
/-- When the chosen `coeff` makes the leading subtraction cancel exactly
(`rem[shift+qDegree] - coeff * q[qDegree] = 0`), the top window position of
`subtractScaledShift` becomes zero, the degree-drop guarantee each long-division step
relies on. -/
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

/-- Runtime helper for `subtractScaledShift`: subtract `coeff * q[j]` from position
`shift + j` of `rem` for `j = 0 … cnt-1`, tail-recursively. Returns the same array
value as `(List.range q.size).foldl (subtractScaledShiftStep q shift coeff) rem` when
called with `j = 0`, `cnt = q.size`, but does not allocate the index list. -/
private def subtractScaledShiftImpl [Sub R] [Mul R]
    (q : Array R) (shift : Nat) (coeff : R) : Nat → Nat → Array R → Array R
  | _, 0, rem => rem
  | j, cnt + 1, rem =>
      subtractScaledShiftImpl q shift coeff (j + 1) cnt
        (subtractScaledShiftStep q shift coeff rem j)

/-- Runtime loop for `divModArrayAux` that resumes the degree scan from the previous
remainder degree instead of rescanning from the top each step. The reference loop calls
`arrayDegree? rem` (a scan from `rem.size` downward) on every iteration, which is `O(n)`
per step and `O(n²)` overall; here `ceil` is the scan ceiling, which in the well-formed
case (`q.size = qDegree + 1`) only ever decreases, so the total scanning cost is `O(n)`.
After eliminating at degree `rd`, the only coefficients that can be nonzero are those at
or below `max (rd + 1) (shift + q.size)` — the elimination window tops out at
`shift + q.size - 1` and everything above `rd` was already zero — so seeding the next scan
at that ceiling returns the same index as the reference's `arrayDegree? rem`.
`divModArrayAux_eq_impl` proves the two loops agree on every input. -/
private def divModArrayAuxImplGo [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R) :
    Nat → Nat → Array R → Array R → Array R × Array R
  | 0, _, quot, rem => (quot, rem)
  | fuel + 1, ceil, quot, rem =>
      match arrayDegreeAux rem ceil with
      | none => (quot, rem)
      | some rd =>
          if rd < qDegree then
            (quot, rem)
          else
            let shift := rd - qDegree
            let coeff := scaleLead (rem.getD rd (Zero.zero : R))
            let quot := quot.set! shift coeff
            let rem := subtractScaledShiftImpl q shift coeff 0 q.size rem
            divModArrayAuxImplGo q qDegree scaleLead fuel
              (Nat.max (rd + 1) (shift + q.size)) quot rem

/-- Runtime implementation of `divModArrayAux`. Seeds the scan ceiling at `rem.size`, so
the first iteration is identical to the reference's `arrayDegree? rem`; thereafter the
ceiling tracks the working degree (see `divModArrayAuxImplGo`). -/
def divModArrayAuxImpl [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R)
    (fuel : Nat) (quot rem : Array R) : Array R × Array R :=
  divModArrayAuxImplGo q qDegree scaleLead fuel rem.size quot rem

/-- The fuel-bounded long-division loop: while the remainder's degree `rd` is at least
the divisor degree `qDegree`, pick the quotient coefficient `scaleLead (rem[rd])`, record
it in `quot`, eliminate the leading term via `subtractScaledShift`, and recurse, returning
the final `(quotient, remainder)` pair. The compiled runtime uses the value-equal
`divModArrayAuxImpl` (proved by `divModArrayAux_eq_impl`, registered `@[csimp]`), which
tracks the working degree instead of rescanning. -/
@[expose]
noncomputable def divModArrayAux [Sub R] [Mul R]
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

/-- Dropping a run of indices on which `coeffs` is zero does not change what
`arrayDegreeAux` reports: scanning down from `c + n` through `n` zeros reaches the same
answer as scanning down from `c`. -/
private theorem arrayDegreeAux_drop {coeffs : Array R} {c : Nat}
    (h : ∀ i, c ≤ i → coeffs.getD i (Zero.zero : R) = (Zero.zero : R)) (n : Nat) :
    arrayDegreeAux coeffs (c + n) = arrayDegreeAux coeffs c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hzero : coeffs.getD (c + n) (Zero.zero : R) = (Zero.zero : R) := h _ (by omega)
      show (if coeffs.getD (c + n) (Zero.zero : R) = (Zero.zero : R)
              then arrayDegreeAux coeffs (c + n) else some (c + n)) = arrayDegreeAux coeffs c
      rw [if_pos hzero]
      exact ih

/-- When every coefficient at or above the scan ceiling `ceil` is zero, the bounded scan
`arrayDegreeAux coeffs ceil` reports the same degree as the full `arrayDegree? coeffs`. -/
private theorem arrayDegreeAux_eq_arrayDegree? {coeffs : Array R} {ceil : Nat}
    (h : ∀ i, ceil ≤ i → coeffs.getD i (Zero.zero : R) = (Zero.zero : R)) :
    arrayDegreeAux coeffs ceil = arrayDegree? coeffs := by
  have hsize : ∀ i, coeffs.size ≤ i → coeffs.getD i (Zero.zero : R) = (Zero.zero : R) := by
    intro i hi
    unfold Array.getD
    exact dif_neg (by omega)
  rw [arrayDegree?]
  rcases Nat.le_total ceil coeffs.size with hle | hle
  · have hdrop := arrayDegreeAux_drop h (coeffs.size - ceil)
    rw [show ceil + (coeffs.size - ceil) = coeffs.size from by omega] at hdrop
    exact hdrop.symm
  · have hdrop := arrayDegreeAux_drop hsize (ceil - coeffs.size)
    rw [show coeffs.size + (ceil - coeffs.size) = ceil from by omega] at hdrop
    exact hdrop

omit [DecidableEq R] in
/-- The tail-recursive `subtractScaledShiftImpl` realises the same fold as
`subtractScaledShiftStep` over `List.range' j cnt`. -/
private theorem subtractScaledShiftImpl_eq_foldl [Sub R] [Mul R]
    (q : Array R) (shift : Nat) (coeff : R) (cnt : Nat) :
    ∀ (j : Nat) (rem : Array R),
      subtractScaledShiftImpl q shift coeff j cnt rem =
        (List.range' j cnt).foldl (subtractScaledShiftStep q shift coeff) rem := by
  induction cnt with
  | zero => intro j rem; rfl
  | succ cnt ih =>
      intro j rem
      rw [subtractScaledShiftImpl, List.range'_succ]
      simp only [List.foldl_cons]
      exact ih (j + 1) (subtractScaledShiftStep q shift coeff rem j)

omit [DecidableEq R] in
/-- The runtime subtraction loop computes the same array as `subtractScaledShift`. -/
private theorem subtractScaledShiftImpl_eq [Sub R] [Mul R]
    (rem q : Array R) (shift : Nat) (coeff : R) :
    subtractScaledShiftImpl q shift coeff 0 q.size rem =
      subtractScaledShift rem q shift coeff := by
  rw [subtractScaledShiftImpl_eq_foldl, subtractScaledShift, List.range_eq_range']

/-- The ceiling-tracking loop `divModArrayAuxImplGo` agrees with the rescanning reference
`divModArrayAux`, provided every coefficient at or above the seed ceiling is already zero. -/
private theorem divModArrayAuxImplGo_eq [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R) (fuel : Nat) :
    ∀ (ceil : Nat) (quot rem : Array R),
      (∀ i, ceil ≤ i → rem.getD i (Zero.zero : R) = (Zero.zero : R)) →
      divModArrayAuxImplGo q qDegree scaleLead fuel ceil quot rem =
        divModArrayAux q qDegree scaleLead fuel quot rem := by
  induction fuel with
  | zero => intro ceil quot rem _; rfl
  | succ fuel ih =>
      intro ceil quot rem hzero
      have hdeg : arrayDegreeAux rem ceil = arrayDegree? rem :=
        arrayDegreeAux_eq_arrayDegree? hzero
      unfold divModArrayAuxImplGo divModArrayAux
      rw [hdeg]
      cases hd : arrayDegree? rem with
      | none => rfl
      | some rd =>
          dsimp only
          by_cases hlt : rd < qDegree
          · rw [if_pos hlt, dif_pos hlt]
          · rw [if_neg hlt, dif_neg hlt]
            rw [subtractScaledShiftImpl_eq rem q (rd - qDegree)
              (scaleLead (rem.getD rd (Zero.zero : R)))]
            apply ih
            intro i hi
            have hb1 : rd + 1 ≤ Nat.max (rd + 1) (rd - qDegree + q.size) :=
              Nat.le_max_left _ _
            have hb2 : rd - qDegree + q.size ≤ Nat.max (rd + 1) (rd - qDegree + q.size) :=
              Nat.le_max_right _ _
            have hi1 : rd < i := by omega
            have hi2 : rd - qDegree + q.size ≤ i := by omega
            rw [subtractScaledShift_getD_of_forall_ne rem q (rd - qDegree)
              (scaleLead (rem.getD rd (Zero.zero : R))) i (by intro j hj; omega)]
            exact arrayDegree?_some_above_eq_zero hd hi1

/-- The runtime long-division loop computes the same quotient/remainder as the reference. -/
private theorem divModArrayAuxImpl_eq [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R)
    (fuel : Nat) (quot rem : Array R) :
    divModArrayAuxImpl q qDegree scaleLead fuel quot rem =
      divModArrayAux q qDegree scaleLead fuel quot rem := by
  unfold divModArrayAuxImpl
  apply divModArrayAuxImplGo_eq
  intro i hi
  unfold Array.getD
  exact dif_neg (by omega)

/-- Register the value-equal `divModArrayAuxImpl` as the compiled implementation of
`divModArrayAux`. Unlike `@[implemented_by]`, the `@[csimp]` swap is backed by the proof
`divModArrayAuxImpl_eq`, so the runtime loop is verified equal to the specification. -/
@[csimp]
theorem divModArrayAux_eq_impl : @divModArrayAux = @divModArrayAuxImpl := by
  funext R _ _ _ _ q qDegree scaleLead fuel quot rem
  exact (divModArrayAuxImpl_eq q qDegree scaleLead fuel quot rem).symm

/-- `divModArrayAux` depends only on the pointwise values of its `scaleLead` argument:
two scaling functions agreeing on every input produce identical quotient/remainder, so
callers may swap in any extensionally-equal leading-coefficient scaler. -/
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

/-- Under a `scaleLead` that cancels each leading term (`a - scaleLead a * q[qDegree] = 0`),
`divModArrayAux` drives every remainder coefficient at index `≥ qDegree` to zero, i.e. the
final remainder has degree `< qDegree`; the core invariant establishing the division
remainder-degree bound. -/
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

/-- Array-backed long division of dense polynomial `p` by `q`: returns `(0, p)` when `q`
is zero, otherwise seeds a zero quotient and runs `divModArrayAux` with `p.size` fuel,
packaging the resulting coefficient arrays back as `DensePoly` quotient and remainder. -/
@[expose]
def divModArray [Sub R] [Mul R]
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
      simp [size]
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
@[expose]
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
@[expose]
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
    have hlast : q.coeffs.size - 1 = 0 := by omega
    rw [hlast]
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
@[expose]
def div [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (divMod p q).1

/-- Remainder from polynomial long division over a field. -/
@[expose]
def mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (divMod p q).2

/-- Remainder from long division by a monic polynomial over a commutative ring. -/
@[expose]
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
  /-- Greatest common divisor returned by the extended Euclidean algorithm. -/
  gcd : DensePoly R
  /-- Bezout coefficient multiplying the left input. -/
  left : DensePoly R
  /-- Bezout coefficient multiplying the right input. -/
  right : DensePoly R

/-- Tail-recursive extended Euclidean algorithm. -/
@[expose]
def xgcdAux [One R] [Add R] [Sub R] [Mul R] [Div R]
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
@[expose]
def xgcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : XGCDResult R :=
  xgcdAux p 1 0 q 0 1 (p.size + q.size + 1)

/-- Tail-recursive Euclidean gcd tracking only the remainder sequence, **without**
the Bezout coefficients. `xgcd`/`xgcdAux` carry the Bezout accumulators `s`, `t`
and update them with a polynomial multiplication (`q * s₁`, `q * t₁`) at every
step on polynomials whose degree grows through the run — that is `O(deg³)` work
and pure waste when only the gcd value is wanted (the common case: the square-free
/ separability test `gcd(f, f') = 1`). `gcdAux` keeps only the remainders and is
`O(deg²)`. -/
@[expose]
def gcdAux [One R] [Add R] [Sub R] [Mul R] [Div R]
    (r₀ r₁ : DensePoly R) (fuel : Nat) : DensePoly R :=
  match fuel with
  | 0 => r₀
  | fuel + 1 =>
      if _hr : r₁.isZero then
        r₀
      else
        gcdAux r₁ (divMod r₀ r₁).2 fuel

/-- The plain remainder gcd agrees with the `gcd` component of the extended
algorithm: `XGCDResult.gcd` never depends on the Bezout accumulators. -/
theorem gcdAux_eq_xgcdAux_gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly R) (fuel : Nat) :
    gcdAux r₀ r₁ fuel = (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero => rfl
  | succ fuel ih =>
      unfold gcdAux xgcdAux
      split
      · rfl
      · exact ih _ _ _ _ _ _

/-- Polynomial gcd over a field. Computed by the plain remainder sequence
(`gcdAux`), **not** the extended algorithm: the gcd value is independent of the
Bezout coefficients, and computing them costs an extra polynomial multiplication
per step (`O(deg³)` vs `O(deg²)`). `xgcd` stays available for callers that
genuinely need Bezout coefficients. -/
@[expose]
def gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  gcdAux p q (p.size + q.size + 1)

/-- `gcd` equals the gcd component of `xgcd`; lets lemmas proved against the
extended algorithm transfer to the plain `gcd`. -/
theorem gcd_eq_xgcd_gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : gcd p q = (xgcd p q).gcd :=
  gcdAux_eq_xgcdAux_gcd p 1 0 q 0 1 (p.size + q.size + 1)

/-- The gcd component returned by `xgcd` is the executable gcd. -/
theorem xgcd_gcd_eq_gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    (xgcd p q).gcd = gcd p q := (gcd_eq_xgcd_gcd p q).symm

/-- The executable gcd of two zero dense polynomials is zero. -/
@[simp, grind =] theorem gcd_zero_zero [One R] [Add R] [Sub R] [Mul R] [Div R] :
    gcd (0 : DensePoly R) (0 : DensePoly R) = 0 := by
  rw [gcd_eq_xgcd_gcd]; rfl

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
@[grind =>]
theorem divMod_spec [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  exact DivModLaws.divMod_spec p q

/-- The polynomial gcd divides the left argument. -/
@[grind =>]
theorem gcd_dvd_left [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    gcd p q ∣ p := by
  exact GcdLaws.gcd_dvd_left p q

/-- The polynomial gcd divides the right argument. -/
@[grind =>]
theorem gcd_dvd_right [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (p q : DensePoly R) :
    gcd p q ∣ q := by
  exact GcdLaws.gcd_dvd_right p q

/-- Every common divisor of `p` and `q` divides `gcd p q`. -/
@[grind =>]
theorem dvd_gcd [One R] [Add R] [Sub R] [Mul R] [Div R] [GcdLaws R]
    (d p q : DensePoly R) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  exact GcdLaws.dvd_gcd d p q

/-- Bezout identity: the extended-gcd coefficients reconstruct the gcd as
`left * p + right * q`. -/
@[grind =>]
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
@[simp, grind =] theorem zero_mod_eq_zero_core {S : Type _}
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
  rw [coeff_ofCoeffs, coeff_add (ofCoeffs coeffs) (monomial shift coeff) n hzero_add,
    coeff_ofCoeffs, coeff_monomial]
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
              exact arrayDegree?_some_lt harray
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
@[grind =>]
theorem divMod_remainder_degree_lt_of_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    0 < q.degree?.getD 0 → (divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  exact DivModLaws.divMod_remainder_degree_lt_of_pos_degree p q

/-- Monic division agrees with field-style division when the divisor is monic. This is the
implementation invariant relating the specialized `divModMonic` path to `divMod`. -/
@[grind =>]
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
  exact congrArg Prod.snd hdiv

/-- Constant-degree divisors are an idempotent edge case for `%`. -/
@[grind =>]
theorem mod_mod_of_not_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    ¬ 0 < q.degree?.getD 0 → (p % q) % q = p % q := by
  exact DivModLaws.mod_mod_of_not_pos_degree p q

/-- The computed remainder has degree below a positive-degree divisor. -/
@[grind =>]
theorem mod_degree_lt_of_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    0 < q.degree?.getD 0 → (p % q).degree?.getD 0 < q.degree?.getD 0 := by
  exact divMod_remainder_degree_lt_of_pos_degree p q

/-- Euclidean division identity: `(p / q) * q + (p % q) = p`. -/
@[grind =>]
theorem div_mul_add_mod [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    (p / q) * q + (p % q) = p := by
  exact divMod_spec p q

/-- If `q ∣ p`, then `p % q = 0`. -/
@[simp, grind =] theorem mod_eq_zero_of_dvd [One R] [Add R] [Sub R] [Mul R] [Div R] [DivModLaws R]
    (p q : DensePoly R) :
    q ∣ p → p % q = 0 := by
  exact DivModLaws.mod_eq_zero_of_dvd p q

/-- Monic division and the generic `%` notation agree when the divisor is monic. -/
@[grind =>]
theorem modByMonic_eq_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) (hq : Monic q) :
    modByMonic p q hq = p % q := by
  rw [modByMonic_eq_divModMonic, mod_eq_divMod, divModMonic_eq_divMod_of_monic p q hq]

/-- The remainder modulo `q` is idempotent under `% q`. -/
@[simp, grind =] theorem mod_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    (p % q) % q = p % q := by
  by_cases hq : 0 < q.degree?.getD 0
  · exact mod_eq_self_of_degree_lt (p % q) q (mod_degree_lt_of_pos_degree p q hq)
  · exact mod_mod_of_not_pos_degree p q hq


end DensePoly
end Hex
