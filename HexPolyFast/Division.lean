/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Reciprocal
public import HexPoly.Euclid.MonicUnique

public section

/-!
Cached reciprocal division.

The executable quotient reverses the dividend, multiplies its low prefix by
the cached reciprocal of the reversed divisor, and reverses the result back.
The remainder uses the same multiplication plan.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- Reverse the first `k` coefficients of a represented series back into a
normalized polynomial.  The explicit bound is independent of any trailing
zeros removed by polynomial normalization. -/
def reversePrefix {n : Nat} (k : Nat) (a : TSeries R n) : DensePoly R :=
  ofList ((List.range k).map fun i => a.coeff (k - 1 - i))

/-- Coefficient law for fixed-bound reverse conversion. -/
theorem coeff_reversePrefix {n : Nat} (k : Nat) (a : TSeries R n) (i : Nat) :
    (reversePrefix k a).coeff i =
      if i < k then a.coeff (k - 1 - i) else 0 := by
  unfold reversePrefix
  rw [coeff_ofList]
  by_cases hi : i < k
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

omit [DecidableEq R] in
private theorem foldRangeExtend (f : Nat → R) (m n : Nat) (hm : m ≤ n)
    (hz : ∀ i, m ≤ i → i < n → f i = 0) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      (List.range m).foldl (fun acc i => acc + f i) 0 := by
  have hn : m + (n - m) = n := by omega
  rw [← hn, List.range_add, List.foldl_append, List.foldl_map]
  apply List.foldl_add_eq_self
  intro j hj
  apply hz (m + j) (by omega)
  have := List.mem_range.mp hj
  omega

private theorem size_le_of_coeff_zero_above {p : DensePoly R} {N : Nat}
    (h : ∀ i, N ≤ i → p.coeff i = 0) : p.size ≤ N := by
  by_cases hle : p.size ≤ N
  · exact hle
  · have hpos : 0 < p.size := by omega
    have hzero := h (p.size - 1) (by omega)
    exact False.elim (coeff_last_ne_zero_of_pos_size p hpos hzero)

/-- Reversing a `k`-coefficient series prefix converts its product's high
coefficients into the corresponding low series convolution. -/
theorem coeff_reversePrefix_mul {n : Nat} (a : TSeries R n)
    (q : DensePoly R) (k t : Nat) (hk : k ≤ n) (ht : t < k)
    (hq : 0 < q.size) :
    (reversePrefix k a * q).coeff (k + q.size - 2 - t) =
      (reverseSeries q n * a).coeff t := by
  let base := k - 1 - t
  have hbase : base + q.size = k + q.size - 1 - t := by
    dsimp [base]
    omega
  have hdeg : k + q.size - 2 - t + 1 = base + q.size := by
    dsimp [base]
    omega
  rw [DensePoly.coeff_mul, mulCoeffSum_eq_diagonal,
    diagonal_eq_degree_bound, TSeries.coeff_mul _ _ t (by omega)]
  unfold TSeries.convCoeff
  rw [show k + q.size - 2 - t + 1 = base + q.size from hdeg,
    List.range_add, List.foldl_append, List.foldl_map]
  have hprefix :
      (List.range base).foldl
          (fun acc i => acc + diagonalMulCoeffTerm
            (reversePrefix k a) q (k + q.size - 2 - t) i) 0 = 0 := by
    apply List.foldl_add_eq_self
    intro i hi
    have hib : i < base := List.mem_range.mp hi
    unfold diagonalMulCoeffTerm
    have hid : i ≤ k + q.size - 2 - t := by omega
    rw [_root_.if_neg (by omega)]
    have hqi : q.size ≤ k + q.size - 2 - t - i := by
      dsimp [base] at hib
      omega
    rw [coeff_eq_zero_of_size_le q hqi]
    exact Lean.Grind.Semiring.mul_zero _
  rw [hprefix]
  have hleft :
      (List.range q.size).foldl
          (fun acc j => acc + diagonalMulCoeffTerm
            (reversePrefix k a) q (k + q.size - 2 - t) (base + j)) 0 =
        (List.range q.size).foldl
          (fun acc j => acc +
            if j < q.size ∧ j ≤ t then
              q.coeff (q.size - 1 - j) * a.coeff (t - j)
            else 0) 0 := by
    apply List.foldl_add_congr
    intro j hj
    have hjs : j < q.size := List.mem_range.mp hj
    unfold diagonalMulCoeffTerm
    rw [_root_.if_neg (by
      dsimp [base]
      omega), coeff_reversePrefix]
    by_cases hjt : j ≤ t
    · rw [_root_.ite_eq_left (by
        dsimp [base]; omega), _root_.ite_eq_left ⟨hjs, hjt⟩]
      have hidx₁ : k + q.size - 2 - t - (base + j) = q.size - 1 - j := by
        dsimp [base]
        omega
      have hidx₂ : k - 1 - (base + j) = t - j := by
        dsimp [base]
        omega
      rw [hidx₁, hidx₂]
      grind
    · rw [_root_.ite_eq_right (by
        dsimp [base]; omega), _root_.ite_eq_right (by omega)]
      exact Lean.Grind.Semiring.zero_mul _
  rw [hleft]
  have hright :
      (List.range (t + 1)).foldl
          (fun acc j => acc + (reverseSeries q n).coeff j * a.coeff (t - j)) 0 =
        (List.range (t + 1)).foldl
          (fun acc j => acc +
            if j < q.size ∧ j ≤ t then
              q.coeff (q.size - 1 - j) * a.coeff (t - j)
            else 0) 0 := by
    apply List.foldl_add_congr
    intro j hj
    have hjt : j ≤ t := by
      have := List.mem_range.mp hj
      omega
    rw [coeff_reverseSeries q n j (by omega)]
    by_cases hjs : j < q.size
    · rw [_root_.ite_eq_left hjs, _root_.ite_eq_left ⟨hjs, hjt⟩]
    · rw [_root_.ite_eq_right hjs, _root_.ite_eq_right (by omega)]
      exact Lean.Grind.Semiring.zero_mul _
  rw [hright]
  let f := fun j =>
    if j < q.size ∧ j ≤ t then
      q.coeff (q.size - 1 - j) * a.coeff (t - j) else 0
  let bound := max q.size (t + 1)
  have hqext := foldRangeExtend f q.size bound (Nat.le_max_left _ _)
    (by
      intro i hi _
      dsimp [f]
      rw [_root_.ite_eq_right (by omega)])
  have htext := foldRangeExtend f (t + 1) bound (Nat.le_max_right _ _)
    (by
      intro i hi _
      dsimp [f]
      rw [_root_.ite_eq_right (by omega)])
  dsimp [f] at hqext htext
  exact hqext.symm.trans htext

/-- Number of quotient coefficients required for division of `p` by `q`.
It is zero for the zero divisor and for a divisor larger than the dividend. -/
def quotientLength (p q : DensePoly R) : Nat :=
  if q.size = 0 || p.size < q.size then 0 else p.size - q.size + 1

/-- A reusable divisor with a reciprocal cached to a fixed capacity. -/
structure DivPlan (R : Type u) [DecidableEq R] [Lean.Grind.CommRing R] where
  mul : MulPlan R
  divisor : DensePoly R
  capacity : Nat
  unitInv : R
  reciprocal : TSeries R capacity
  divisor_ne : divisor ≠ 0
  unitInv_spec : 0 < capacity →
    (reverseSeries divisor capacity).coeff 0 * unitInv = 1
  reciprocal_spec :
    reciprocal = TSeries.invOfUnit (reverseSeries divisor capacity)
      unitInv

/-- Build a cached plan for a nonzero monic divisor. -/
def DivPlan.ofMonic (mul : MulPlan R) (q : DensePoly R)
    (hq : Monic q) (hqne : q ≠ 0) (capacity : Nat) : DivPlan R :=
  let reciprocal := reciprocalWith mul (reverseSeries q capacity) 1
  { mul
    divisor := q
    capacity
    unitInv := 1
    reciprocal
    divisor_ne := hqne
    unitInv_spec := by
      intro hcap
      rw [coeff_reverseSeries_of_lt q capacity 0 hcap (by
        have : q.size ≠ 0 := by
          intro hs
          exact hqne ((size_eq_zero_iff q).mp hs)
        omega)]
      have hqpos : 0 < q.size := by
        apply Nat.pos_of_ne_zero
        intro hs
        exact hqne ((size_eq_zero_iff q).mp hs)
      simp only [Nat.sub_zero]
      have hlead : q.coeff (q.size - 1) = q.leadingCoeff := by
        rfl
      rw [hlead, leadingCoeff_eq_one_of_monic hq]
      grind
    reciprocal_spec := by
      dsimp [reciprocal]
      exact reciprocalWith_eq mul _ 1 }

/-- A monic division plan retains its supplied divisor. -/
@[simp] theorem DivPlan.divisor_ofMonic (mul : MulPlan R) (q : DensePoly R)
    (hq : Monic q) (hqne : q ≠ 0) (capacity : Nat) :
    (DivPlan.ofMonic mul q hq hqne capacity).divisor = q := by
  rfl

/-- Build a cached plan for an arbitrary nonzero divisor over a field. -/
def DivPlan.ofNonzero {F : Type u} [DecidableEq F] [Lean.Grind.Field F]
    (mul : MulPlan F) (q : DensePoly F) (hqne : q ≠ 0)
    (capacity : Nat) : DivPlan F :=
  let u := q.leadingCoeff⁻¹
  let reciprocal := reciprocalWith mul (reverseSeries q capacity) u
  { mul
    divisor := q
    capacity
    unitInv := u
    reciprocal
    divisor_ne := hqne
    unitInv_spec := by
      intro hcap
      rw [coeff_reverseSeries_of_lt q capacity 0 hcap (by
        have : q.size ≠ 0 := by
          intro hs
          exact hqne ((size_eq_zero_iff q).mp hs)
        omega)]
      simp only [Nat.sub_zero]
      have hlead : q.coeff (q.size - 1) = q.leadingCoeff := by
        rfl
      rw [hlead]
      have hqpos : 0 < q.size := by
        apply Nat.pos_of_ne_zero
        intro hs
        exact hqne ((size_eq_zero_iff q).mp hs)
      have hne : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero_of_pos_size q hqpos
      dsimp [u]
      exact Lean.Grind.Field.mul_inv_cancel hne
    reciprocal_spec := by
      dsimp [reciprocal]
      exact reciprocalWith_eq mul _ u }

/-- Quotient obtained from a cached reversed reciprocal. -/
def DivPlan.quotient (plan : DivPlan R) (p : DensePoly R)
    (_hcap : quotientLength p plan.divisor ≤ plan.capacity) : DensePoly R :=
  let k := quotientLength p plan.divisor
  let top := reverseSeries p plan.capacity
  let qrev := seriesMulUpTo plan.mul k top plan.reciprocal
  reversePrefix k qrev

/-- The reciprocal quotient cancels every coefficient in the high window of
the dividend.  The index `t` counts down from the leading coefficient. -/
theorem DivPlan.coeff_quotient_mul_high (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity) (t : Nat)
    (ht : t < quotientLength p plan.divisor) :
    (plan.quotient p hcap * plan.divisor).coeff (p.size - 1 - t) =
      p.coeff (p.size - 1 - t) := by
  let k := quotientLength p plan.divisor
  let top := reverseSeries p plan.capacity
  let qrev := seriesMulUpTo plan.mul k top plan.reciprocal
  have hdpos : 0 < plan.divisor.size := by
    apply Nat.pos_of_ne_zero
    intro hs
    exact plan.divisor_ne ((size_eq_zero_iff plan.divisor).mp hs)
  have hdle : plan.divisor.size ≤ p.size := by
    by_cases hle : plan.divisor.size ≤ p.size
    · exact hle
    · have hlt : p.size < plan.divisor.size := Nat.lt_of_not_ge hle
      have hkzero : k = 0 := by simp [k, quotientLength, hlt]
      omega
  have hkform : k = p.size - plan.divisor.size + 1 := by
    simp [k, quotientLength, plan.divisor_ne, Nat.not_lt.mpr hdle]
  have hkpos : 0 < k := by omega
  have hklep : k ≤ p.size := by
    rw [hkform]
    omega
  have hkcap : k ≤ plan.capacity := hcap
  have hunit : (reverseSeries plan.divisor plan.capacity).coeff 0 *
      plan.unitInv = 1 := plan.unitInv_spec (by omega)
  have hinv : reverseSeries plan.divisor plan.capacity * plan.reciprocal = 1 := by
    rw [plan.reciprocal_spec]
    exact TSeries.invOfUnit_mul _ _ hunit
  have hqrev : TSeries.Agree k qrev (top * plan.reciprocal) := by
    dsimp [qrev]
    rw [seriesMulUpTo_eq]
    exact TSeries.Agree.mulUpTo k top plan.reciprocal
  have hprod : TSeries.Agree k
      (reverseSeries plan.divisor plan.capacity * qrev) top := by
    have hmul := TSeries.Agree.mul
      (TSeries.Agree.refl k (reverseSeries plan.divisor plan.capacity)) hqrev
    intro i hi hik
    have h := hmul i hi hik
    rw [← TSeries.mul_assoc,
      TSeries.mul_comm (reverseSeries plan.divisor plan.capacity) top,
      TSeries.mul_assoc, hinv, TSeries.mul_one] at h
    exact h
  have hidx : k + plan.divisor.size - 2 - t = p.size - 1 - t := by
    rw [hkform]
    omega
  have hbridge :
      (reversePrefix k qrev * plan.divisor).coeff (p.size - 1 - t) =
        (reverseSeries plan.divisor plan.capacity * qrev).coeff t := by
    rw [← hidx]
    exact coeff_reversePrefix_mul qrev plan.divisor k t hkcap ht hdpos
  change (reversePrefix k qrev * plan.divisor).coeff (p.size - 1 - t) = _
  rw [hbridge, hprod t (by omega) ht]
  dsimp [top]
  rw [coeff_reverseSeries_of_lt p plan.capacity t (by omega) (by omega)]

/-- The normalized reciprocal quotient has no more than the requested number
of coefficients. -/
theorem DivPlan.size_quotient_le (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity) :
    (plan.quotient p hcap).size ≤ quotientLength p plan.divisor := by
  unfold DivPlan.quotient reversePrefix
  exact Nat.le_trans (size_ofList_le _) (by simp)

/-- Subtracting the reciprocal quotient product leaves fewer coefficients than
the divisor.  This is the executable division algorithm's termination law. -/
theorem DivPlan.remainder_size_le (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity) :
    (p - mulWith plan.mul (plan.quotient p hcap) plan.divisor).size ≤
      plan.divisor.size - 1 := by
  apply size_le_of_coeff_zero_above
  intro i hi
  rw [coeff_sub_ring, mulWith_eq]
  by_cases hip : i < p.size
  · have hdle : plan.divisor.size ≤ p.size := by omega
    have hkform : quotientLength p plan.divisor =
        p.size - plan.divisor.size + 1 := by
      simp [quotientLength, plan.divisor_ne, Nat.not_lt.mpr hdle]
    let t := p.size - 1 - i
    have ht : t < quotientLength p plan.divisor := by
      dsimp [t]
      rw [hkform]
      omega
    have hcancel := plan.coeff_quotient_mul_high p hcap t ht
    have hidx : p.size - 1 - t = i := by
      dsimp [t]
      omega
    rw [hidx] at hcancel
    rw [hcancel]
    grind
  · rw [coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hip)]
    have hqsize := plan.size_quotient_le p hcap
    have hprod := size_mul_le (plan.quotient p hcap) plan.divisor
    by_cases hdp : plan.divisor.size ≤ p.size
    · have hkform : quotientLength p plan.divisor =
          p.size - plan.divisor.size + 1 := by
        simp [quotientLength, plan.divisor_ne, Nat.not_lt.mpr hdp]
      rw [coeff_eq_zero_of_size_le _ (by rw [hkform] at hqsize; omega)]
      grind
    · have hdlt : p.size < plan.divisor.size := Nat.lt_of_not_ge hdp
      have hkzero : quotientLength p plan.divisor = 0 := by
        simp [quotientLength, hdlt]
      rw [coeff_eq_zero_of_size_le _ (by rw [hkzero] at hqsize; omega)]
      grind

/-- The cached division remainder has degree strictly below every
positive-degree divisor. -/
theorem DivPlan.remainder_degree_lt (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity)
    (hdeg : 0 < plan.divisor.degree?.getD 0) :
    (p - mulWith plan.mul (plan.quotient p hcap) plan.divisor).degree?.getD 0 <
      plan.divisor.degree?.getD 0 := by
  have hdpos : 0 < plan.divisor.size := by
    rcases Nat.eq_zero_or_pos plan.divisor.size with hz | hz
    · rw [(degree?_eq_none_iff plan.divisor).mpr hz, Option.getD_none] at hdeg
      omega
    · exact hz
  have hddegree : plan.divisor.degree?.getD 0 = plan.divisor.size - 1 := by
    rw [degree?_eq_some_of_pos_size plan.divisor hdpos, Option.getD_some]
  let r := p - mulWith plan.mul (plan.quotient p hcap) plan.divisor
  have hrsize : r.size ≤ plan.divisor.size - 1 := plan.remainder_size_le p hcap
  rcases Nat.eq_zero_or_pos r.size with hz | hz
  · rw [(degree?_eq_none_iff r).mpr hz, Option.getD_none, hddegree]
    omega
  · rw [degree?_eq_some_of_pos_size r hz, Option.getD_some, hddegree]
    omega

/-- Divide using a cached reciprocal.  The proof ensures the cached precision
covers the requested quotient; it is erased from executable code. -/
def DivPlan.divMod (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity) :
    DensePoly R × DensePoly R :=
  let q := plan.quotient p hcap
  (q, p - mulWith plan.mul q plan.divisor)

/-- Cached reciprocal division agrees with the established long-division
result whenever coefficient division satisfies the laws needed by that
result.  The size-one divisor case is handled as an exact product rather than
being hidden by the default-zero degree convention. -/
theorem DivPlan.divMod_eq_divMod [Div R] (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity)
    (hcancel : ∀ a : R,
      a - (a / plan.divisor.leadingCoeff) * plan.divisor.leadingCoeff = 0)
    (hexact : ∀ a : R,
      (a * plan.divisor.leadingCoeff) / plan.divisor.leadingCoeff = a)
    (h_top_ne : ∀ a : R, a ≠ 0 →
      a * plan.divisor.leadingCoeff ≠ 0) :
    plan.divMod p hcap = _root_.Hex.DensePoly.divMod p plan.divisor := by
  let q := plan.quotient p hcap
  let r := p - mulWith plan.mul q plan.divisor
  have hrec : q * plan.divisor + r = p := by
    apply ext_coeff
    intro i
    rw [coeff_add_semiring, coeff_sub_ring, mulWith_eq]
    grind
  have hdpos : 0 < plan.divisor.size := by
    apply Nat.pos_of_ne_zero
    intro hs
    exact plan.divisor_ne ((size_eq_zero_iff plan.divisor).mp hs)
  have heq : _root_.Hex.DensePoly.divMod p plan.divisor = (q, r) := by
    by_cases hdeg : 0 < plan.divisor.degree?.getD 0
    · exact divMod_eq_of_reconstruction p plan.divisor q r hdeg hcancel
        hexact h_top_ne hrec (plan.remainder_degree_lt p hcap hdeg)
    · have hddegree : plan.divisor.degree?.getD 0 =
          plan.divisor.size - 1 := by
        rw [degree?_eq_some_of_pos_size plan.divisor hdpos, Option.getD_some]
      have hdsize : plan.divisor.size = 1 := by omega
      have hrsize : r.size ≤ plan.divisor.size - 1 :=
        plan.remainder_size_le p hcap
      have hrzero : r = 0 := by
        apply (size_eq_zero_iff r).mp
        rw [hdsize] at hrsize
        omega
      have hmul : q * plan.divisor = p := by
        rw [hrzero, add_zero_poly] at hrec
        exact hrec
      simpa [hrzero] using
        (divMod_eq_of_polynomial_mul p plan.divisor q plan.divisor_ne
          hexact h_top_ne hmul)
  change (q, r) = _root_.Hex.DensePoly.divMod p plan.divisor
  exact heq.symm

/-- Remainder-only cached division. -/
def DivPlan.mod (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity) : DensePoly R :=
  (plan.divMod p hcap).2

/-- Reconstruction form of the cached remainder. -/
theorem DivPlan.mod_eq (plan : DivPlan R) (p : DensePoly R)
    (hcap : quotientLength p plan.divisor ≤ plan.capacity) :
    plan.mod p hcap =
      p - mulWith plan.mul (plan.quotient p hcap) plan.divisor := by
  rfl

/-- One-shot reciprocal division by a monic polynomial. -/
def divModMonicWith (mul : MulPlan R) (p q : DensePoly R) (hq : Monic q) :
    DensePoly R × DensePoly R :=
  if hqne : q = 0 then
    (0, p)
  else
    let k := quotientLength p q
    let plan := DivPlan.ofMonic mul q hq hqne k
    plan.divMod p (by
      dsimp [plan, DivPlan.ofMonic]
      exact Nat.le_refl k)

/-- One-shot monic reciprocal division agrees with the existing specialized
monic long-division operation. -/
theorem divModMonicWith_eq (mul : MulPlan R) (p q : DensePoly R)
    (hq : Monic q) :
    divModMonicWith mul p q hq = divModMonic p q hq := by
  unfold divModMonicWith
  split
  · rename_i hqzero
    subst q
    have hzero_one : (0 : R) = 1 := by
      simpa using (leadingCoeff_eq_one_of_monic hq)
    have hpzero : p = 0 := by
      apply ext_coeff
      intro i
      rw [coeff_zero]
      calc
        p.coeff i = p.coeff i * 1 := by grind
        _ = p.coeff i * 0 := by rw [hzero_one]
        _ = 0 := by grind
    subst p
    letI : Div R := ⟨fun a _ => a⟩
    have hnot_lt : ¬(0 : DensePoly R).degree?.getD 0 <
        (0 : DensePoly R).degree?.getD 0 := by omega
    rw [divModMonic_eq_divMod_of_monic_of_scale 0 0 hq hnot_lt
      (fun _ => rfl)]
    exact (divMod_eq_zero_self_of_size_zero 0 0 size_zero).symm
  · rename_i hqne
    let k := quotientLength p q
    let plan := DivPlan.ofMonic mul q hq hqne k
    letI : Div R := ⟨fun a _ => a⟩
    have hlead : q.leadingCoeff = 1 := leadingCoeff_eq_one_of_monic hq
    have hplan : plan.divMod p (by
        dsimp [plan, DivPlan.ofMonic]
        exact Nat.le_refl k) = _root_.Hex.DensePoly.divMod p q := by
      apply plan.divMod_eq_divMod
      · intro a
        change a - a * q.leadingCoeff = 0
        rw [hlead]
        grind
      · intro a
        change a * q.leadingCoeff = a
        rw [hlead]
        grind
      · intro a ha
        change a * q.leadingCoeff ≠ 0
        rw [hlead]
        simpa only [Lean.Grind.Semiring.mul_one] using ha
    by_cases hlt : p.degree?.getD 0 < q.degree?.getD 0
    · have hfast : _root_.Hex.DensePoly.divMod p q = (0, p) :=
        divMod_eq_zero_self_of_degree_lt p q hlt
      have hmonic : divModMonic p q hq = (0, p) := by
        unfold divModMonic
        exact divModArray_eq_zero_self_of_degree_lt p q id hlt
      rw [hplan, hfast, hmonic]
    · have hmonic := divModMonic_eq_divMod_of_monic_of_scale p q hq hlt
        (fun _ => rfl)
      exact hplan.trans hmonic.symm

/-- One-shot reciprocal division over a field. -/
def divModWith {F : Type u} [DecidableEq F] [Lean.Grind.Field F]
    (mul : MulPlan F) (p q : DensePoly F) : DensePoly F × DensePoly F :=
  if hqne : q = 0 then
    (0, p)
  else
    let k := quotientLength p q
    let plan := DivPlan.ofNonzero mul q hqne k
    plan.divMod p (by
      dsimp [plan, DivPlan.ofNonzero]
      exact Nat.le_refl k)

/-- One-shot field reciprocal division is extensionally the existing verified
long-division operation. -/
theorem divModWith_eq {F : Type u} [DecidableEq F] [Lean.Grind.Field F]
    (mul : MulPlan F) (p q : DensePoly F) :
    divModWith mul p q = _root_.Hex.DensePoly.divMod p q := by
  unfold divModWith
  split
  · rename_i hq
    have hqsize : q.size = 0 := (size_eq_zero_iff q).mpr hq
    exact (divMod_eq_zero_self_of_size_zero p q hqsize).symm
  · rename_i hqne
    let k := quotientLength p q
    let plan := DivPlan.ofNonzero mul q hqne k
    have hlead : q.leadingCoeff ≠ 0 := by
      apply leadingCoeff_ne_zero_of_pos_size q
      apply Nat.pos_of_ne_zero
      intro hs
      exact hqne ((size_eq_zero_iff q).mp hs)
    apply plan.divMod_eq_divMod
    · intro a
      change a - (a / q.leadingCoeff) * q.leadingCoeff = 0
      rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
        Lean.Grind.Field.inv_mul_cancel hlead, Lean.Grind.Semiring.mul_one]
      grind
    · intro a
      change (a * q.leadingCoeff) / q.leadingCoeff = a
      rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
        Lean.Grind.Field.mul_inv_cancel hlead, Lean.Grind.Semiring.mul_one]
    · intro a ha
      change a * q.leadingCoeff ≠ 0
      intro hz
      have hz' := congrArg (fun y : F => y * q.leadingCoeff⁻¹) hz
      rw [Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_assoc,
        Lean.Grind.Field.mul_inv_cancel hlead, Lean.Grind.Semiring.mul_one] at hz'
      exact ha hz'

end Hex.DensePoly
