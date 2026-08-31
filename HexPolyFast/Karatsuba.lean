/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Plan

public section

/-!
Splitting and algebraic assembly lemmas for Karatsuba multiplication.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- Coefficients strictly below `k`. -/
@[expose]
def low (k : Nat) (p : DensePoly R) : DensePoly R :=
  ofList ((List.range k).map p.coeff)

/-- Coefficients at and above `k`, shifted down by `k`. -/
@[expose]
def high (k : Nat) (p : DensePoly R) : DensePoly R :=
  ofList ((List.range (p.size - k)).map fun i => p.coeff (k + i))

/-- Coefficient law for the low half. -/
theorem coeff_low (k : Nat) (p : DensePoly R) (i : Nat) :
    (low k p).coeff i = if i < k then p.coeff i else 0 := by
  unfold low
  rw [coeff_ofList]
  by_cases hi : i < k
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Coefficient law for the shifted-down high half. -/
theorem coeff_high (k : Nat) (p : DensePoly R) (i : Nat) :
    (high k p).coeff i =
      if i < p.size - k then p.coeff (k + i) else 0 := by
  unfold high
  rw [coeff_ofList]
  by_cases hi : i < p.size - k
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Splitting at `k` and shifting the high half back reconstructs the input. -/
theorem low_add_shift_high (k : Nat) (p : DensePoly R) :
    low k p + shift k (high k p) = p := by
  apply ext_coeff
  intro i
  have hz : (0 : R) + 0 = 0 := by grind
  rw [coeff_add _ _ _ hz, coeff_low, coeff_shift]
  by_cases hik : i < k
  · rw [_root_.ite_eq_left hik, _root_.ite_eq_left hik]
    change p.coeff i + (0 : R) = p.coeff i
    exact Lean.Grind.Semiring.add_zero _
  · have hki : k ≤ i := Nat.le_of_not_gt hik
    rw [_root_.ite_eq_right hik, _root_.ite_eq_right hik]
    by_cases hip : i < p.size
    · have hh : i - k < p.size - k := by omega
      rw [coeff_high, _root_.ite_eq_left hh]
      have hidx : k + (i - k) = i := by omega
      rw [hidx]
      grind
    · have hsize : p.size ≤ i := Nat.le_of_not_gt hip
      have hh : ¬ i - k < p.size - k := by omega
      rw [coeff_high, _root_.ite_eq_right hh,
        coeff_eq_zero_of_size_le p hsize]
      exact hz

/-- Nested shifts add their offsets. -/
theorem shift_shift (k l : Nat) (p : DensePoly R) :
    shift k (shift l p) = shift (k + l) p := by
  apply ext_coeff
  intro i
  rw [coeff_shift, coeff_shift, coeff_shift]
  by_cases hi : i < k
  · have hil : i < k + l := by omega
    simp [hi, hil]
  · by_cases hil : i - k < l
    · have hisum : i < k + l := by omega
      simp [hi, hil, hisum]
    · have hisum : ¬ i < k + l := by omega
      have hidx : i - k - l = i - (k + l) := by omega
      simp [hi, hil, hisum, hidx]

/-- A shifted left factor shifts the product. -/
theorem shift_mul (k : Nat) (p q : DensePoly R) :
    shift k p * q = shift k (p * q) := by
  calc
    shift k p * q = (monomial k 1 * p) * q := by
      rw [monomial_one_mul_poly_eq_shift]
    _ = monomial k 1 * (p * q) := mul_assoc_poly _ _ _
    _ = shift k (p * q) := monomial_one_mul_poly_eq_shift _ _

/-- A shifted right factor shifts the product. -/
theorem mul_shift (k : Nat) (p q : DensePoly R) :
    p * shift k q = shift k (p * q) := by
  calc
    p * shift k q = shift k q * p := mul_comm_poly _ _
    _ = shift k (q * p) := shift_mul _ _ _
    _ = shift k (p * q) := congrArg (shift k) (mul_comm_poly q p)

/-- Multiplying two shifted polynomials adds their offsets. -/
theorem shift_mul_shift (k l : Nat) (p q : DensePoly R) :
    shift k p * shift l q = shift (k + l) (p * q) := by
  rw [shift_mul, mul_shift, shift_shift]

/-- The three-product Karatsuba assembly identity. -/
theorem karatsuba_combine (k : Nat) (a₀ a₁ b₀ b₁ : DensePoly R) :
    let z₀ := a₀ * b₀
    let z₂ := a₁ * b₁
    let z₁ := (a₀ + a₁) * (b₀ + b₁) - z₀ - z₂
    z₀ + shift k z₁ + shift (2 * k) z₂ =
      (a₀ + shift k a₁) * (b₀ + shift k b₁) := by
  dsimp
  rw [mul_add_right_poly (a₀ + a₁) b₀ b₁,
    mul_add_left_poly a₀ a₁ b₀,
    mul_add_left_poly a₀ a₁ b₁,
    mul_add_right_poly (a₀ + shift k a₁) b₀ (shift k b₁),
    mul_add_left_poly a₀ (shift k a₁) b₀,
    mul_add_left_poly a₀ (shift k a₁) (shift k b₁),
    shift_mul, mul_shift, shift_mul_shift]
  have hkk : k + k = 2 * k := by omega
  rw [hkk]
  apply ext_coeff
  intro i
  have hzadd : (0 : R) + 0 = 0 := by grind
  have hzsub : (0 : R) - 0 = 0 := by grind
  simp only [coeff_add _ _ _ hzadd, coeff_sub _ _ _ hzsub, coeff_shift]
  have hzero : (Zero.zero : R) = 0 := rfl
  simp only [hzero]
  split <;> split <;> grind

namespace Karatsuba.Raw

/-- Coefficientwise addition without polynomial normalization. -/
def add (a b : Array R) : Array R :=
  Array.ofFn (n := max a.size b.size) fun i =>
    a.getD i 0 + b.getD i 0

/-- Coefficientwise subtraction without polynomial normalization. -/
def sub (a b : Array R) : Array R :=
  Array.ofFn (n := max a.size b.size) fun i =>
    a.getD i 0 - b.getD i 0

/-- The raw coefficient prefix strictly below `k`. -/
def low (k : Nat) (a : Array R) : Array R :=
  Array.ofFn (n := min k a.size) fun i => a.getD i 0

/-- The raw coefficient suffix at `k`, shifted down. -/
def high (k : Nat) (a : Array R) : Array R :=
  Array.ofFn (n := a.size - k) fun i => a.getD (k + i) 0

/-- Assemble the three Karatsuba pieces in one output allocation. -/
def combine (k : Nat) (z₀ z₁ z₂ : Array R) : Array R :=
  Array.ofFn
    (n := max z₀.size (max (k + z₁.size) (2 * k + z₂.size))) fun i =>
      z₀.getD i 0 +
        (if k ≤ i then z₁.getD (i - k) 0 else 0) +
        if 2 * k ≤ i then z₂.getD (i - 2 * k) 0 else 0

/-- One schoolbook convolution diagonal over raw arrays. -/
def schoolbookCoeff (a b : Array R) (d : Nat) : R :=
  (List.range a.size).foldl
    (fun acc i =>
      if d < i then acc
      else if d - i < b.size then acc + a.getD i 0 * b.getD (d - i) 0
      else acc)
    0

/-- Raw schoolbook multiplication with no normalization pass. -/
def schoolbook (a b : Array R) : Array R :=
  if a.size = 0 || b.size = 0 then #[]
  else if a.size ≤ b.size then
    Array.ofFn (n := a.size + b.size - 1) fun i => schoolbookCoeff a b i
  else
    Array.ofFn (n := a.size + b.size - 1) fun i => schoolbookCoeff b a i

/-- Fuelled raw-array Karatsuba multiplication. -/
def mulAux (cutoff : Nat) : Nat → Array R → Array R → Array R
  | 0, a, b => schoolbook a b
  | fuel + 1, a, b =>
      if a.size ≤ max 1 cutoff || b.size ≤ max 1 cutoff then
        schoolbook a b
      else
        let k := (max a.size b.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let b₀ := low k b
        let b₁ := high k b
        let z₀ := mulAux cutoff fuel a₀ b₀
        let z₂ := mulAux cutoff fuel a₁ b₁
        let z₁ := sub (sub (mulAux cutoff fuel (add a₀ a₁) (add b₀ b₁)) z₀) z₂
        combine k z₀ z₁ z₂

/-- Fuelled raw-array specialized Karatsuba squaring. -/
def squareAux (cutoff : Nat) : Nat → Array R → Array R
  | 0, a => schoolbook a a
  | fuel + 1, a =>
      if a.size ≤ max 1 cutoff then
        schoolbook a a
      else
        let k := (a.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let z₀ := squareAux cutoff fuel a₀
        let z₂ := squareAux cutoff fuel a₁
        let z₁ := sub (sub (squareAux cutoff fuel (add a₀ a₁)) z₀) z₂
        combine k z₀ z₁ z₂

/-- Add a raw suffix at an offset in one output allocation. -/
def addShift (offset : Nat) (a b : Array R) : Array R :=
  Array.ofFn (n := max a.size (offset + b.size)) fun i =>
    a.getD i 0 + if offset ≤ i then b.getD (i - offset) 0 else 0

/-- Fuelled unbalanced block multiplication over raw arrays. -/
def blocks (cutoff blockSize : Nat) : Nat → Array R → Array R → Array R
  | 0, long, short => mulAux cutoff (max long.size short.size) long short
  | fuel + 1, long, short =>
      if long.size = 0 then #[]
      else
        addShift blockSize
          (mulAux cutoff (max (low blockSize long).size short.size)
            (low blockSize long) short)
          (blocks cutoff blockSize fuel (high blockSize long) short)

/-- A clipped raw schoolbook product. -/
def schoolbookSlice (lo len : Nat) (a b : Array R) : Array R :=
  if a.size = 0 || b.size = 0 then #[]
  else
    let used := min len (a.size + b.size - 1 - lo)
    if a.size ≤ b.size then
      Array.ofFn (n := used) fun i => schoolbookCoeff a b (lo + i)
    else
      Array.ofFn (n := used) fun i => schoolbookCoeff b a (lo + i)

/-- Fuelled interval-pruned Karatsuba recursion over raw arrays. -/
def sliceAux (cutoff : Nat) :
    Nat → Nat → Nat → Array R → Array R → Array R
  | 0, lo, len, a, b => schoolbookSlice lo len a b
  | fuel + 1, lo, len, a, b =>
      let used := min len (a.size + b.size - 1 - lo)
      if used = 0 then #[]
      else if a.size ≤ max 1 cutoff || b.size ≤ max 1 cutoff then
        schoolbookSlice lo used a b
      else
        let k := (max a.size b.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let b₀ := low k b
        let b₁ := high k b
        let hi := lo + used
        let base₀ := lo - k
        let base₁ := lo - k
        let base₂ := lo - 2 * k
        let z₀ := sliceAux cutoff fuel base₀ (hi - base₀) a₀ b₀
        let z₁ := sliceAux cutoff fuel base₁ ((hi - k) - base₁)
          (add a₀ a₁) (add b₀ b₁)
        let z₂ := sliceAux cutoff fuel base₂ ((hi - k) - base₂) a₁ b₁
        Array.ofFn (n := used) fun i =>
          let d := lo + i
          z₀.getD (d - base₀) 0 +
            (if k ≤ d then
              z₁.getD (d - k - base₁) 0 -
                z₀.getD (d - k - base₀) 0 -
                z₂.getD (d - k - base₂) 0
            else 0) +
            if 2 * k ≤ d then z₂.getD (d - 2 * k - base₂) 0 else 0

end Karatsuba.Raw

namespace Karatsuba.Raw

/-- Raw coefficientwise addition represents polynomial addition. -/
theorem ofCoeffs_add (a b : Array R) :
    (ofCoeffs (add a b) : DensePoly R) = ofCoeffs a + ofCoeffs b := by
  apply ext_coeff
  intro i
  have hz : (0 : R) + 0 = 0 := by grind
  rw [coeff_ofCoeffs, coeff_add _ _ _ hz, coeff_ofCoeffs, coeff_ofCoeffs]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  unfold add
  by_cases hi : i < max a.size b.size
  · simp [Array.getD, hi]
  · have ha : ¬i < a.size := by omega
    have hb : ¬i < b.size := by omega
    simp [Array.getD, hi, ha, hb]
    exact hz.symm

/-- Raw coefficientwise subtraction represents polynomial subtraction. -/
theorem ofCoeffs_sub (a b : Array R) :
    (ofCoeffs (sub a b) : DensePoly R) = ofCoeffs a - ofCoeffs b := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs, coeff_sub_ring, coeff_ofCoeffs, coeff_ofCoeffs]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  unfold sub
  by_cases hi : i < max a.size b.size
  · simp [Array.getD, hi]
  · have ha : ¬i < a.size := by omega
    have hb : ¬i < b.size := by omega
    simp [Array.getD, hi, ha, hb]
    change (0 : R) = 0 - 0
    grind

/-- A raw low split represents the polynomial low split. -/
theorem ofCoeffs_low (k : Nat) (a : Array R) :
    (ofCoeffs (low k a) : DensePoly R) = Hex.DensePoly.low k (ofCoeffs a) := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs, coeff_low, coeff_ofCoeffs]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  unfold low
  by_cases hik : i < k
  · rw [_root_.ite_eq_left hik]
    by_cases hia : i < a.size
    · have himin : i < min k a.size := by omega
      simp [Array.getD, himin, hia]
    · have himin : ¬i < min k a.size := by omega
      simp [Array.getD, himin, hia]
  · rw [_root_.ite_eq_right hik]
    have himin : ¬i < min k a.size := by omega
    simp [Array.getD, himin]

/-- A raw high split represents the polynomial shifted-down high split. -/
theorem ofCoeffs_high (k : Nat) (a : Array R) :
    (ofCoeffs (high k a) : DensePoly R) = Hex.DensePoly.high k (ofCoeffs a) := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs, coeff_high, coeff_ofCoeffs]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  unfold high
  have hsize : (ofCoeffs a : DensePoly R).size ≤ a.size := size_ofCoeffs_le a
  by_cases hip : i < (ofCoeffs a : DensePoly R).size - k
  · rw [_root_.ite_eq_left hip]
    have hiraw : i < a.size - k := by omega
    have hki : k + i < a.size := by omega
    simp [Array.getD, hiraw, hki]
  · rw [_root_.ite_eq_right hip]
    by_cases hiraw : i < a.size - k
    · have hbound : (ofCoeffs a : DensePoly R).size ≤ k + i := by omega
      have hz := coeff_eq_zero_of_size_le (ofCoeffs a : DensePoly R) hbound
      rw [coeff_ofCoeffs] at hz
      have hki : k + i < a.size := by omega
      have hzraw : a[k + i] = (Zero.zero : R) := by
        simpa [Array.getD, hki] using hz
      have hz' : a[k + i] = 0 := hzraw.trans hzero
      simp [Array.getD, hiraw, hki, hz']
    · simp [Array.getD, hiraw]

private theorem fold_schoolbook_extend (a b : Array R) (d extra : Nat) (acc : R) :
    (List.range ((ofCoeffs a : DensePoly R).size + extra)).foldl
        (fun acc i =>
          if d < i then acc
          else if d - i < b.size then acc + a.getD i 0 * b.getD (d - i) 0
          else acc)
        acc =
      (List.range (ofCoeffs a : DensePoly R).size).foldl
        (fun acc i =>
          if d < i then acc
          else if d - i < b.size then acc + a.getD i 0 * b.getD (d - i) 0
          else acc)
        acc := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hbound : (ofCoeffs a : DensePoly R).size ≤
          (ofCoeffs a : DensePoly R).size + extra := by omega
      have hazero := coeff_eq_zero_of_size_le (ofCoeffs a : DensePoly R) hbound
      rw [coeff_ofCoeffs] at hazero
      have hzero : (Zero.zero : R) = 0 := rfl
      have hazero' : a.getD ((ofCoeffs a : DensePoly R).size + extra) 0 = 0 := by
        simpa [hzero] using hazero
      by_cases hd : d < (ofCoeffs a : DensePoly R).size + extra
      · rw [_root_.ite_eq_left hd]
      · rw [_root_.ite_eq_right hd]
        by_cases hb : d - ((ofCoeffs a : DensePoly R).size + extra) < b.size
        · rw [_root_.ite_eq_left hb, hazero', Lean.Grind.Semiring.zero_mul,
            Lean.Grind.Semiring.add_zero]
        · rw [_root_.ite_eq_right hb]

/-- A raw diagonal fold represents the corresponding dense diagonal. -/
theorem schoolbookCoeff_eq_dense (a b : Array R) (d : Nat) :
    schoolbookCoeff a b d =
      Hex.DensePoly.schoolbookCoeff (ofCoeffs a) (ofCoeffs b) d := by
  unfold schoolbookCoeff Hex.DensePoly.schoolbookCoeff
  have hsize : (ofCoeffs a : DensePoly R).size ≤ a.size := size_ofCoeffs_le a
  have hsum : (ofCoeffs a : DensePoly R).size +
      (a.size - (ofCoeffs a : DensePoly R).size) = a.size := by omega
  rw [← hsum, fold_schoolbook_extend]
  have hbsize : (ofCoeffs b : DensePoly R).size ≤ b.size := size_ofCoeffs_le b
  have aux : ∀ (xs : List Nat) (acc : R),
      xs.foldl
          (fun acc i =>
            if d < i then acc
            else if d - i < b.size then acc + a.getD i 0 * b.getD (d - i) 0
            else acc)
          acc =
        xs.foldl
          (fun acc i =>
            if d < i then acc
            else if d - i < (ofCoeffs b : DensePoly R).size then
              acc + (ofCoeffs a : DensePoly R).coeff i *
                (ofCoeffs b : DensePoly R).coeff (d - i)
            else acc)
          acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        rw [List.foldl_cons, List.foldl_cons]
        by_cases hdi : d < i
        · rw [_root_.ite_eq_left hdi, _root_.ite_eq_left hdi]
          exact ih acc
        · rw [_root_.ite_eq_right hdi, _root_.ite_eq_right hdi]
          by_cases hq : d - i < (ofCoeffs b : DensePoly R).size
          · have hb : d - i < b.size := Nat.lt_of_lt_of_le hq hbsize
            rw [_root_.ite_eq_left hq, _root_.ite_eq_left hb,
              coeff_ofCoeffs, coeff_ofCoeffs]
            have hzero : (Zero.zero : R) = 0 := rfl
            rw [hzero]
            exact ih _
          · rw [_root_.ite_eq_right hq]
            by_cases hb : d - i < b.size
            · rw [_root_.ite_eq_left hb]
              have hz := coeff_eq_zero_of_size_le (ofCoeffs b : DensePoly R)
                (Nat.le_of_not_gt hq)
              rw [coeff_ofCoeffs] at hz
              have hzero : (Zero.zero : R) = 0 := rfl
              have hz' : b.getD (d - i) 0 = 0 := by simpa [hzero] using hz
              rw [hz', Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
              exact ih acc
            · rw [_root_.ite_eq_right hb]
              exact ih acc
  exact aux (List.range (ofCoeffs a : DensePoly R).size) 0

/-- Raw convolution diagonals are symmetric in their operands. -/
theorem schoolbookCoeff_comm (a b : Array R) (d : Nat) :
    schoolbookCoeff a b d = schoolbookCoeff b a d := by
  rw [schoolbookCoeff_eq_dense, schoolbookCoeff_eq_dense,
    schoolbookCoeff_eq_mulCoeffSum, schoolbookCoeff_eq_mulCoeffSum,
    ← coeff_mul, ← coeff_mul, mul_comm_poly]

/-- Raw schoolbook multiplication represents dense multiplication. -/
theorem ofCoeffs_schoolbook (a b : Array R) :
    (ofCoeffs (schoolbook a b) : DensePoly R) = ofCoeffs a * ofCoeffs b := by
  apply ext_coeff
  intro i
  rw [coeff_ofCoeffs]
  by_cases ha0 : a.size = 0
  · have hpa : (ofCoeffs a : DensePoly R) = 0 := by
      apply (size_eq_zero_iff (ofCoeffs a : DensePoly R)).mp
      exact Nat.le_antisymm (Nat.le_trans (size_ofCoeffs_le a) (by omega))
        (Nat.zero_le _)
    rw [hpa, zero_mul, coeff_zero]
    simp [schoolbook, ha0, Array.getD]
    rfl
  by_cases hb0 : b.size = 0
  · have hpb : (ofCoeffs b : DensePoly R) = 0 := by
      apply (size_eq_zero_iff (ofCoeffs b : DensePoly R)).mp
      exact Nat.le_antisymm (Nat.le_trans (size_ofCoeffs_le b) (by omega))
        (Nat.zero_le _)
    rw [hpb, mul_comm_poly, zero_mul, coeff_zero]
    simp [schoolbook, hb0, Array.getD]
    rfl
  · have ha : 0 < a.size := Nat.pos_of_ne_zero ha0
    have hb : 0 < b.size := Nat.pos_of_ne_zero hb0
    by_cases hi : i < a.size + b.size - 1
    · simp [schoolbook, ha0, hb0, Array.getD, hi, schoolbookCoeff_comm]
      rw [schoolbookCoeff_eq_dense, schoolbookCoeff_eq_mulCoeffSum]
      exact (coeff_mul (ofCoeffs a : DensePoly R) (ofCoeffs b : DensePoly R) i).symm
    · simp [schoolbook, ha0, hb0, Array.getD, hi, schoolbookCoeff_comm]
      have hpa : (ofCoeffs a : DensePoly R).size ≤ a.size := size_ofCoeffs_le a
      have hpb : (ofCoeffs b : DensePoly R).size ≤ b.size := size_ofCoeffs_le b
      by_cases hpzero : (ofCoeffs a : DensePoly R).size = 0
      · have hp : (ofCoeffs a : DensePoly R) = 0 :=
          (size_eq_zero_iff (ofCoeffs a : DensePoly R)).mp hpzero
        rw [hp, zero_mul, coeff_zero]
        rfl
      by_cases hqzero : (ofCoeffs b : DensePoly R).size = 0
      · have hq : (ofCoeffs b : DensePoly R) = 0 :=
          (size_eq_zero_iff (ofCoeffs b : DensePoly R)).mp hqzero
        rw [hq, mul_comm_poly, zero_mul, coeff_zero]
        rfl
      · have hsupp := size_mul_le (ofCoeffs a : DensePoly R) (ofCoeffs b : DensePoly R)
        have hsum : (ofCoeffs a : DensePoly R).size +
            (ofCoeffs b : DensePoly R).size ≤ a.size + b.size :=
          Nat.add_le_add hpa hpb
        have hsub := Nat.sub_le_sub_right hsum 1
        exact (coeff_eq_zero_of_size_le _
          (Nat.le_trans hsupp (Nat.le_trans hsub (Nat.le_of_not_gt hi)))).symm

/-- A raw clipped schoolbook product has the planned slice coefficients. -/
theorem coeff_ofCoeffs_schoolbookSlice (lo len : Nat) (a b : Array R) (i : Nat) :
    (ofCoeffs (schoolbookSlice lo len a b) : DensePoly R).coeff i =
      if i < len then (ofCoeffs a * ofCoeffs b).coeff (lo + i) else 0 := by
  rw [coeff_ofCoeffs]
  by_cases ha0 : a.size = 0
  · have hpa : (ofCoeffs a : DensePoly R) = 0 := by
      apply (size_eq_zero_iff (ofCoeffs a : DensePoly R)).mp
      exact Nat.le_antisymm (Nat.le_trans (size_ofCoeffs_le a) (by omega))
        (Nat.zero_le _)
    rw [hpa, zero_mul, coeff_zero]
    simp [schoolbookSlice, ha0, Array.getD]
    rfl
  by_cases hb0 : b.size = 0
  · have hpb : (ofCoeffs b : DensePoly R) = 0 := by
      apply (size_eq_zero_iff (ofCoeffs b : DensePoly R)).mp
      exact Nat.le_antisymm (Nat.le_trans (size_ofCoeffs_le b) (by omega))
        (Nat.zero_le _)
    rw [hpb, mul_comm_poly, zero_mul, coeff_zero]
    simp [schoolbookSlice, hb0, Array.getD]
    rfl
  · have ha : 0 < a.size := Nat.pos_of_ne_zero ha0
    have hb : 0 < b.size := Nat.pos_of_ne_zero hb0
    let used := min len (a.size + b.size - 1 - lo)
    by_cases hi : i < used
    · have hilen : i < len := Nat.lt_of_lt_of_le hi (Nat.min_le_left ..)
      rw [_root_.ite_eq_left hilen]
      simp [schoolbookSlice, ha0, hb0, used, Array.getD, hi,
        schoolbookCoeff_comm]
      rw [schoolbookCoeff_eq_dense, schoolbookCoeff_eq_mulCoeffSum]
      exact (coeff_mul (ofCoeffs a : DensePoly R) (ofCoeffs b : DensePoly R)
        (lo + i)).symm
    · simp [schoolbookSlice, ha0, hb0, used, Array.getD, hi,
        schoolbookCoeff_comm]
      by_cases hilen : i < len
      · rw [_root_.ite_eq_left hilen]
        have hraw : a.size + b.size - 1 ≤ lo + i := by
          dsimp [used] at hi
          omega
        have hpa : (ofCoeffs a : DensePoly R).size ≤ a.size := size_ofCoeffs_le a
        have hpb : (ofCoeffs b : DensePoly R).size ≤ b.size := size_ofCoeffs_le b
        by_cases hpzero : (ofCoeffs a : DensePoly R).size = 0
        · have hp : (ofCoeffs a : DensePoly R) = 0 :=
            (size_eq_zero_iff (ofCoeffs a : DensePoly R)).mp hpzero
          rw [hp, zero_mul, coeff_zero]
          rfl
        by_cases hqzero : (ofCoeffs b : DensePoly R).size = 0
        · have hq : (ofCoeffs b : DensePoly R) = 0 :=
            (size_eq_zero_iff (ofCoeffs b : DensePoly R)).mp hqzero
          rw [hq, mul_comm_poly, zero_mul, coeff_zero]
          rfl
        · have hsupp := size_mul_le
            (ofCoeffs a : DensePoly R) (ofCoeffs b : DensePoly R)
          have hsum : (ofCoeffs a : DensePoly R).size +
              (ofCoeffs b : DensePoly R).size ≤ a.size + b.size :=
            Nat.add_le_add hpa hpb
          have hsub := Nat.sub_le_sub_right hsum 1
          exact (coeff_eq_zero_of_size_le _
            (Nat.le_trans hsupp (Nat.le_trans hsub hraw))).symm
      · rw [_root_.ite_eq_right hilen]
        rfl

/-- Raw one-allocation assembly represents the Karatsuba shifted sum. -/
theorem ofCoeffs_combine (k : Nat) (z₀ z₁ z₂ : Array R) :
    (ofCoeffs (combine k z₀ z₁ z₂) : DensePoly R) =
      ofCoeffs z₀ + shift k (ofCoeffs z₁) + shift (2 * k) (ofCoeffs z₂) := by
  apply ext_coeff
  intro i
  have hz : (0 : R) + 0 = 0 := by grind
  rw [coeff_ofCoeffs, coeff_add _ _ _ hz, coeff_add _ _ _ hz,
    coeff_shift, coeff_shift, coeff_ofCoeffs, coeff_ofCoeffs, coeff_ofCoeffs]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  unfold combine
  let n := max z₀.size (max (k + z₁.size) (2 * k + z₂.size))
  by_cases hi : i < n
  · by_cases hk : k ≤ i
    · have hnk : ¬i < k := by omega
      by_cases h2k : 2 * k ≤ i
      · have hn2k : ¬i < 2 * k := by omega
        simp [Array.getD, n, hi, hk, hnk, h2k, hn2k]
      · have hi2k : i < 2 * k := by omega
        simp [Array.getD, n, hi, hk, hnk, h2k, hi2k]
    · have hik : i < k := by omega
      have h2k : ¬2 * k ≤ i := by omega
      have hi2k : i < 2 * k := by omega
      simp [Array.getD, n, hi, hk, hik, h2k, hi2k]
  · have hz₀ : ¬i < z₀.size := by dsimp [n] at hi; omega
    by_cases hk : k ≤ i
    · have hz₁ : ¬i - k < z₁.size := by dsimp [n] at hi; omega
      by_cases h2k : 2 * k ≤ i
      · have hz₂ : ¬i - 2 * k < z₂.size := by dsimp [n] at hi; omega
        simp [Array.getD, n, hi, hz₀, hz₁, hz₂]
        grind
      · simp [Array.getD, n, hi, hz₀, hz₁]
        grind
    · have h2k : ¬2 * k ≤ i := by omega
      simp [Array.getD, n, hi, hz₀]
      grind

/-- Raw shifted addition represents polynomial shifted addition. -/
theorem ofCoeffs_addShift (offset : Nat) (a b : Array R) :
    (ofCoeffs (addShift offset a b) : DensePoly R) =
      ofCoeffs a + shift offset (ofCoeffs b) := by
  apply ext_coeff
  intro i
  have hz : (0 : R) + 0 = 0 := by grind
  rw [coeff_ofCoeffs, coeff_add _ _ _ hz, coeff_shift,
    coeff_ofCoeffs, coeff_ofCoeffs]
  have hzero : (Zero.zero : R) = 0 := rfl
  rw [hzero]
  unfold addShift
  let n := max a.size (offset + b.size)
  by_cases hi : i < n
  · by_cases hoff : offset ≤ i
    · have hnot : ¬i < offset := by omega
      simp [Array.getD, n, hi, hoff, hnot]
    · have hlt : i < offset := by omega
      simp [Array.getD, n, hi, hoff, hlt]
  · have ha : ¬i < a.size := by dsimp [n] at hi; omega
    by_cases hoff : offset ≤ i
    · have hb : ¬i - offset < b.size := by dsimp [n] at hi; omega
      simp [Array.getD, n, hi, ha, hb]
      grind
    · have hlt : i < offset := by omega
      simp [Array.getD, n, hi, ha, hlt]
      grind

/-- Raw Karatsuba recursion represents dense multiplication for every fuel. -/
theorem ofCoeffs_mulAux (cutoff fuel : Nat) (a b : Array R) :
    (ofCoeffs (mulAux cutoff fuel a b) : DensePoly R) = ofCoeffs a * ofCoeffs b := by
  induction fuel generalizing a b with
  | zero => exact ofCoeffs_schoolbook a b
  | succ fuel ih =>
      rw [mulAux]
      split
      · exact ofCoeffs_schoolbook a b
      · dsimp only
        rw [ofCoeffs_combine, ofCoeffs_sub, ofCoeffs_sub,
          ih, ih, ih, ofCoeffs_add, ofCoeffs_add,
          ofCoeffs_low, ofCoeffs_high, ofCoeffs_low, ofCoeffs_high]
        rw [karatsuba_combine, low_add_shift_high, low_add_shift_high]

/-- Raw specialized Karatsuba squaring represents dense squaring for every fuel. -/
theorem ofCoeffs_squareAux (cutoff fuel : Nat) (a : Array R) :
    (ofCoeffs (squareAux cutoff fuel a) : DensePoly R) = ofCoeffs a * ofCoeffs a := by
  induction fuel generalizing a with
  | zero => exact ofCoeffs_schoolbook a a
  | succ fuel ih =>
      rw [squareAux]
      split
      · exact ofCoeffs_schoolbook a a
      · dsimp only
        rw [ofCoeffs_combine, ofCoeffs_sub, ofCoeffs_sub,
          ih, ih, ih, ofCoeffs_add, ofCoeffs_low, ofCoeffs_high]
        rw [karatsuba_combine, low_add_shift_high]

/-- Raw block recursion represents dense multiplication for every fuel. -/
theorem ofCoeffs_blocks (cutoff blockSize fuel : Nat) (long short : Array R) :
    (ofCoeffs (blocks cutoff blockSize fuel long short) : DensePoly R) =
      ofCoeffs long * ofCoeffs short := by
  induction fuel generalizing long with
  | zero => exact ofCoeffs_mulAux cutoff _ long short
  | succ fuel ih =>
      rw [blocks]
      split
      · rename_i hzero
        have hlong : (ofCoeffs long : DensePoly R) = 0 := by
          apply (size_eq_zero_iff (ofCoeffs long : DensePoly R)).mp
          exact Nat.le_antisymm (Nat.le_trans (size_ofCoeffs_le long) (by omega))
            (Nat.zero_le _)
        rw [hlong, zero_mul]
        rfl
      · rw [ofCoeffs_addShift, ofCoeffs_mulAux, ih,
          ofCoeffs_low, ofCoeffs_high, ← shift_mul,
          ← mul_add_left_poly, low_add_shift_high]

end Karatsuba.Raw

/-- Fuelled three-product Karatsuba recursion.  Fuel is separate from the
cutoff so cutoff zero remains total; public callers provide at least the
larger operand size. -/
@[expose]
def karatsubaAux (cutoff : Nat) : Nat → DensePoly R → DensePoly R → DensePoly R
  | 0, a, b => mulImpl a b
  | fuel + 1, a, b =>
      if a.size ≤ max 1 cutoff || b.size ≤ max 1 cutoff then
        mulImpl a b
      else
        let k := (max a.size b.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let b₀ := low k b
        let b₁ := high k b
        let z₀ := karatsubaAux cutoff fuel a₀ b₀
        let z₂ := karatsubaAux cutoff fuel a₁ b₁
        let z₁ := karatsubaAux cutoff fuel (a₀ + a₁) (b₀ + b₁) - z₀ - z₂
        z₀ + shift k z₁ + shift (2 * k) z₂

/-- Specialized three-square Karatsuba recursion. -/
@[expose]
def karatsubaSquareAux (cutoff : Nat) : Nat → DensePoly R → DensePoly R
  | 0, a => mulImpl a a
  | fuel + 1, a =>
      if a.size ≤ max 1 cutoff then
        mulImpl a a
      else
        let k := (a.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let z₀ := karatsubaSquareAux cutoff fuel a₀
        let z₂ := karatsubaSquareAux cutoff fuel a₁
        let z₁ := karatsubaSquareAux cutoff fuel (a₀ + a₁) - z₀ - z₂
        z₀ + shift k z₁ + shift (2 * k) z₂

/-- Every fuelled Karatsuba product agrees with schoolbook multiplication. -/
theorem karatsubaAux_eq (cutoff fuel : Nat) (a b : DensePoly R) :
    karatsubaAux cutoff fuel a b = a * b := by
  induction fuel generalizing a b with
  | zero =>
      exact (mul_eq_mulImpl a b).symm
  | succ fuel ih =>
      rw [karatsubaAux]
      split
      · exact (mul_eq_mulImpl a b).symm
      · dsimp only
        rw [ih, ih, ih]
        rw [karatsuba_combine]
        rw [low_add_shift_high, low_add_shift_high]

/-- Every fuelled Karatsuba square agrees with ordinary squaring. -/
theorem karatsubaSquareAux_eq (cutoff fuel : Nat) (a : DensePoly R) :
    karatsubaSquareAux cutoff fuel a = a * a := by
  induction fuel generalizing a with
  | zero =>
      exact (mul_eq_mulImpl a a).symm
  | succ fuel ih =>
      rw [karatsubaSquareAux]
      split
      · exact (mul_eq_mulImpl a a).symm
      · dsimp only
        rw [ih, ih, ih]
        rw [karatsuba_combine]
        rw [low_add_shift_high]

/-- Runtime Karatsuba recursion over raw coefficient arrays. The sole
normalization pass is the final `ofCoeffs`. -/
@[expose]
def karatsubaAuxImpl (cutoff fuel : Nat) (a b : DensePoly R) : DensePoly R :=
  ofCoeffs (Karatsuba.Raw.mulAux cutoff fuel a.toArray b.toArray)

/-- The raw-array Karatsuba runtime agrees with the proof-facing recursion. -/
theorem karatsubaAux_eq_impl (cutoff fuel : Nat) (a b : DensePoly R) :
    karatsubaAux cutoff fuel a b = karatsubaAuxImpl cutoff fuel a b := by
  rw [karatsubaAux_eq]
  unfold karatsubaAuxImpl
  rw [Karatsuba.Raw.ofCoeffs_mulAux, ofCoeffs_toArray, ofCoeffs_toArray]

/-- Compile fuelled Karatsuba through the raw-array recursion. -/
@[csimp]
theorem karatsubaAux_csimp : @karatsubaAux = @karatsubaAuxImpl := by
  funext R instDecEq instRing cutoff fuel a b
  exact karatsubaAux_eq_impl cutoff fuel a b

/-- Runtime specialized Karatsuba squaring over raw coefficient arrays. -/
@[expose]
def karatsubaSquareAuxImpl (cutoff fuel : Nat) (a : DensePoly R) : DensePoly R :=
  ofCoeffs (Karatsuba.Raw.squareAux cutoff fuel a.toArray)

/-- The raw-array square runtime agrees with the proof-facing recursion. -/
theorem karatsubaSquareAux_eq_impl (cutoff fuel : Nat) (a : DensePoly R) :
    karatsubaSquareAux cutoff fuel a = karatsubaSquareAuxImpl cutoff fuel a := by
  rw [karatsubaSquareAux_eq]
  unfold karatsubaSquareAuxImpl
  rw [Karatsuba.Raw.ofCoeffs_squareAux, ofCoeffs_toArray]

/-- Compile specialized Karatsuba squaring through the raw-array recursion. -/
@[csimp]
theorem karatsubaSquareAux_csimp : @karatsubaSquareAux = @karatsubaSquareAuxImpl := by
  funext R instDecEq instRing cutoff fuel a
  exact karatsubaSquareAux_eq_impl cutoff fuel a

/-- Balanced Karatsuba multiplication with an explicit schoolbook cutoff. -/
def mulKaratsubaBalanced (cutoff : Nat) (a b : DensePoly R) : DensePoly R :=
  karatsubaAux cutoff (max a.size b.size) a b

/-- Specialized Karatsuba squaring with an explicit schoolbook cutoff. -/
def squareKaratsuba (cutoff : Nat) (a : DensePoly R) : DensePoly R :=
  karatsubaSquareAux cutoff a.size a

/-- Balanced Karatsuba multiplication agrees exactly with `DensePoly.mul`. -/
theorem mulKaratsubaBalanced_eq (cutoff : Nat) (a b : DensePoly R) :
    mulKaratsubaBalanced cutoff a b = a * b :=
  karatsubaAux_eq cutoff _ a b

/-- Specialized Karatsuba squaring agrees exactly with `DensePoly.mul`. -/
theorem squareKaratsuba_eq (cutoff : Nat) (a : DensePoly R) :
    squareKaratsuba cutoff a = a * a :=
  karatsubaSquareAux_eq cutoff _ a

/-- Multiply a long operand by blocks of `blockSize` coefficients.  Each block
uses balanced Karatsuba; the shifted block products are accumulated without
padding the short operand to the long size. -/
@[expose]
def karatsubaBlocks (cutoff blockSize : Nat) :
    Nat → DensePoly R → DensePoly R → DensePoly R
  | 0, long, short => mulKaratsubaBalanced cutoff long short
  | fuel + 1, long, short =>
      if long.size = 0 then 0
      else
        mulKaratsubaBalanced cutoff (low blockSize long) short +
          shift blockSize
            (karatsubaBlocks cutoff blockSize fuel (high blockSize long) short)

/-- Blocked unbalanced multiplication agrees with the ordinary product for
every fuel value. -/
theorem karatsubaBlocks_eq (cutoff blockSize fuel : Nat)
    (long short : DensePoly R) :
    karatsubaBlocks cutoff blockSize fuel long short = long * short := by
  induction fuel generalizing long with
  | zero => exact mulKaratsubaBalanced_eq cutoff long short
  | succ fuel ih =>
      rw [karatsubaBlocks]
      split <;> rename_i hzero
      · have hlong : long = 0 := (size_eq_zero_iff long).mp hzero
        subst long
        exact (zero_mul short).symm
      · rw [mulKaratsubaBalanced_eq, ih, ← shift_mul,
          ← mul_add_left_poly, low_add_shift_high]

/-- Runtime unbalanced multiplication over raw coefficient arrays. -/
@[expose]
def karatsubaBlocksImpl (cutoff blockSize fuel : Nat)
    (long short : DensePoly R) : DensePoly R :=
  ofCoeffs
    (Karatsuba.Raw.blocks cutoff blockSize fuel long.toArray short.toArray)

/-- The raw-array block runtime agrees with the proof-facing recursion. -/
theorem karatsubaBlocks_eq_impl (cutoff blockSize fuel : Nat)
    (long short : DensePoly R) :
    karatsubaBlocks cutoff blockSize fuel long short =
      karatsubaBlocksImpl cutoff blockSize fuel long short := by
  rw [karatsubaBlocks_eq]
  unfold karatsubaBlocksImpl
  rw [Karatsuba.Raw.ofCoeffs_blocks, ofCoeffs_toArray, ofCoeffs_toArray]

/-- Compile unbalanced multiplication through the raw-array block recursion. -/
@[csimp]
theorem karatsubaBlocks_csimp : @karatsubaBlocks = @karatsubaBlocksImpl := by
  funext R instDecEq instRing cutoff blockSize fuel long short
  exact karatsubaBlocks_eq_impl cutoff blockSize fuel long short

/-- Full Karatsuba multiplication.  Strongly skewed operands are processed in
blocks near the shorter size rather than padded to the longer size. -/
def mulKaratsuba (cutoff : Nat) (a b : DensePoly R) : DensePoly R :=
  if a.size = 0 || b.size = 0 then
    mulImpl a b
  else if 2 * b.size < a.size then
    karatsubaBlocks cutoff b.size a.size a b
  else if 2 * a.size < b.size then
    karatsubaBlocks cutoff a.size b.size b a
  else
    mulKaratsubaBalanced cutoff a b

/-- Full balanced-or-blocked Karatsuba multiplication agrees exactly with
`DensePoly.mul`. -/
theorem mulKaratsuba_eq (cutoff : Nat) (a b : DensePoly R) :
    mulKaratsuba cutoff a b = a * b := by
  unfold mulKaratsuba
  split
  · exact (mul_eq_mulImpl a b).symm
  · split
    · exact karatsubaBlocks_eq cutoff b.size a.size a b
    · split
      · rw [karatsubaBlocks_eq, mul_comm_poly]
      · exact mulKaratsubaBalanced_eq cutoff a b

/-- Extract `len` coefficients beginning at `lo` from an already-computed
polynomial, shifting them down to degree zero. -/
@[expose]
def coeffSlice (lo len : Nat) (p : DensePoly R) : DensePoly R :=
  ofList ((List.range len).map fun i => p.coeff (lo + i))

/-- Coefficient law for extracting a polynomial interval. -/
theorem coeff_coeffSlice (lo len : Nat) (p : DensePoly R) (i : Nat) :
    (coeffSlice lo len p).coeff i =
      if i < len then p.coeff (lo + i) else 0 := by
  unfold coeffSlice
  rw [coeff_ofList]
  by_cases hi : i < len
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Truncating both inputs above `n` preserves every product coefficient
strictly below `n`. -/
theorem coeff_low_mul_low (n : Nat) (a b : DensePoly R) (i : Nat)
    (hi : i < n) :
    (low n a * low n b).coeff i = (a * b).coeff i := by
  have hdecomp :
      (low n a + shift n (high n a)) *
          (low n b + shift n (high n b)) = a * b := by
    rw [low_add_shift_high, low_add_shift_high]
  rw [← hdecomp]
  rw [mul_add_right_poly, mul_add_left_poly, mul_add_left_poly,
    shift_mul, mul_shift, shift_mul_shift]
  have hz : (0 : R) + 0 = 0 := by grind
  simp only [coeff_add _ _ _ hz, coeff_shift]
  have h2i : i < n + n := by omega
  have hzero : (Zero.zero : R) = 0 := rfl
  simp only [hzero]
  simp [hi, h2i]
  grind

/-- Fuelled interval-pruned Karatsuba recursion.  At a split, each of the
three mathematical subproducts is computed once over the smallest bounding
interval containing all of its shifted contributions to `[lo, lo + len)`.
Branches whose shifted output starts beyond the interval receive length zero. -/
@[expose]
def karatsubaSliceAux (cutoff : Nat) :
    Nat → Nat → Nat → DensePoly R → DensePoly R → DensePoly R
  | 0, lo, len, a, b => schoolbookSlice lo len a b
  | fuel + 1, lo, len, a, b =>
      let used := min len (a.size + b.size - 1 - lo)
      if used = 0 then
        0
      else if a.size ≤ max 1 cutoff || b.size ≤ max 1 cutoff then
        schoolbookSlice lo used a b
      else
        let k := (max a.size b.size + 1) / 2
        let a₀ := low k a
        let a₁ := high k a
        let b₀ := low k b
        let b₁ := high k b
        let hi := lo + used
        let base₀ := lo - k
        let base₁ := lo - k
        let base₂ := lo - 2 * k
        let z₀ := karatsubaSliceAux cutoff fuel base₀ (hi - base₀) a₀ b₀
        let z₁ := karatsubaSliceAux cutoff fuel base₁
          ((hi - k) - base₁) (a₀ + a₁) (b₀ + b₁)
        let z₂ := karatsubaSliceAux cutoff fuel base₂
          ((hi - k) - base₂) a₁ b₁
        ofList ((List.range used).map fun i =>
          let d := lo + i
          z₀.coeff (d - base₀) +
            (if k ≤ d then
              z₁.coeff (d - k - base₁) -
                z₀.coeff (d - k - base₀) -
                z₂.coeff (d - k - base₂)
            else 0) +
            if 2 * k ≤ d then z₂.coeff (d - 2 * k - base₂) else 0)

private theorem coeff_mul_zero_of_bounds (p q : DensePoly R)
    (pBound qBound d : Nat) (hp : p.size ≤ pBound) (hq : q.size ≤ qBound)
    (hd : pBound + qBound - 1 ≤ d) : (p * q).coeff d = 0 := by
  by_cases hpzero : p.size = 0
  · have hz : p = 0 := (size_eq_zero_iff p).mp hpzero
    rw [hz, zero_mul, coeff_zero]
  by_cases hqzero : q.size = 0
  · have hz : q = 0 := (size_eq_zero_iff q).mp hqzero
    rw [hz, mul_comm_poly, zero_mul, coeff_zero]
  · have hsupp := size_mul_le p q
    have hsum : p.size + q.size ≤ pBound + qBound := Nat.add_le_add hp hq
    have hsub := Nat.sub_le_sub_right hsum 1
    exact coeff_eq_zero_of_size_le _ (Nat.le_trans hsupp (Nat.le_trans hsub hd))

private theorem clipped_ite_eq (p q : DensePoly R) (pBound qBound lo len i : Nat)
    (hp : p.size ≤ pBound) (hq : q.size ≤ qBound) :
    (if i < min len (pBound + qBound - 1 - lo) then
        (p * q).coeff (lo + i) else 0) =
      if i < len then (p * q).coeff (lo + i) else 0 := by
  by_cases hilen : i < len
  · rw [_root_.ite_eq_left hilen]
    by_cases hiused : i < min len (pBound + qBound - 1 - lo)
    · rw [_root_.ite_eq_left hiused]
    · rw [_root_.ite_eq_right hiused]
      symm
      apply coeff_mul_zero_of_bounds p q pBound qBound (lo + i) hp hq
      omega
  · rw [_root_.ite_eq_right hilen]
    have hiused : ¬i < min len (pBound + qBound - 1 - lo) := by omega
    rw [_root_.ite_eq_right hiused]

/-- Every fuelled interval recursion returns exactly the requested product
coefficients. -/
theorem coeff_karatsubaSliceAux (cutoff fuel lo len : Nat)
    (a b : DensePoly R) (i : Nat) :
    (karatsubaSliceAux cutoff fuel lo len a b).coeff i =
      if i < len then (a * b).coeff (lo + i) else 0 := by
  induction fuel generalizing lo len a b i with
  | zero => exact coeff_schoolbookSlice lo len a b i
  | succ fuel ih =>
      rw [karatsubaSliceAux]
      let used := min len (a.size + b.size - 1 - lo)
      rw [← show used = min len (a.size + b.size - 1 - lo) from rfl]
      by_cases husedzero : used = 0
      · rw [_root_.ite_eq_left husedzero]
        simpa [used, husedzero] using
          clipped_ite_eq a b a.size b.size lo len i (by omega) (by omega)
      rw [_root_.ite_eq_right husedzero]
      split
      · rw [coeff_schoolbookSlice]
        exact clipped_ite_eq a b a.size b.size lo len i (by omega) (by omega)
      · dsimp only
        rw [coeff_ofList]
        rw [← clipped_ite_eq a b a.size b.size lo len i (by omega) (by omega)]
        by_cases hil : i < used
        · rw [List.getD_eq_getElem?_getD]
          simp only [List.getElem?_map, List.getElem?_range, hil,
            Option.map_some, Option.getD_some]
          let k := (max a.size b.size + 1) / 2
          let a₀ := low k a
          let a₁ := high k a
          let b₀ := low k b
          let b₁ := high k b
          let hi := lo + used
          let base₀ := lo - k
          let base₁ := lo - k
          let base₂ := lo - 2 * k
          have hprod :
              a₀ * b₀ + shift k
                  ((a₀ + a₁) * (b₀ + b₁) - a₀ * b₀ - a₁ * b₁) +
                    shift (2 * k) (a₁ * b₁) = a * b := by
            rw [karatsuba_combine]
            dsimp [a₀, a₁, b₀, b₁]
            rw [low_add_shift_high, low_add_shift_high]
          simp only [ih]
          have hc := congrArg (fun p : DensePoly R => p.coeff (lo + i)) hprod
          have hz : (0 : R) + 0 = 0 := by grind
          have hzs : (0 : R) - 0 = 0 := by grind
          simp only [coeff_add _ _ _ hz, coeff_sub _ _ _ hzs,
            coeff_shift] at hc
          have hzero : (Zero.zero : R) = 0 := rfl
          simp only [hzero] at hc
          have h₀ : lo + i - base₀ < hi - base₀ := by
            dsimp [hi, base₀]
            omega
          have he₀ : base₀ + (lo + i - base₀) = lo + i := by
            dsimp [base₀]
            omega
          rw [_root_.ite_eq_left h₀, he₀]
          by_cases hk : k ≤ lo + i
          · have h₁ : lo + i - k - base₁ < (hi - k) - base₁ := by
              dsimp [hi, base₁]
              omega
            have h₀' : lo + i - k - base₀ < hi - base₀ := by
              dsimp [hi, base₀]
              omega
            have h₂ : lo + i - k - base₂ < (hi - k) - base₂ := by
              dsimp [hi, base₂]
              omega
            have he₁ : base₁ + (lo + i - k - base₁) = lo + i - k := by
              dsimp [base₁]
              omega
            have he₀' : base₀ + (lo + i - k - base₀) = lo + i - k := by
              dsimp [base₀]
              omega
            have he₂ : base₂ + (lo + i - k - base₂) = lo + i - k := by
              dsimp [base₂]
              omega
            rw [_root_.ite_eq_left hk, _root_.ite_eq_left h₁,
              _root_.ite_eq_left h₀', _root_.ite_eq_left h₂]
            by_cases h2k : 2 * k ≤ lo + i
            · have h₂' : lo + i - 2 * k - base₂ < (hi - k) - base₂ := by
                dsimp [hi, base₂]
                omega
              have he₂' : base₂ + (lo + i - 2 * k - base₂) =
                  lo + i - 2 * k := by
                dsimp [base₂]
                omega
              rw [_root_.ite_eq_left h2k, _root_.ite_eq_left h₂', he₂']
              rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega)] at hc
              grind
            · rw [_root_.ite_eq_right h2k]
              rw [_root_.ite_eq_right (by omega), _root_.ite_eq_left (by omega)] at hc
              grind
          · have h2k : ¬2 * k ≤ lo + i := by omega
            rw [_root_.ite_eq_right hk, _root_.ite_eq_right h2k]
            rw [_root_.ite_eq_left (by omega), _root_.ite_eq_left (by omega)] at hc
            grind
        · have hlen :
              (List.map
                (fun i =>
                  let k := (max a.size b.size + 1) / 2
                  let a₀ := low k a
                  let a₁ := high k a
                  let b₀ := low k b
                  let b₁ := high k b
                  let hi := lo + used
                  let base₀ := lo - k
                  let base₁ := lo - k
                  let base₂ := lo - 2 * k
                  let z₀ := karatsubaSliceAux cutoff fuel base₀ (hi - base₀) a₀ b₀
                  let z₁ := karatsubaSliceAux cutoff fuel base₁
                    ((hi - k) - base₁) (a₀ + a₁) (b₀ + b₁)
                  let z₂ := karatsubaSliceAux cutoff fuel base₂
                    ((hi - k) - base₂) a₁ b₁
                  let d := lo + i
                  z₀.coeff (d - base₀) +
                    (if k ≤ d then
                      z₁.coeff (d - k - base₁) - z₀.coeff (d - k - base₀) -
                        z₂.coeff (d - k - base₂)
                    else 0) +
                    if 2 * k ≤ d then z₂.coeff (d - 2 * k - base₂) else 0)
                (List.range used)).length ≤ i := by simp; omega
          rw [List.getD_eq_getElem?_getD]
          simp [used, hil]
          rfl

/-- Raw interval recursion returns exactly the requested dense-product
coefficients for every fuel value. -/
theorem Karatsuba.Raw.coeff_ofCoeffs_sliceAux (cutoff fuel lo len : Nat)
    (a b : Array R) (i : Nat) :
    (ofCoeffs (Karatsuba.Raw.sliceAux cutoff fuel lo len a b) : DensePoly R).coeff i =
      if i < len then (ofCoeffs a * ofCoeffs b).coeff (lo + i) else 0 := by
  induction fuel generalizing lo len a b i with
  | zero => exact Karatsuba.Raw.coeff_ofCoeffs_schoolbookSlice lo len a b i
  | succ fuel ih =>
      rw [Karatsuba.Raw.sliceAux]
      let used := min len (a.size + b.size - 1 - lo)
      rw [← show used = min len (a.size + b.size - 1 - lo) from rfl]
      by_cases husedzero : used = 0
      · rw [_root_.ite_eq_left husedzero]
        rw [coeff_ofCoeffs]
        have hs := clipped_ite_eq (ofCoeffs a : DensePoly R)
          (ofCoeffs b : DensePoly R) a.size b.size lo len i
          (size_ofCoeffs_le a) (size_ofCoeffs_le b)
        have hiused : ¬i < min len (a.size + b.size - 1 - lo) := by
          rw [← show used = min len (a.size + b.size - 1 - lo) from rfl]
          omega
        rw [_root_.ite_eq_right hiused] at hs
        have hzero : (Zero.zero : R) = 0 := rfl
        rw [hzero]
        exact hs
      rw [_root_.ite_eq_right husedzero]
      split
      · rw [Karatsuba.Raw.coeff_ofCoeffs_schoolbookSlice]
        exact clipped_ite_eq (ofCoeffs a : DensePoly R) (ofCoeffs b : DensePoly R)
          a.size b.size lo len i (size_ofCoeffs_le a) (size_ofCoeffs_le b)
      · dsimp only
        rw [coeff_ofCoeffs]
        rw [← clipped_ite_eq (ofCoeffs a : DensePoly R) (ofCoeffs b : DensePoly R)
          a.size b.size lo len i (size_ofCoeffs_le a) (size_ofCoeffs_le b)]
        by_cases hil : i < used
        · rw [_root_.ite_eq_left hil]
          simp [Array.getD, hil]
          let k := (max a.size b.size + 1) / 2
          let ra₀ := Karatsuba.Raw.low k a
          let ra₁ := Karatsuba.Raw.high k a
          let rb₀ := Karatsuba.Raw.low k b
          let rb₁ := Karatsuba.Raw.high k b
          let a₀ : DensePoly R := ofCoeffs ra₀
          let a₁ : DensePoly R := ofCoeffs ra₁
          let b₀ : DensePoly R := ofCoeffs rb₀
          let b₁ : DensePoly R := ofCoeffs rb₁
          let hi := lo + used
          let base₀ := lo - k
          let base₁ := lo - k
          let base₂ := lo - 2 * k
          let z₀ := Karatsuba.Raw.sliceAux cutoff fuel base₀ (hi - base₀) ra₀ rb₀
          let z₁ := Karatsuba.Raw.sliceAux cutoff fuel base₁
            ((hi - k) - base₁) (Karatsuba.Raw.add ra₀ ra₁)
              (Karatsuba.Raw.add rb₀ rb₁)
          let z₂ := Karatsuba.Raw.sliceAux cutoff fuel base₂
            ((hi - k) - base₂) ra₁ rb₁
          change z₀.getD (lo + i - base₀) 0 +
              (if k ≤ lo + i then
                z₁.getD (lo + i - k - base₁) 0 -
                    z₀.getD (lo + i - k - base₀) 0 -
                  z₂.getD (lo + i - k - base₂) 0
              else 0) +
              (if 2 * k ≤ lo + i then
                z₂.getD (lo + i - 2 * k - base₂) 0 else 0) =
            (ofCoeffs a * ofCoeffs b).coeff (lo + i)
          have hcoeff (z : Array R) (j : Nat) :
              z.getD j 0 = (ofCoeffs z : DensePoly R).coeff j := by
            rw [coeff_ofCoeffs]
            rfl
          have hz₀spec (j : Nat) :
              (ofCoeffs z₀ : DensePoly R).coeff j =
                if j < hi - base₀ then (a₀ * b₀).coeff (base₀ + j) else 0 := by
            simpa [z₀, a₀, b₀] using ih base₀ (hi - base₀) ra₀ rb₀ j
          have hz₁spec (j : Nat) :
              (ofCoeffs z₁ : DensePoly R).coeff j =
                if j < (hi - k) - base₁ then
                  ((a₀ + a₁) * (b₀ + b₁)).coeff (base₁ + j) else 0 := by
            have h := ih base₁ ((hi - k) - base₁)
              (Karatsuba.Raw.add ra₀ ra₁) (Karatsuba.Raw.add rb₀ rb₁) j
            rw [Karatsuba.Raw.ofCoeffs_add, Karatsuba.Raw.ofCoeffs_add] at h
            simpa [z₁, a₀, a₁, b₀, b₁] using h
          have hz₂spec (j : Nat) :
              (ofCoeffs z₂ : DensePoly R).coeff j =
                if j < (hi - k) - base₂ then
                  (a₁ * b₁).coeff (base₂ + j) else 0 := by
            simpa [z₂, a₁, b₁] using
              ih base₂ ((hi - k) - base₂) ra₁ rb₁ j
          simp only [hcoeff, hz₀spec, hz₁spec, hz₂spec]
          have hprod :
              a₀ * b₀ + shift k
                  ((a₀ + a₁) * (b₀ + b₁) - a₀ * b₀ - a₁ * b₁) +
                    shift (2 * k) (a₁ * b₁) = ofCoeffs a * ofCoeffs b := by
            rw [karatsuba_combine]
            dsimp [a₀, a₁, b₀, b₁, ra₀, ra₁, rb₀, rb₁]
            rw [Karatsuba.Raw.ofCoeffs_low, Karatsuba.Raw.ofCoeffs_high,
              Karatsuba.Raw.ofCoeffs_low, Karatsuba.Raw.ofCoeffs_high,
              low_add_shift_high, low_add_shift_high]
          have hc := congrArg (fun p : DensePoly R => p.coeff (lo + i)) hprod
          have hz : (0 : R) + 0 = 0 := by grind
          have hzs : (0 : R) - 0 = 0 := by grind
          simp only [coeff_add _ _ _ hz, coeff_sub _ _ _ hzs,
            coeff_shift] at hc
          have hzero : (Zero.zero : R) = 0 := rfl
          simp only [hzero] at hc
          have h₀ : lo + i - base₀ < hi - base₀ := by
            dsimp [hi, base₀]
            omega
          have he₀ : base₀ + (lo + i - base₀) = lo + i := by
            dsimp [base₀]
            omega
          rw [_root_.ite_eq_left h₀, he₀]
          by_cases hk : k ≤ lo + i
          · have h₁ : lo + i - k - base₁ < (hi - k) - base₁ := by
              dsimp [hi, base₁]
              omega
            have h₀' : lo + i - k - base₀ < hi - base₀ := by
              dsimp [hi, base₀]
              omega
            have h₂ : lo + i - k - base₂ < (hi - k) - base₂ := by
              dsimp [hi, base₂]
              omega
            have he₁ : base₁ + (lo + i - k - base₁) = lo + i - k := by
              dsimp [base₁]
              omega
            have he₀' : base₀ + (lo + i - k - base₀) = lo + i - k := by
              dsimp [base₀]
              omega
            have he₂ : base₂ + (lo + i - k - base₂) = lo + i - k := by
              dsimp [base₂]
              omega
            rw [_root_.ite_eq_left hk, _root_.ite_eq_left h₁,
              _root_.ite_eq_left h₀', _root_.ite_eq_left h₂]
            by_cases h2k : 2 * k ≤ lo + i
            · have h₂' : lo + i - 2 * k - base₂ < (hi - k) - base₂ := by
                dsimp [hi, base₂]
                omega
              have he₂' : base₂ + (lo + i - 2 * k - base₂) =
                  lo + i - 2 * k := by
                dsimp [base₂]
                omega
              rw [_root_.ite_eq_left h2k, _root_.ite_eq_left h₂', he₂']
              rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega)] at hc
              grind
            · rw [_root_.ite_eq_right h2k]
              rw [_root_.ite_eq_right (by omega), _root_.ite_eq_left (by omega)] at hc
              grind
          · have h2k : ¬2 * k ≤ lo + i := by omega
            rw [_root_.ite_eq_right hk, _root_.ite_eq_right h2k]
            rw [_root_.ite_eq_left (by omega), _root_.ite_eq_left (by omega)] at hc
            grind
        · rw [_root_.ite_eq_right hil]
          simp [Array.getD, used, hil]
          rfl

/-- Runtime interval-pruned Karatsuba recursion over raw coefficient arrays. -/
@[expose]
def karatsubaSliceAuxImpl (cutoff fuel lo len : Nat)
    (a b : DensePoly R) : DensePoly R :=
  ofCoeffs
    (Karatsuba.Raw.sliceAux cutoff fuel lo len a.toArray b.toArray)

/-- The raw-array clipped runtime agrees with the proof-facing recursion. -/
theorem karatsubaSliceAux_eq_impl (cutoff fuel lo len : Nat)
    (a b : DensePoly R) :
    karatsubaSliceAux cutoff fuel lo len a b =
      karatsubaSliceAuxImpl cutoff fuel lo len a b := by
  apply ext_coeff
  intro i
  rw [coeff_karatsubaSliceAux]
  unfold karatsubaSliceAuxImpl
  rw [Karatsuba.Raw.coeff_ofCoeffs_sliceAux,
    ofCoeffs_toArray, ofCoeffs_toArray]

/-- Compile clipped Karatsuba through the raw-array interval recursion. -/
@[csimp]
theorem karatsubaSliceAux_csimp : @karatsubaSliceAux = @karatsubaSliceAuxImpl := by
  funext R instDecEq instRing cutoff fuel lo len a b
  exact karatsubaSliceAux_eq_impl cutoff fuel lo len a b

/-- Interval-pruned Karatsuba slicing. -/
def karatsubaSlice (cutoff lo len : Nat) (a b : DensePoly R) : DensePoly R :=
  karatsubaSliceAux cutoff (max a.size b.size) lo len a b

/-- Interval-pruned Karatsuba slicing has the exact planned-slice semantics. -/
theorem coeff_karatsubaSlice (cutoff lo len : Nat) (a b : DensePoly R)
    (i : Nat) :
    (karatsubaSlice cutoff lo len a b).coeff i =
      if i < len then (a * b).coeff (lo + i) else 0 :=
  coeff_karatsubaSliceAux cutoff _ lo len a b i

/-- A lawful Karatsuba plan. -/
def karatsubaPlan (cutoff : Nat) : MulPlan R where
  mul := mulKaratsuba cutoff
  square := squareKaratsuba cutoff
  slice := karatsubaSlice cutoff
  mul_eq := mulKaratsuba_eq cutoff
  square_eq := squareKaratsuba_eq cutoff
  coeff_slice := coeff_karatsubaSlice cutoff

end Hex.DensePoly
