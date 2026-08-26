/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.Kronecker

public section
set_option backward.proofsInPublic true

/-!
Multipoint Kronecker substitution for integer dense-polynomial products.

The two-, three-, and four-point kernels share signed base-`2 ^ b` recovery.
Keeping that recovery here makes the no-overlap obligation explicit for each
short packed product and prevents the kernels from acquiring subtly different
borrow conventions.
-/

namespace Hex

namespace ZPoly

/-! # Signed digit recovery -/

/-- Recover `slots` signed base-`2 ^ b` digits from a packed integer.

Every digit is biased by `2 ^ (b - 1)` before extraction.  If each true digit
lies strictly inside the signed half-range, the bias makes every extracted
digit nonnegative without allowing a carry into the next slot. -/
@[expose]
def signedUnpack (b : Nat) (packed : Int) (slots : Nat) : Array Int :=
  let bias : Int := ((2 ^ (b - 1) : Nat) : Int)
  (unpackAux b (packed + constPack b bias slots).toNat slots).map
    (fun d : Nat => (d : Int) - bias)

/-- Signed recovery inverts a packed range when every digit fits strictly in
the signed half-range. -/
theorem signedUnpack_packSpec (b slots : Nat) (f : Nat → Int)
    (hb : 0 < b) (hbudget : ∀ i, (f i).natAbs < 2 ^ (b - 1)) :
    signedUnpack b (packSpec b f slots) slots =
      ((List.range slots).map f).toArray := by
  have hcast : ∀ k, ((((f k + ((2 ^ (b - 1) : Nat) : Int)).toNat : Nat) : Int)
      = f k + ((2 ^ (b - 1) : Nat) : Int)) := by
    intro k
    have := hbudget k
    omega
  have hclt : ∀ k, (f k + ((2 ^ (b - 1) : Nat) : Int)).toNat < 2 ^ b := by
    intro k
    have hb1 : (2 : Nat) ^ b = 2 ^ (b - 1) + 2 ^ (b - 1) := by
      have hstep : (2 : Nat) ^ ((b - 1) + 1) = 2 ^ (b - 1) * 2 :=
        Nat.pow_succ 2 (b - 1)
      rw [show (b - 1) + 1 = b by omega] at hstep
      omega
    have h1 := hbudget k
    have h2 := hcast k
    omega
  have hdigits :
      (packSpec b f slots
          + constPack b ((2 ^ (b - 1) : Nat) : Int) slots).toNat =
        natEval b
          (fun k => (f k + ((2 ^ (b - 1) : Nat) : Int)).toNat) slots := by
    rw [constPack_eq, ← packSpec_add_fun]
    have hfun : (fun i => f i + ((2 ^ (b - 1) : Nat) : Int)) =
        (fun i => ((((f i + ((2 ^ (b - 1) : Nat) : Int)).toNat : Nat) : Int))) := by
      funext i
      rw [hcast i]
    rw [hfun, packSpec_natCast]
    exact Int.toNat_natCast _
  change (unpackAux b
      (packSpec b f slots + constPack b ((2 ^ (b - 1) : Nat) : Int) slots).toNat slots).map
        (fun d : Nat => (d : Int) - ((2 ^ (b - 1) : Nat) : Int)) = _
  rw [hdigits, unpackAux_natEval slots b _ hclt]
  apply Array.ext
  · simp
  · intro i hi₁ hi₂
    have hleft : (((List.range slots).map
        (fun k => (f k + ((2 ^ (b - 1) : Nat) : Int)).toNat)).toArray.map
          (fun d : Nat => (d : Int) - ((2 ^ (b - 1) : Nat) : Int)))[i] =
        ((((f i + ((2 ^ (b - 1) : Nat) : Int)).toNat : Nat) : Int)
          - ((2 ^ (b - 1) : Nat) : Int)) := by
      simp
    have hright : ((List.range slots).map f).toArray[i] = f i := by
      simp
    rw [hleft, hright, hcast i]
    omega

/-! # Evaluation at opposite points -/

/-- Horner evaluation of the first `len` values of `f` at an arbitrary
integer point.  `packSpec` is the specialization to `2 ^ b`. -/
@[expose]
def evalRange (x : Int) (f : Nat → Int) : Nat → Int
  | 0 => 0
  | len + 1 => f 0 + x * evalRange x (fun i => f (i + 1)) len

/-- `packSpec` is range evaluation at the positive power of two. -/
theorem evalRange_twoPow (b : Nat) (f : Nat → Int) :
    ∀ len, evalRange ((2 : Int) ^ b) f len = packSpec b f len := by
  intro len
  induction len generalizing f with
  | zero => rfl
  | succ len ih =>
      simp only [evalRange, packSpec]
      rw [ih]

private theorem evalRange_coeffList (x : Int) :
    ∀ (cs : List Int) (len : Nat), cs.length ≤ len →
      evalRange x (fun i => cs.getD i 0) len = DensePoly.evalCoeffList cs x := by
  intro cs
  induction cs with
  | nil =>
      intro len _
      have hzero : ∀ len, evalRange x (fun _ => (0 : Int)) len = 0 := by
        intro len
        induction len with
        | zero => rfl
        | succ len ih => simp [evalRange, ih]
      have hfun : (fun i => List.getD ([] : List Int) i 0) = (fun _ => (0 : Int)) := by
        funext i
        rfl
      rw [hfun, hzero]
      rfl
  | cons c cs ih =>
      intro len hlen
      match len with
      | 0 => simp at hlen
      | len + 1 =>
          have hlen' : cs.length ≤ len := by simpa using hlen
          show (List.getD (c :: cs) 0 0 : Int)
              + x * evalRange x (fun i => List.getD (c :: cs) (i + 1) 0) len = _
          have hshift : (fun i => List.getD (c :: cs) (i + 1) 0) =
              (fun i => cs.getD i 0) := by
            funext i
            rfl
          rw [hshift, ih len hlen']
          show c + x * DensePoly.evalCoeffList cs x =
            DensePoly.evalCoeffList cs x * x + c
          grind

/-- Range evaluation agrees with polynomial evaluation once the requested
range covers all stored coefficients. -/
theorem evalRange_coeff_eq_eval (x : Int) (p : ZPoly) (len : Nat)
    (hlen : p.size ≤ len) :
    evalRange x p.coeff len = DensePoly.eval p x := by
  have hcoeff : (fun i => p.toList.getD i 0) = p.coeff := by
    funext i
    by_cases hi : i < p.size
    · rw [List.getD_eq_getElem?_getD, DensePoly.toList]
      have hi' : i < p.toArray.size := by simpa using hi
      rw [Array.getElem?_toList, Array.getElem?_eq_getElem hi']
      show p.toArray[i] = p.coeff i
      rw [← DensePoly.toArray_getD p i]
      exact Array.getElem_eq_getD (Zero.zero : Int)
    · rw [List.getD_eq_getElem?_getD]
      have : p.toList.length ≤ i := by simpa using Nat.le_of_not_gt hi
      rw [List.getElem?_eq_none this]
      exact (DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hi)).symm
  rw [← hcoeff, evalRange_coeffList x p.toList len (by simpa using hlen)]
  rfl

/-- Alternate coefficient signs, so positive-base packing represents
evaluation at the corresponding negative base. -/
@[expose]
def alternate (f : Nat → Int) (i : Nat) : Int :=
  if i % 2 = 0 then f i else -f i

private theorem alternate_zero (f : Nat → Int) : alternate f 0 = f 0 := by
  simp [alternate]

private theorem alternate_succ (f : Nat → Int) (i : Nat) :
    alternate f (i + 1) = -alternate (fun j => f (j + 1)) i := by
  unfold alternate
  by_cases hi : i % 2 = 0
  · have his : (i + 1) % 2 ≠ 0 := by omega
    rw [ite_eq_left hi, ite_eq_right his]
  · have his : (i + 1) % 2 = 0 := by omega
    rw [ite_eq_right hi, ite_eq_left his]
    simp

private theorem evalRange_neg (x : Int) (f : Nat → Int) :
    ∀ len, evalRange x (fun i => -f i) len = -evalRange x f len := by
  intro len
  induction len generalizing f with
  | zero => rfl
  | succ len ih =>
      simp only [evalRange]
      rw [ih]
      grind

/-- Packing alternating coefficients at `B` is evaluation of the original
coefficient stream at `-B`. -/
theorem evalRange_alternate (x : Int) (f : Nat → Int) :
    ∀ len, evalRange x (alternate f) len = evalRange (-x) f len := by
  intro len
  induction len generalizing f with
  | zero => rfl
  | succ len ih =>
      simp only [evalRange, alternate_zero]
      have hshift : (fun i => alternate f (i + 1)) =
          (fun i => -alternate (fun j => f (j + 1)) i) := by
        funext i
        exact alternate_succ f i
      rw [hshift, evalRange_neg, ih]
      grind

/-- An even-length evaluation splits into its even and odd coefficient
streams, each evaluated at the squared point. -/
theorem evalRange_split (x : Int) (f : Nat → Int) :
    ∀ pairs,
      evalRange x f (2 * pairs) =
        evalRange (x * x) (fun i => f (2 * i)) pairs
          + x * evalRange (x * x) (fun i => f (2 * i + 1)) pairs := by
  intro pairs
  induction pairs generalizing f with
  | zero => simp [evalRange]
  | succ pairs ih =>
      rw [show 2 * (pairs + 1) = (2 * pairs) + 2 by omega]
      change f 0 + x * (f 1 + x * evalRange x (fun i => f (i + 2)) (2 * pairs)) = _
      rw [ih (fun i => f (i + 2))]
      simp only [evalRange]
      have heven : (fun i => f (2 * (i + 1))) = (fun i => f (i * 2 + 2)) := by
        funext i
        congr 1
        omega
      have hodd : (fun i => f (2 * (i + 1) + 1)) = (fun i => f (i * 2 + 3)) := by
        funext i
        congr 1
        omega
      rw [heven, hodd]
      grind

/-- Adding evaluations at opposite points isolates the even coefficient
stream. -/
theorem evalRange_add_neg (x : Int) (f : Nat → Int) (pairs : Nat) :
    evalRange x f (2 * pairs) + evalRange (-x) f (2 * pairs) =
      2 * evalRange (x * x) (fun i => f (2 * i)) pairs := by
  rw [evalRange_split, evalRange_split]
  have hsq : -x * -x = x * x := by grind
  rw [hsq]
  grind

/-- Subtracting evaluations at opposite points isolates the odd coefficient
stream, with one factor of the evaluation point. -/
theorem evalRange_sub_neg (x : Int) (f : Nat → Int) (pairs : Nat) :
    evalRange x f (2 * pairs) - evalRange (-x) f (2 * pairs) =
      (2 * x) * evalRange (x * x) (fun i => f (2 * i + 1)) pairs := by
  rw [evalRange_split, evalRange_split]
  have hsq : -x * -x = x * x := by grind
  rw [hsq]
  grind

/-- Alternating-sign balanced packing evaluates a polynomial at `-2 ^ b`. -/
theorem packAlternate_eq_eval (b : Nat) (p : ZPoly) :
    packAux b (alternate p.coeff) 0 p.size =
      DensePoly.eval p (-((2 : Int) ^ b)) := by
  rw [packAux_eq]
  simp only [Nat.zero_add]
  rw [← evalRange_twoPow, evalRange_alternate,
    evalRange_coeff_eq_eval _ p p.size (Nat.le_refl _)]

/-- Balanced positive packing evaluates a polynomial at `2 ^ b`. -/
theorem pack_eq_eval (b : Nat) (p : ZPoly) :
    packAux b p.coeff 0 p.size = DensePoly.eval p ((2 : Int) ^ b) := by
  rw [packAux_eq]
  simpa using packSpec_eq_eval b p p.size (Nat.le_refl _)

/-! # Parity-channel reconstruction -/

/-- Interleave equal-length even and odd coefficient channels, retaining only
the requested number of output slots. -/
@[expose]
def mergeParity (even odd : Array Int) (slots : Nat) : Array Int :=
  Array.ofFn (n := slots) fun i =>
    if i.1 % 2 = 0 then even.getD (i.1 / 2) 0 else odd.getD (i.1 / 2) 0

private theorem mergeParity_ranges (f : Nat → Int) (pairs slots : Nat)
    (hslots : slots ≤ 2 * pairs) :
    mergeParity
        ((List.range pairs).map (fun i => f (2 * i))).toArray
        ((List.range pairs).map (fun i => f (2 * i + 1))).toArray slots =
      ((List.range slots).map f).toArray := by
  apply Array.ext
  · simp [mergeParity]
  · intro i hi₁ hi₂
    unfold mergeParity at hi₁ ⊢
    rw [Array.getElem_ofFn]
    have hi : i < slots := by simpa using hi₁
    have hip : i / 2 < pairs := by omega
    have hright : ((List.range slots).map f).toArray[i] = f i := by
      simp
    rw [hright]
    by_cases heven : i % 2 = 0
    · rw [ite_eq_left heven]
      simp [hip]
      congr 1
      omega
    · rw [ite_eq_right heven]
      simp [hip]
      congr 1
      have hmod := Nat.mod_two_eq_zero_or_one i
      omega

/-! # Two-point Kronecker substitution -/

namespace KS2

/-- The two-point reconstruction at an explicit half-width and output shape.
The only large products are the evaluations at `2 ^ b` and `-2 ^ b`. -/
@[expose]
def recover (b pairs slots : Nat) (p q : ZPoly) : ZPoly :=
  let base : Int := (2 : Int) ^ b
  let pos := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
  let neg := packAux b (alternate p.coeff) 0 p.size *
    packAux b (alternate q.coeff) 0 q.size
  let even := signedUnpack (2 * b) ((pos + neg) / 2) pairs
  let odd := signedUnpack (2 * b) ((pos - neg) / (2 * base)) pairs
  DensePoly.ofCoeffs (mergeParity even odd slots)

/-- Two evaluations at opposite points recover the schoolbook product when
the doubled slots contain every signed coefficient. -/
theorem recover_eq (p q : ZPoly) (b pairs slots : Nat)
    (hb : 0 < b) (hsize : (p * q).size ≤ slots) (hslots : slots ≤ 2 * pairs)
    (hbudget : ∀ i, ((p * q).coeff i).natAbs < 2 ^ (2 * b - 1)) :
    recover b pairs slots p q = p * q := by
  let base : Int := (2 : Int) ^ b
  let pos := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
  let neg := packAux b (alternate p.coeff) 0 p.size *
    packAux b (alternate q.coeff) 0 q.size
  have hbase : base ≠ 0 := by
    unfold base
    exact Int.pow_ne_zero (by decide)
  have hpow : base * base = (2 : Int) ^ (2 * b) := by
    unfold base
    rw [← Int.pow_add]
    congr 2
    omega
  have hpos : pos = DensePoly.eval (p * q) base := by
    unfold pos base
    rw [pack_eq_eval, pack_eq_eval, DensePoly.eval_mul_commring]
  have hneg : neg = DensePoly.eval (p * q) (-base) := by
    unfold neg base
    rw [packAlternate_eq_eval, packAlternate_eq_eval, DensePoly.eval_mul_commring]
  have hcover : (p * q).size ≤ 2 * pairs := Nat.le_trans hsize hslots
  have hadd : pos + neg =
      2 * packSpec (2 * b) (fun i => (p * q).coeff (2 * i)) pairs := by
    rw [hpos, hneg,
      ← evalRange_coeff_eq_eval base (p * q) (2 * pairs) hcover,
      ← evalRange_coeff_eq_eval (-base) (p * q) (2 * pairs) hcover,
      evalRange_add_neg, hpow, evalRange_twoPow]
  have hsub : pos - neg =
      (2 * base) * packSpec (2 * b) (fun i => (p * q).coeff (2 * i + 1)) pairs := by
    rw [hpos, hneg,
      ← evalRange_coeff_eq_eval base (p * q) (2 * pairs) hcover,
      ← evalRange_coeff_eq_eval (-base) (p * q) (2 * pairs) hcover,
      evalRange_sub_neg, hpow, evalRange_twoPow]
  have heven : (pos + neg) / 2 =
      packSpec (2 * b) (fun i => (p * q).coeff (2 * i)) pairs := by
    rw [hadd]
    simpa only [Int.mul_comm] using Int.mul_ediv_cancel
      (packSpec (2 * b) (fun i => (p * q).coeff (2 * i)) pairs)
      (by decide : (2 : Int) ≠ 0)
  have hden : 2 * base ≠ 0 := Int.mul_ne_zero (by decide) hbase
  have hodd : (pos - neg) / (2 * base) =
      packSpec (2 * b) (fun i => (p * q).coeff (2 * i + 1)) pairs := by
    rw [hsub]
    simpa only [Int.mul_comm] using Int.mul_ediv_cancel
      (packSpec (2 * b) (fun i => (p * q).coeff (2 * i + 1)) pairs) hden
  unfold recover
  change DensePoly.ofCoeffs
      (mergeParity (signedUnpack (2 * b) ((pos + neg) / 2) pairs)
        (signedUnpack (2 * b) ((pos - neg) / (2 * base)) pairs) slots) = _
  rw [heven, hodd,
    signedUnpack_packSpec (2 * b) pairs _ (by omega)
      (fun i => hbudget (2 * i)),
    signedUnpack_packSpec (2 * b) pairs _ (by omega)
      (fun i => hbudget (2 * i + 1)),
    mergeParity_ranges _ pairs slots hslots]
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?]
  by_cases hi : i < slots
  · rw [Array.getElem?_eq_getElem (by simpa using hi), Option.getD_some]
    simp
  · rw [Array.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi), Option.getD_none]
    exact (DensePoly.coeff_eq_zero_of_size_le (p * q) (by omega)).symm

end KS2

/-! # Forced KS2 kernel -/

/-- The exact maximum product-coefficient budget used by the multipoint
kernels: diagonal length times the two separate coefficient maxima. -/
@[expose]
def coeffBudget (p q : ZPoly) : Nat :=
  min p.size q.size * (maxAbs p * maxAbs q)

/-- Half-width used by KS2.  Two adjacent result coefficients share a
`2 * ks2Width`-bit packed slot after the opposite-point evaluations are
combined. -/
@[expose]
def ks2Width (p q : ZPoly) : Nat :=
  (bitLen (coeffBudget p q) + 2) / 2

private theorem coeff_lt_ks2Range (p q : ZPoly) (i : Nat) :
    ((p * q).coeff i).natAbs < 2 ^ (2 * ks2Width p q - 1) := by
  have hcoeff := natAbs_mulCoeff_le_min p q (maxAbs p) (maxAbs q)
    (natAbs_coeff_le_maxAbs p) (natAbs_coeff_le_maxAbs q) i
  have hfit := lt_two_pow_bitLen (coeffBudget p q)
  have hexp : bitLen (coeffBudget p q) ≤ 2 * ks2Width p q - 1 := by
    unfold ks2Width
    omega
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (by simpa [coeffBudget] using hcoeff) hfit)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)

private theorem mul_eq_zero_of_isZero (p q : ZPoly)
    (h : p.isZero = true ∨ q.isZero = true) : p * q = 0 := by
  show DensePoly.mul p q = 0
  unfold DensePoly.mul
  rcases h with h | h <;> rw [ite_eq_left (by simp [h])]

/-- Forced two-point Kronecker substitution.  Every nonzero input uses exactly
the two packed integer products at `B` and `-B`; there is no size or width
fallback in this entry point. -/
@[expose]
def mulKS2 (p q : ZPoly) : ZPoly :=
  if p.isZero || q.isZero then 0
  else
    let slots := p.size + q.size - 1
    let pairs := (p.size + q.size) / 2
    KS2.recover (ks2Width p q) pairs slots p q

/-- Forced KS2 agrees with the schoolbook polynomial product. -/
theorem mulKS2_eq (p q : ZPoly) : mulKS2 p q = p * q := by
  unfold mulKS2
  by_cases hz : p.isZero || q.isZero
  · rw [ite_eq_left hz]
    exact (mul_eq_zero_of_isZero p q (by simpa using hz)).symm
  rw [ite_eq_right hz]
  have hnonzero := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hz)
  apply KS2.recover_eq
  · unfold ks2Width
    omega
  · exact DensePoly.size_mul_le p q
  · have hp : 0 < p.size := by
      exact (DensePoly.isZero_eq_false_iff p).mp hnonzero.1
    have hq : 0 < q.size := by
      exact (DensePoly.isZero_eq_false_iff q).mp hnonzero.2
    omega
  · exact coeff_lt_ks2Range p q

end ZPoly

end Hex
