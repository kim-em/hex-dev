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
Multipoint Kronecker substitution for integer polynomials.

The two-point kernel evaluates at `B` and `-B`.  Adding and subtracting the
two integer products separates the even and odd product coefficients, each
packed at base `B²`.  Consequently the two GMP multiplications have roughly
half the bit length of the one-point substitution.  Signed output streams use
the same explicit half-slot bias as the established KS1 kernel.
-/

namespace Hex
namespace ZPoly

private theorem foldl_add_natAbs_le_separate (f : Nat → Int) (B : Nat)
    (hf : ∀ i, (f i).natAbs ≤ B) : ∀ (l : List Nat) (acc : Int),
    (l.foldl (fun a i => a + f i) acc).natAbs ≤ acc.natAbs + l.length * B := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons i is ih =>
      intro acc
      have h1 := ih (acc + f i)
      have h2 : (acc + f i).natAbs ≤ acc.natAbs + B :=
        Nat.le_trans (Int.natAbs_add_le acc (f i))
          (Nat.add_le_add_left (hf i) _)
      have hd : (is.length + 1) * B = is.length * B + B := Nat.succ_mul _ _
      simp only [List.foldl_cons, List.length_cons]
      omega

private theorem natAbs_coeff_mul_le_left_separate (p q : ZPoly) (A C : Nat)
    (hp : ∀ i, (p.coeff i).natAbs ≤ A)
    (hq : ∀ j, (q.coeff j).natAbs ≤ C) (n : Nat) :
    ((p * q).coeff n).natAbs ≤ p.size * (A * C) := by
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_diagonal]
  have hterm : ∀ i,
      (DensePoly.diagonalMulCoeffTerm p q n i).natAbs ≤ A * C := by
    intro i
    unfold DensePoly.diagonalMulCoeffTerm
    by_cases hni : n < i
    · simp [hni]
    · rw [_root_.if_neg hni, Int.natAbs_mul]
      exact Nat.mul_le_mul (hp i) (hq (n - i))
  simpa using foldl_add_natAbs_le_separate
    (DensePoly.diagonalMulCoeffTerm p q n) (A * C) hterm
    (List.range p.size) 0

/-- Product coefficients are bounded using the two operands' separate maxima,
rather than the square of one shared maximum. -/
theorem natAbs_coeff_mul_le_separate (p q : ZPoly) (A C : Nat)
    (hp : ∀ i, (p.coeff i).natAbs ≤ A)
    (hq : ∀ j, (q.coeff j).natAbs ≤ C) (n : Nat) :
    ((p * q).coeff n).natAbs ≤ min p.size q.size * (A * C) := by
  have hleft := natAbs_coeff_mul_le_left_separate p q A C hp hq n
  have hright : ((p * q).coeff n).natAbs ≤ q.size * (A * C) := by
    rw [DensePoly.mul_comm_poly]
    have h := natAbs_coeff_mul_le_left_separate q p C A hq hp n
    rw [Nat.mul_comm C A] at h
    exact h
  by_cases hsize : p.size ≤ q.size
  · rw [Nat.min_eq_left hsize]
    exact hleft
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hsize)]
    exact hright

/-- Alternating-sign coefficient stream, used to evaluate at `-2^b` while
retaining the balanced positive-base packer. -/
@[inline]
def alternatingCoeff (p : ZPoly) (i : Nat) : Int :=
  if i % 2 = 0 then p.coeff i else -p.coeff i

private theorem packSpec_alternating (b : Nat) (f : Nat → Int) (s : Int) :
    ∀ len,
      packSpec b (fun i => s * (if i % 2 = 0 then f i else -f i)) len =
        s * DensePoly.evalCoeffList
          ((List.range len).map f) (-((2 : Int) ^ b)) := by
  intro len
  induction len generalizing f s with
  | zero =>
      change (0 : Int) = s * 0
      grind
  | succ len ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [DensePoly.evalCoeffList, packSpec, Nat.zero_mod, ↓reduceIte]
      have htail :
          (fun i => s * (if (i + 1) % 2 = 0 then f (i + 1) else -f (i + 1))) =
            (fun i => (-s) *
              (if i % 2 = 0 then f (i + 1) else -f (i + 1))) := by
        funext i
        rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
          simp [hi, Nat.add_mod] <;> grind
      rw [htail, ih (fun i => f (i + 1)) (-s)]
      have hmap :
          (List.range len).map (f ∘ Nat.succ) =
            (List.range len).map (fun i => f (i + 1)) := by
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
      rw [hmap]
      grind

/-- Alternating-sign packing is evaluation at the negated power of two. -/
theorem packAlternating_eq_eval (b : Nat) (p : ZPoly) :
    packAux b (alternatingCoeff p) 0 p.size =
      DensePoly.eval p (-((2 : Int) ^ b)) := by
  rw [packAux_eq]
  unfold alternatingCoeff
  have h := packSpec_alternating b p.coeff 1 p.size
  simp only [Int.one_mul] at h
  simp only [Nat.zero_add] at ⊢
  rw [h]
  unfold DensePoly.eval
  rw [DensePoly.toList_eq_coeff_range]

private theorem packSpec_even (b : Nat) (f : Nat → Int) : ∀ n,
    packSpec b f (2 * n) =
      packSpec (2 * b) (fun i => f (2 * i)) n +
        (2 : Int) ^ b * packSpec (2 * b) (fun i => f (2 * i + 1)) n := by
  intro n
  induction n generalizing f with
  | zero => simp [packSpec]
  | succ n ih =>
      change
        f 0 + 2 ^ b * (f 1 + 2 ^ b *
          packSpec b (fun i => f (i + 2)) (2 * n)) =
        (f 0 + 2 ^ (2 * b) *
          packSpec (2 * b) (fun i => f (2 * (i + 1))) n) +
        2 ^ b * (f 1 + 2 ^ (2 * b) *
          packSpec (2 * b) (fun i => f (2 * (i + 1) + 1)) n)
      rw [ih (fun i => f (i + 2))]
      have heven : (fun i => f (2 * i + 2)) =
          (fun i => f (2 * (i + 1))) := by
        funext i
        congr 1
      have hodd : (fun i => f (2 * i + 1 + 2)) =
          (fun i => f (2 * (i + 1) + 1)) := by
        funext i
        congr 1
      rw [heven, hodd]
      have hpow : (2 : Int) ^ (2 * b) = 2 ^ b * 2 ^ b := by
        rw [show 2 * b = b + b by omega, Int.pow_add]
      rw [hpow]
      grind

private theorem packSpec_odd (b : Nat) (f : Nat → Int) (n : Nat) :
    packSpec b f (2 * n + 1) =
      packSpec (2 * b) (fun i => f (2 * i)) (n + 1) +
        (2 : Int) ^ b * packSpec (2 * b) (fun i => f (2 * i + 1)) n := by
  change f 0 + 2 ^ b * packSpec b (fun i => f (i + 1)) (2 * n) =
    (f 0 + 2 ^ (2 * b) * packSpec (2 * b) (fun i => f (2 * (i + 1))) n) +
      2 ^ b * packSpec (2 * b) (fun i => f (2 * i + 1)) n
  rw [packSpec_even b (fun i => f (i + 1)) n]
  have heven : (fun i => f (2 * i + 1)) = (fun i => f (2 * i + 1)) := rfl
  have hodd : (fun i => f (2 * i + 1 + 1)) =
      (fun i => f (2 * (i + 1))) := by
    funext i
    congr 1
  rw [heven, hodd]
  have hpow : (2 : Int) ^ (2 * b) = 2 ^ b * 2 ^ b := by
    rw [show 2 * b = b + b by omega, Int.pow_add]
  rw [hpow]
  grind

/-- Split a packed coefficient stream into even and odd streams at the squared
base. -/
theorem packSpec_evenOdd (b : Nat) (f : Nat → Int) (len : Nat) :
    packSpec b f len =
      packSpec (2 * b) (fun i => f (2 * i)) ((len + 1) / 2) +
        (2 : Int) ^ b *
          packSpec (2 * b) (fun i => f (2 * i + 1)) (len / 2) := by
  rcases Nat.mod_two_eq_zero_or_one len with h | h
  · have heq : len = 2 * (len / 2) := by omega
    rw [heq]
    have hhalf1 : (2 * (len / 2) + 1) / 2 = len / 2 := by omega
    have hhalf2 : (2 * (len / 2)) / 2 = len / 2 := by omega
    rw [hhalf1, hhalf2]
    exact packSpec_even b f (len / 2)
  · have heq : len = 2 * (len / 2) + 1 := by omega
    rw [heq]
    have hhalf1 : (2 * (len / 2) + 1 + 1) / 2 = len / 2 + 1 := by omega
    have hhalf2 : (2 * (len / 2) + 1) / 2 = len / 2 := by omega
    rw [hhalf1, hhalf2]
    exact packSpec_odd b f (len / 2)

private theorem packSpec_zero (b len : Nat) :
    packSpec b (fun _ => (0 : Int)) len = 0 := by
  induction len with
  | zero => rfl
  | succ len ih =>
      simp only [packSpec, ih]
      grind

private theorem packSpec_neg (b : Nat) (f : Nat → Int) : ∀ len,
    packSpec b (fun i => -f i) len = -packSpec b f len := by
  intro len
  induction len generalizing f with
  | zero => rfl
  | succ len ih =>
      simp only [packSpec, ih]
      grind

/-- Alternating packing separates into the difference of the even stream and
the shifted odd stream. -/
theorem packSpec_alternating_evenOdd (b : Nat) (f : Nat → Int) (len : Nat) :
    packSpec b (fun i => if i % 2 = 0 then f i else -f i) len =
      packSpec (2 * b) (fun i => f (2 * i)) ((len + 1) / 2) -
        (2 : Int) ^ b *
          packSpec (2 * b) (fun i => f (2 * i + 1)) (len / 2) := by
  rw [packSpec_evenOdd]
  have heven : (fun i => if (2 * i) % 2 = 0 then f (2 * i) else -f (2 * i)) =
      (fun i => f (2 * i)) := by
    funext i
    simp
  have hodd : (fun i => if (2 * i + 1) % 2 = 0 then f (2 * i + 1)
      else -f (2 * i + 1)) = (fun i => -f (2 * i + 1)) := by
    funext i
    simp
  rw [heven, hodd, packSpec_neg]
  grind

private theorem packSpec_extend (b : Nat) (f : Nat → Int) (m n : Nat)
    (hmn : m ≤ n) (hz : ∀ i, m ≤ i → i < n → f i = 0) :
    packSpec b f n = packSpec b f m := by
  have hsum := packSpec_add b f m (n - m)
  rw [show m + (n - m) = n by omega] at hsum
  rw [hsum]
  have htail : packSpec b (fun i => f (m + i)) (n - m) = 0 := by
    have hzero : ∀ k lo, m ≤ lo → lo + k ≤ n →
        packSpec b (fun i => f (lo + i)) k = 0 := by
      intro k
      induction k with
      | zero => intro lo _ _; rfl
      | succ k ih =>
          intro lo hmlo hbound
          simp only [packSpec]
          simp only [Nat.add_zero]
          rw [hz lo hmlo (by omega)]
          have hfun : (fun i => f (lo + (i + 1))) =
              (fun i => f ((lo + 1) + i)) := by
            funext i
            congr 1
            omega
          rw [hfun, ih (lo + 1) (by omega) (by omega)]
          grind
    exact hzero (n - m) m (Nat.le_refl _) (by omega)
  rw [htail]
  grind

/-- Alternating packing may be padded with zero coefficient slots. -/
theorem packAlternatingSpec_eq_eval (b : Nat) (p : ZPoly) (len : Nat)
    (hsize : p.size ≤ len) :
    packSpec b (alternatingCoeff p) len =
      DensePoly.eval p (-((2 : Int) ^ b)) := by
  rw [packSpec_extend b (alternatingCoeff p) p.size len hsize (by
    intro i hi _
    unfold alternatingCoeff
    rw [DensePoly.coeff_eq_zero_of_size_le p hi]
    split <;> rfl)]
  have hp := packAlternating_eq_eval b p
  rw [packAux_eq] at hp
  simpa only [Nat.zero_add] using hp

/-- Coefficients at even indices. -/
@[expose]
def evenPart (p : ZPoly) : ZPoly :=
  DensePoly.ofList ((List.range ((p.size + 1) / 2)).map fun i => p.coeff (2 * i))

/-- Coefficients at odd indices. -/
@[expose]
def oddPart (p : ZPoly) : ZPoly :=
  DensePoly.ofList ((List.range (p.size / 2)).map fun i => p.coeff (2 * i + 1))

/-- Coefficient law for the even-index stream. -/
theorem coeff_evenPart (p : ZPoly) (i : Nat) :
    (evenPart p).coeff i = p.coeff (2 * i) := by
  unfold evenPart
  rw [DensePoly.coeff_ofList]
  by_cases hi : i < (p.size + 1) / 2
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi), Option.getD_none]
    rw [DensePoly.coeff_eq_zero_of_size_le p (by omega)]

/-- Coefficient law for the odd-index stream. -/
theorem coeff_oddPart (p : ZPoly) (i : Nat) :
    (oddPart p).coeff i = p.coeff (2 * i + 1) := by
  unfold oddPart
  rw [DensePoly.coeff_ofList]
  by_cases hi : i < p.size / 2
  · simp [List.getD, hi]
  · rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi), Option.getD_none]
    rw [DensePoly.coeff_eq_zero_of_size_le p (by omega)]

/-- Interleave even- and odd-index coefficient arrays. -/
@[expose]
def interleave (even odd : Array Int) (len : Nat) : Array Int :=
  (List.range len).map (fun i =>
    if i % 2 = 0 then even.getD (i / 2) 0 else odd.getD (i / 2) 0) |>.toArray

private theorem toArray_getD (l : List Int) (i : Nat) (d : Int) :
    l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

/-- Interleaving recovered even and odd streams reconstructs the source
polynomial. -/
theorem ofCoeffs_interleave (r : ZPoly) (even odd : Array Int) (len : Nat)
    (hsize : r.size ≤ len)
    (heven : DensePoly.ofCoeffs even = evenPart r)
    (hodd : DensePoly.ofCoeffs odd = oddPart r) :
    DensePoly.ofCoeffs (interleave even odd len) = r := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_ofCoeffs]
  unfold interleave
  rw [toArray_getD _ _ (Zero.zero : Int)]
  by_cases hi : i < len
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using hi), Option.getD_some]
    simp only [List.getElem_map, List.getElem_range]
    by_cases hip : i % 2 = 0
    · rw [_root_.ite_eq_left hip]
      have hcoeff := congrArg (fun p : ZPoly => p.coeff (i / 2)) heven
      rw [DensePoly.coeff_ofCoeffs, coeff_evenPart] at hcoeff
      change even.getD (i / 2) (Zero.zero : Int) = r.coeff i
      rw [hcoeff]
      congr 1
      omega
    · rw [_root_.ite_eq_right hip]
      have hcoeff := congrArg (fun p : ZPoly => p.coeff (i / 2)) hodd
      rw [DensePoly.coeff_ofCoeffs, coeff_oddPart] at hcoeff
      change odd.getD (i / 2) (Zero.zero : Int) = r.coeff i
      rw [hcoeff]
      congr 1
      omega
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi), Option.getD_none]
    exact (DensePoly.coeff_eq_zero_of_size_le r (by omega)).symm

/-- Recover a signed coefficient stream whose absolute values fit below the
half-slot boundary. -/
@[expose]
def unpackSigned (b : Nat) (packed : Int) (slots : Nat) : Array Int :=
  let bias : Int := (2 ^ (b - 1) : Nat)
  (unpackAux b (packed + constPack b bias slots).toNat slots).map
    (fun d : Nat => (d : Int) - bias)

/-- Signed digit recovery inverts a sufficiently wide packed coefficient
stream. -/
theorem unpackSigned_packSpec (r : ZPoly) (b slots : Nat)
    (hb : 0 < b) (hsize : r.size ≤ slots)
    (hbudget : ∀ n, (r.coeff n).natAbs < 2 ^ (b - 1)) :
    DensePoly.ofCoeffs (unpackSigned b (packSpec b r.coeff slots) slots) = r := by
  have h := kronecker_identity r (1 : ZPoly) b slots hb (by
    rw [DensePoly.mul_one_right_poly]
    exact hsize) (by
      intro n
      rw [DensePoly.mul_one_right_poly]
      exact hbudget n)
  have hr : packAux b r.coeff 0 r.size = packSpec b r.coeff slots := by
    rw [packAux_eq]
    simp only [Nat.zero_add]
    rw [packSpec_eq_eval b r r.size (Nat.le_refl _),
      packSpec_eq_eval b r slots hsize]
  have hone : packAux b (1 : ZPoly).coeff 0 (1 : ZPoly).size = 1 := by
    rw [packAux_eq]
    simp only [Nat.zero_add]
    rw [packSpec_eq_eval b (1 : ZPoly) (1 : ZPoly).size
      (Nat.le_refl _)]
    change DensePoly.eval (DensePoly.C 1) ((2 : Int) ^ b) = 1
    rw [DensePoly.eval_C_semiring]
  rw [hr, hone, Int.mul_one] at h
  rw [DensePoly.mul_one_right_poly] at h
  simpa only [unpackSigned] using h

private theorem packProduct_eq (p q : ZPoly) (b slots : Nat)
    (hsize : (p * q).size ≤ slots) :
    packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size =
      packSpec b (p * q).coeff slots := by
  rw [packAux_eq, packAux_eq]
  simp only [Nat.zero_add]
  rw [packSpec_eq_eval b p p.size (Nat.le_refl _),
    packSpec_eq_eval b q q.size (Nat.le_refl _),
    ← DensePoly.eval_mul_commring,
    packSpec_eq_eval b (p * q) slots hsize]

private theorem packAlternatingProduct_eq (p q : ZPoly) (b slots : Nat)
    (hsize : (p * q).size ≤ slots) :
    packAux b (alternatingCoeff p) 0 p.size *
        packAux b (alternatingCoeff q) 0 q.size =
      packSpec b (alternatingCoeff (p * q)) slots := by
  rw [packAlternating_eq_eval, packAlternating_eq_eval,
    ← DensePoly.eval_mul_commring,
    packAlternatingSpec_eq_eval b (p * q) slots hsize]

/-- Two-point Kronecker substitution identity at an explicit half-slot width.
The hypotheses expose exactly the signed no-overlap obligation. -/
theorem kronecker2_identity (p q : ZPoly) (b slots : Nat)
    (hb : 0 < b) (hsize : (p * q).size ≤ slots)
    (hbudget : ∀ n, ((p * q).coeff n).natAbs < 2 ^ (2 * b - 1)) :
    let plus := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
    let minus := packAux b (alternatingCoeff p) 0 p.size *
      packAux b (alternatingCoeff q) 0 q.size
    DensePoly.ofCoeffs (interleave
      (unpackSigned (2 * b) ((plus + minus) / 2) ((slots + 1) / 2))
      (unpackSigned (2 * b) ((plus - minus) / (2 ^ (b + 1) : Nat))
        (slots / 2)) slots) = p * q := by
  dsimp only
  let r := p * q
  let evenSlots := (slots + 1) / 2
  let oddSlots := slots / 2
  let evenPacked := packSpec (2 * b) (evenPart r).coeff evenSlots
  let oddPacked := packSpec (2 * b) (oddPart r).coeff oddSlots
  have hplus := packProduct_eq p q b slots hsize
  rw [packSpec_evenOdd] at hplus
  have hevenFun : (fun i => r.coeff (2 * i)) = (evenPart r).coeff := by
    funext i
    exact (coeff_evenPart r i).symm
  have hoddFun : (fun i => r.coeff (2 * i + 1)) = (oddPart r).coeff := by
    funext i
    exact (coeff_oddPart r i).symm
  change _ = packSpec (2 * b) (fun i => r.coeff (2 * i)) evenSlots +
    (2 : Int) ^ b * packSpec (2 * b) (fun i => r.coeff (2 * i + 1)) oddSlots at hplus
  rw [hevenFun, hoddFun] at hplus
  change _ = evenPacked + (2 : Int) ^ b * oddPacked at hplus
  have hminus := packAlternatingProduct_eq p q b slots hsize
  change packAux b (alternatingCoeff p) 0 p.size *
      packAux b (alternatingCoeff q) 0 q.size =
    packSpec b (fun i => if i % 2 = 0 then r.coeff i else -r.coeff i) slots at hminus
  rw [packSpec_alternating_evenOdd] at hminus
  change _ = packSpec (2 * b) (fun i => r.coeff (2 * i)) evenSlots -
    (2 : Int) ^ b * packSpec (2 * b) (fun i => r.coeff (2 * i + 1)) oddSlots at hminus
  rw [hevenFun, hoddFun] at hminus
  change _ = evenPacked - (2 : Int) ^ b * oddPacked at hminus
  have hevenPacked :
      (packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size +
        packAux b (alternatingCoeff p) 0 p.size *
          packAux b (alternatingCoeff q) 0 q.size) / 2 = evenPacked := by
    apply Int.ediv_eq_of_eq_mul_right (by omega)
    grind
  have hden : ((2 ^ (b + 1) : Nat) : Int) = 2 * (2 : Int) ^ b := by
    rw [Nat.pow_succ]
    push_cast
    grind
  have hoddPacked :
      (packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size -
        packAux b (alternatingCoeff p) 0 p.size *
          packAux b (alternatingCoeff q) 0 q.size) /
          (2 ^ (b + 1) : Nat) = oddPacked := by
    apply Int.ediv_eq_of_eq_mul_right (by
      rw [hden]
      have : (0 : Int) < 2 ^ b := Int.pow_pos (by omega)
      omega)
    rw [hden]
    grind
  rw [hevenPacked, hoddPacked]
  apply ofCoeffs_interleave r _ _ slots hsize
  · apply unpackSigned_packSpec (evenPart r) (2 * b) evenSlots (by omega)
    · unfold evenPart evenSlots
      refine Nat.le_trans (DensePoly.size_ofList_le _) ?_
      simpa only [List.length_map, List.length_range] using
        (Nat.div_le_div_right (Nat.add_le_add_right hsize 1) :
          (r.size + 1) / 2 ≤ (slots + 1) / 2)
    · intro n
      rw [coeff_evenPart]
      exact hbudget (2 * n)
  · apply unpackSigned_packSpec (oddPart r) (2 * b) oddSlots (by omega)
    · unfold oddPart oddSlots
      refine Nat.le_trans (DensePoly.size_ofList_le _) ?_
      simpa only [List.length_map, List.length_range] using
        (Nat.div_le_div_right hsize : r.size / 2 ≤ slots / 2)
    · intro n
      rw [coeff_oddPart]
      exact hbudget (2 * n + 1)

/-- KS2 with no dispatcher guard.  It performs exactly two multiplications of
packed integers; callers use this forced surface for conformance and crossover
measurement. -/
@[expose]
def mulKronecker2 (p q : ZPoly) : ZPoly :=
  if p.isZero || q.isZero then 0
  else
    let terms := min p.size q.size
    let bound := terms * (maxAbs p * maxAbs q)
    let productBits := bitLen bound + 2
    let b := (productBits + 1) / 2
    let slots := p.size + q.size - 1
    let plus := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
    let minus := packAux b (alternatingCoeff p) 0 p.size *
      packAux b (alternatingCoeff q) 0 q.size
    let evenPacked := (plus + minus) / 2
    let oddPacked := (plus - minus) / (2 ^ (b + 1) : Nat)
    let slotBits := 2 * b
    DensePoly.ofCoeffs (interleave
      (unpackSigned slotBits evenPacked ((slots + 1) / 2))
      (unpackSigned slotBits oddPacked (slots / 2)) slots)

/-- The forced two-point kernel computes the ordinary dense product. -/
theorem mulKronecker2_eq (p q : ZPoly) : mulKronecker2 p q = p * q := by
  unfold mulKronecker2
  by_cases hz : p.isZero || q.isZero
  · rw [_root_.ite_eq_left hz]
    have h := mulKroneckerAt_eq 0 0 p q
    unfold mulKroneckerAt at h
    rw [_root_.ite_eq_left hz] at h
    exact h
  · rw [_root_.ite_eq_right hz]
    let terms := min p.size q.size
    let bound := terms * (maxAbs p * maxAbs q)
    let productBits := bitLen bound + 2
    let b := (productBits + 1) / 2
    let slots := p.size + q.size - 1
    apply kronecker2_identity p q b slots
    · dsimp [b, productBits]
      omega
    · exact DensePoly.size_mul_le p q
    · intro n
      have hcoeff := natAbs_coeff_mul_le_separate p q (maxAbs p) (maxAbs q)
        (natAbs_coeff_le_maxAbs p) (natAbs_coeff_le_maxAbs q) n
      have hfit := lt_two_pow_bitLen bound
      have hbound : min p.size q.size * (maxAbs p * maxAbs q) = bound := rfl
      rw [hbound] at hcoeff
      have hexp : bitLen bound ≤ 2 * b - 1 := by
        dsimp [b, productBits]
        omega
      exact Nat.lt_of_le_of_lt hcoeff
        (Nat.lt_of_lt_of_le hfit (Nat.pow_le_pow_right (by decide : 0 < 2) hexp))

/-! # Reciprocal two-product substitution -/

private theorem foldAdd_right (xs : List Int) (a d : Int) :
    xs.foldl (fun acc x => acc + x) (a + d) =
      xs.foldl (fun acc x => acc + x) a + d := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [show a + d + x = (a + x) + d by omega, ih]

private theorem foldAdd_reverse (xs : List Int) (a : Int) :
    xs.reverse.foldl (fun acc x => acc + x) a =
      xs.foldl (fun acc x => acc + x) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, foldAdd_right]

private theorem foldAdd_map {α : Type} (xs : List α) (f : α → Int) (a : Int) :
    xs.foldl (fun acc x => acc + f x) a =
      (xs.map f).foldl (fun acc x => acc + x) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      exact ih (a + f x)

private theorem range_reverse_eq (n : Nat) :
    (List.range n).reverse = (List.range n).map (fun i => n - 1 - i) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.length_reverse] at hleft hright
    rw [List.getElem_reverse]
    simp [List.getElem_map, List.getElem_range]

/-- A fixed-length coefficient reversal.  Normalization may shorten its stored
array, but its coefficient law retains the explicit length. -/
private def reverseFixed (p : ZPoly) (len : Nat) : ZPoly :=
  DensePoly.ofList ((List.range len).map fun i => p.coeff (len - 1 - i))

private theorem coeff_reverseFixed (p : ZPoly) (len i : Nat) :
    (reverseFixed p len).coeff i =
      if i < len then p.coeff (len - 1 - i) else 0 := by
  unfold reverseFixed
  rw [DensePoly.coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < len
  · rw [List.getElem?_range hi]
    simp [hi]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
    simp [hi]
    change (0 : Int) = 0
    rfl

private theorem coeff_mul_extended (a b : ZPoly) (m k : Nat) (ha : a.size ≤ m) :
    (a * b).coeff k =
      (List.range m).foldl
        (fun acc i => acc + DensePoly.diagonalMulCoeffTerm a b k i) 0 := by
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_diagonal]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [List.range_add, List.foldl_append]
  suffices hzero : ∀ (xs : List Nat) (acc : Int),
      (∀ i, i ∈ xs → a.size ≤ i) →
      xs.foldl (fun total i => total + DensePoly.diagonalMulCoeffTerm a b k i) acc = acc by
    exact (hzero _ _ (by
      intro i hi
      simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      omega)).symm
  intro xs acc hx
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hai : a.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le a (hx i (by simp))
      have hterm : DensePoly.diagonalMulCoeffTerm a b k i = 0 := by
        unfold DensePoly.diagonalMulCoeffTerm
        split <;> simp [hai]
      rw [hterm, Int.add_zero]
      exact ih acc (by intro j hj; exact hx j (by simp [hj]))

private theorem reverseFixed_mul (p q : ZPoly) (hp : 0 < p.size) (hq : 0 < q.size) :
    reverseFixed p p.size * reverseFixed q q.size =
      reverseFixed (p * q) (p.size + q.size - 1) := by
  apply DensePoly.ext_coeff
  intro k
  let slots := p.size + q.size - 1
  rw [coeff_mul_extended _ _ p.size k (by
    unfold reverseFixed
    exact Nat.le_trans (DensePoly.size_ofList_le _) (by simp))]
  rw [coeff_reverseFixed]
  by_cases hk : k < slots
  · rw [_root_.ite_eq_left hk]
    rw [coeff_mul_extended p q p.size (slots - 1 - k) (Nat.le_refl _)]
    have hterm : ∀ i, i < p.size →
        DensePoly.diagonalMulCoeffTerm (reverseFixed p p.size)
            (reverseFixed q q.size) k i =
          DensePoly.diagonalMulCoeffTerm p q (slots - 1 - k)
            (p.size - 1 - i) := by
      intro i hi
      unfold DensePoly.diagonalMulCoeffTerm
      rw [coeff_reverseFixed, _root_.ite_eq_left hi]
      by_cases hki : k < i
      · rw [_root_.ite_eq_left hki]
        rw [_root_.ite_eq_right (by omega)]
        rw [DensePoly.coeff_eq_zero_of_size_le q (by omega)]
        exact (Int.mul_zero _).symm
      · rw [_root_.ite_eq_right hki]
        by_cases hqki : q.size ≤ k - i
        · rw [coeff_reverseFixed, _root_.ite_eq_right (Nat.not_lt.mpr hqki)]
          rw [_root_.ite_eq_left (by omega)]
          rw [Int.mul_zero]
        · rw [coeff_reverseFixed, _root_.ite_eq_left (Nat.lt_of_not_ge hqki)]
          rw [_root_.ite_eq_right (by omega)]
          congr 2 <;> omega
    have hmap :
        ((List.range p.size).map fun i =>
          DensePoly.diagonalMulCoeffTerm p q (slots - 1 - k) (p.size - 1 - i)) =
        (List.range p.size).map fun i =>
          DensePoly.diagonalMulCoeffTerm (reverseFixed p p.size)
            (reverseFixed q q.size) k i := by
      apply List.map_congr_left
      intro i hi
      exact (hterm i (List.mem_range.mp hi)).symm
    let term := fun i => DensePoly.diagonalMulCoeffTerm p q (slots - 1 - k) i
    calc
      (List.range p.size).foldl
          (fun acc i => acc + DensePoly.diagonalMulCoeffTerm
            (reverseFixed p p.size) (reverseFixed q q.size) k i) 0 =
          ((List.range p.size).map fun i =>
            DensePoly.diagonalMulCoeffTerm (reverseFixed p p.size)
              (reverseFixed q q.size) k i).foldl (fun acc x => acc + x) 0 :=
            foldAdd_map _ _ _
      _ = ((List.range p.size).map fun i => term (p.size - 1 - i)).foldl
          (fun acc x => acc + x) 0 := by rw [hmap]
      _ = ((List.range p.size).reverse.map term).foldl
          (fun acc x => acc + x) 0 := by
            rw [range_reverse_eq, List.map_map]
            change ((List.range p.size).map fun i => term (p.size - 1 - i)).foldl
              (fun acc x => acc + x) 0 = _
            rfl
      _ = ((List.range p.size).map term).reverse.foldl
          (fun acc x => acc + x) 0 := by rw [List.map_reverse]
      _ = ((List.range p.size).map term).foldl
          (fun acc x => acc + x) 0 := foldAdd_reverse _ _
      _ = (List.range p.size).foldl (fun acc i => acc + term i) 0 :=
          (foldAdd_map _ _ _).symm
  · rw [_root_.ite_eq_right hk]
    have hzero : ∀ i, i < p.size →
        DensePoly.diagonalMulCoeffTerm (reverseFixed p p.size)
          (reverseFixed q q.size) k i = 0 := by
      intro i hi
      unfold DensePoly.diagonalMulCoeffTerm
      split
      · rfl
      · rw [coeff_reverseFixed, _root_.ite_eq_left hi]
        rw [coeff_reverseFixed, _root_.ite_eq_right (by omega)]
        simp
    have hfold : ∀ xs : List Nat, (∀ i, i ∈ xs → i < p.size) →
        xs.foldl (fun acc i => acc +
          DensePoly.diagonalMulCoeffTerm (reverseFixed p p.size)
            (reverseFixed q q.size) k i) 0 = 0 := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons i is ih =>
          simp only [List.foldl_cons]
          rw [hzero i (hxs i (by simp)), Int.zero_add]
          exact ih (by intro j hj; exact hxs j (by simp [hj]))
    exact hfold _ (by intro i hi; exact List.mem_range.mp hi)

/-- Pack the coefficients from the leading end.  This represents the
reciprocal evaluation after clearing its negative power of the base. -/
@[inline]
def packReverse (b : Nat) (p : ZPoly) : Int :=
  packAux b (fun i => p.coeff (p.size - 1 - i)) 0 p.size

private theorem packSpec_congr (b : Nat) (f g : Nat → Int) :
    ∀ len, (∀ i, i < len → f i = g i) → packSpec b f len = packSpec b g len := by
  intro len
  induction len generalizing f g with
  | zero => intro _; rfl
  | succ len ih =>
      intro h
      simp only [packSpec]
      rw [h 0 (by omega), ih (fun i => f (i + 1)) (fun i => g (i + 1)) (by
        intro i hi
        exact h (i + 1) (by omega))]

private theorem natEval_congr (b : Nat) (f g : Nat → Nat) :
    ∀ len, (∀ i, i < len → f i = g i) → natEval b f len = natEval b g len := by
  intro len
  induction len generalizing f g with
  | zero => intro _; rfl
  | succ len ih =>
      intro h
      simp only [natEval]
      rw [h 0 (by omega), ih (fun i => f (i + 1)) (fun i => g (i + 1)) (by
        intro i hi
        exact h (i + 1) (by omega))]

private theorem packReverse_eq_eval (b : Nat) (p : ZPoly) :
    packReverse b p = DensePoly.eval (reverseFixed p p.size) ((2 : Int) ^ b) := by
  unfold packReverse
  rw [packAux_eq]
  simp only [Nat.zero_add]
  rw [show packSpec b (fun i => p.coeff (p.size - 1 - i)) p.size =
      packSpec b (reverseFixed p p.size).coeff p.size by
    apply packSpec_congr
    intro i hi
    rw [coeff_reverseFixed, _root_.ite_eq_left hi]]
  rw [packSpec_eq_eval]
  unfold reverseFixed
  exact Nat.le_trans (DensePoly.size_ofList_le _) (by simp)

private theorem packReverseProduct_eq (b : Nat) (p q : ZPoly)
    (hp : 0 < p.size) (hq : 0 < q.size) :
    packReverse b p * packReverse b q =
      packSpec b (fun i => (p * q).coeff (p.size + q.size - 2 - i))
        (p.size + q.size - 1) := by
  rw [packReverse_eq_eval, packReverse_eq_eval, ← DensePoly.eval_mul_commring,
    reverseFixed_mul p q hp hq]
  rw [← packSpec_eq_eval b (reverseFixed (p * q) (p.size + q.size - 1))
    (p.size + q.size - 1) (by
      unfold reverseFixed
      exact Nat.le_trans (DensePoly.size_ofList_le _) (by simp))]
  apply packSpec_congr
  intro i hi
  rw [coeff_reverseFixed, _root_.ite_eq_left hi]
  congr 2

/-- High-to-low evaluation of a fixed coefficient stream. -/
private def reverseNatEval (b : Nat) (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c 0 * (2 ^ b) ^ n + reverseNatEval b (fun i => c (i + 1)) n

private theorem reverseNatEval_eq (b : Nat) (c : Nat → Nat) : ∀ len,
    reverseNatEval b c len = natEval b (fun i => c (len - 1 - i)) len := by
  intro len
  induction len generalizing c with
  | zero => rfl
  | succ len ih =>
      simp only [reverseNatEval]
      rw [natEval_add b (fun i => c (len + 1 - 1 - i)) len 1]
      simp only [natEval]
      rw [ih (fun i => c (i + 1))]
      rw [natEval_congr b
        (fun i => c (len - 1 - i + 1))
        (fun i => c (len + 1 - 1 - i)) len (by
          intro i hi
          congr 1
          omega)]
      simp only [Nat.add_zero]
      rw [Nat.pow_mul]
      have hidx : len + 1 - 1 - len = 0 := by omega
      rw [hidx]
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [Nat.mul_comm, Nat.add_comm]

private theorem reverseNatEval_lt (b : Nat) (_hb : 0 < b) (c : Nat → Nat) :
    ∀ n, (∀ i, i < n → c i < 2 ^ b * (2 ^ b - 1)) →
      reverseNatEval b c n < (2 ^ b) ^ (n + 1) := by
  intro n
  induction n generalizing c with
  | zero =>
      intro _
      simp [reverseNatEval, Nat.pow_pos]
  | succ n ih =>
      intro hc
      have h0 := hc 0 (by omega)
      have htail := ih (fun i => c (i + 1)) (by
        intro i hi
        exact hc (i + 1) (by omega))
      simp only [reverseNatEval]
      let base := 2 ^ b
      let place := base ^ n
      have hbase : 0 < base := by
        dsimp [base]
        exact Nat.two_pow_pos b
      have hplace : 0 < place := Nat.pow_pos hbase
      have hfirst : c 0 * place < (base * (base - 1)) * place :=
        (Nat.mul_lt_mul_right hplace).2 h0
      have hsum : base * (base - 1) + base = base * base := by
        rw [Nat.mul_sub_left_distrib]
        have : base ≤ base * base := Nat.le_mul_of_pos_right base (by
          dsimp [base]
          exact hbase)
        omega
      change c 0 * place + reverseNatEval b (fun i => c (i + 1)) n < _
      calc
        c 0 * place + reverseNatEval b (fun i => c (i + 1)) n
            < (base * (base - 1)) * place + base * place :=
              Nat.add_lt_add hfirst (by
                simpa [base, place, Nat.pow_succ, Nat.mul_comm] using htail)
        _ = (base * base) * place := by rw [← Nat.add_mul, hsum]
        _ = base ^ (n + 2) := by
          rw [show n + 2 = (n + 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
          ac_rfl
        _ = (2 ^ b) ^ (n + 1 + 1) := by simp [base]

private theorem recoverReciprocalHead (base c forward tail place : Nat)
    (hbase : 0 < base) (hplace : 0 < place) (htail : tail < base * place) :
    let lo := (c + base * forward) % base
    let hi := ((c * place + tail) / place - lo) / base
    lo + base * hi = c := by
  dsimp only
  have hlo : (c + base * forward) % base = c % base := by
    simp [Nat.add_mod]
  rw [hlo]
  have hq : (c * place + tail) / place = c + tail / place := by
    simpa [Nat.add_comm, Nat.mul_comm] using Nat.add_mul_div_left tail c hplace
  rw [hq]
  have hgamma : tail / place < base := by
    exact (Nat.div_lt_iff_lt_mul hplace).2 (by simpa [Nat.mul_comm] using htail)
  have hrem : c % base ≤ c := Nat.mod_le _ _
  have hc : c % base + base * (c / base) = c := Nat.mod_add_div c base
  have hdiff : c - c % base = base * (c / base) := by omega
  have hsub : c + tail / place - c % base = base * (c / base) + tail / place := by
    rw [Nat.add_comm c, Nat.add_sub_assoc hrem, hdiff, Nat.add_comm]
  rw [hsub]
  have hdiv : (base * (c / base) + tail / place) / base = c / base := by
    simpa [Nat.add_comm, Nat.div_eq_of_lt hgamma] using
      Nat.add_mul_div_left (tail / place) (c / base) hbase
  rw [hdiv]
  exact hc

/-- Proof-oriented reciprocal reconstruction.  At each step the low base
digit of `forward` supplies the low half of the next coefficient.  Dividing
`reverse` at its leading slot supplies that coefficient plus a carry smaller
than one base digit, hence its high half after subtracting the known low half.
-/
@[expose]
def recoverReciprocalNat (b forward reverse len : Nat) : Array Nat :=
  if len = 0 then #[]
  else
    let base := 2 ^ b
    let place := base ^ (len - 1)
    let lo := forward % base
    let hi := (reverse / place - lo) / base
    let digit := lo + base * hi
    #[digit] ++ recoverReciprocalNat b ((forward - digit) / base)
      (reverse - digit * place) (len - 1)
termination_by len
decreasing_by omega

/-- Linear digit-state implementation of reciprocal reconstruction.  It
extracts the two packed products once, then propagates the two one-bit carry
chains using only slot-sized naturals. -/
@[expose]
def recoverReciprocalDigits (b forward reverse len : Nat) : Array Nat := Id.run do
  if len = 0 then return #[]
  let base := 2 ^ b
  let u := unpackAux b forward (len + 1)
  let q := unpackAux b reverse (len + 1)
  let mut out := Array.emptyWithCapacity len
  let mut alphaPrev := 0
  let mut alpha := u.getD 0 0
  let mut delta := 0
  for j in [0:len] do
    let wj := q.getD (len - j) 0
    let epsilon :=
      if j + 1 < len && alpha > q.getD (len - (j + 1)) 0 then 1 else 0
    let beta := (wj + base - alphaPrev - epsilon) % base
    out := out.push (alpha + base * beta)
    if j + 1 < len then
      let alphaNext := (u.getD (j + 1) 0 + base - beta - delta) % base
      delta := (beta + alphaNext + delta - u.getD (j + 1) 0) / base
      alphaPrev := alpha
      alpha := alphaNext
  return out

def packDigits (b : Nat) (a : Array Nat) : Int :=
  packAux b (fun i => Int.ofNat (a.getD i 0)) 0 a.size

def packDigitsReverse (b : Nat) (a : Array Nat) : Int :=
  packAux b (fun i => Int.ofNat (a.getD (a.size - 1 - i) 0)) 0 a.size

/-- Fast reciprocal recovery guarded by a proof-relevant certificate check.
The check repacks the bounded candidate in both directions; failure falls back
to the specification recurrence. -/
@[expose]
def recoverReciprocalChecked (b forward reverse len : Nat) : Array Nat :=
  let candidate := recoverReciprocalDigits b forward reverse len
  let limit := 2 ^ b * (2 ^ b - 1)
  if candidate.size = len ∧
      (∀ d ∈ candidate.toList, d < limit) ∧
      packDigits b candidate = Int.ofNat forward ∧
      packDigitsReverse b candidate = Int.ofNat reverse then
    candidate
  else
    recoverReciprocalNat b forward reverse len

/-- Reciprocal reconstruction inverts overlapping forward/reverse streams
when every coefficient fits below `B(B-1)`. -/
private theorem recoverReciprocalNat_eval (b : Nat) (hb : 0 < b) (c : Nat → Nat) :
    ∀ len, (∀ i, i < len → c i < 2 ^ b * (2 ^ b - 1)) →
      recoverReciprocalNat b (natEval b c len) (reverseNatEval b c len) len =
        ((List.range len).map c).toArray := by
  intro len
  induction len generalizing c with
  | zero =>
      intro _
      simp [recoverReciprocalNat]
  | succ len ih =>
      intro hc
      let base := 2 ^ b
      let tailForward := natEval b (fun i => c (i + 1)) len
      let tailReverse := reverseNatEval b (fun i => c (i + 1)) len
      have hbase : 0 < base := by
        dsimp [base]
        exact Nat.two_pow_pos b
      have htail : tailReverse < base * base ^ len := by
        have h := reverseNatEval_lt b hb (fun i => c (i + 1)) len (by
          intro i hi
          exact hc (i + 1) (by omega))
        simpa [base, Nat.pow_succ, Nat.mul_comm] using h
      have hdigit := recoverReciprocalHead base (c 0) tailForward tailReverse
        (base ^ len) hbase (Nat.pow_pos hbase) htail
      unfold recoverReciprocalNat
      rw [_root_.if_neg (by omega)]
      simp only [natEval, reverseNatEval]
      change
        let lo := (c 0 + base * tailForward) % base
        let hi := ((c 0 * base ^ len + tailReverse) / base ^ len - lo) / base
        let digit := lo + base * hi
        #[digit] ++ recoverReciprocalNat b
          ((c 0 + base * tailForward - digit) / base)
          (c 0 * base ^ len + tailReverse - digit * base ^ len) len = _
      dsimp only
      rw [hdigit]
      have hforward : (c 0 + base * tailForward - c 0) / base = tailForward := by
        rw [Nat.add_sub_cancel_left]
        simpa [Nat.mul_comm] using Nat.mul_div_left tailForward hbase
      have hreverse : c 0 * base ^ len + tailReverse - c 0 * base ^ len =
          tailReverse := Nat.add_sub_cancel_left _ _
      rw [hforward, hreverse, ih (fun i => c (i + 1)) (by
        intro i hi
        exact hc (i + 1) (by omega))]
      simp [List.range_succ_eq_map]

private theorem packDigits_eq (b : Nat) (a : Array Nat) :
    packDigits b a = Int.ofNat (natEval b (fun i => a.getD i 0) a.size) := by
  unfold packDigits
  rw [packAux_eq]
  simp only [Nat.zero_add]
  exact packSpec_natCast b (fun i => a.getD i 0) a.size

private theorem packDigitsReverse_eq (b : Nat) (a : Array Nat) :
    packDigitsReverse b a =
      Int.ofNat (reverseNatEval b (fun i => a.getD i 0) a.size) := by
  unfold packDigitsReverse
  rw [packAux_eq]
  simp only [Nat.zero_add]
  rw [reverseNatEval_eq]
  exact packSpec_natCast b (fun i => a.getD (a.size - 1 - i) 0) a.size

private theorem array_range_getD (a : Array Nat) :
    ((List.range a.size).map fun i => a.getD i 0).toArray = a := by
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    exact (Array.getElem_eq_getD 0).symm

private theorem recoverReciprocalChecked_eval (b : Nat) (hb : 0 < b)
    (c : Nat → Nat) (len : Nat)
    (hfit : ∀ i, i < len → c i < 2 ^ b * (2 ^ b - 1)) :
    recoverReciprocalChecked b (natEval b c len) (reverseNatEval b c len) len =
      ((List.range len).map c).toArray := by
  unfold recoverReciprocalChecked
  let candidate := recoverReciprocalDigits b (natEval b c len)
    (reverseNatEval b c len) len
  let valid := candidate.size = len ∧
    (∀ d ∈ candidate.toList, d < 2 ^ b * (2 ^ b - 1)) ∧
    packDigits b candidate = Int.ofNat (natEval b c len) ∧
    packDigitsReverse b candidate = Int.ofNat (reverseNatEval b c len)
  by_cases hvalid : valid
  · rw [_root_.ite_eq_left hvalid]
    rcases hvalid with ⟨hsize, hbounded, hforward, hreverse⟩
    let d : Nat → Nat := fun i => candidate.getD i 0
    have hdFit : ∀ i, i < len → d i < 2 ^ b * (2 ^ b - 1) := by
      intro i hi
      apply hbounded
      unfold d
      have hic : i < candidate.size := by omega
      rw [← Array.getElem_eq_getD 0]
      exact Array.getElem_mem_toList hic
    have hforwardNat : natEval b d len = natEval b c len := by
      rw [packDigits_eq] at hforward
      have h := Int.ofNat_inj.mp hforward
      simpa [d, hsize] using h
    have hreverseNat : reverseNatEval b d len = reverseNatEval b c len := by
      rw [packDigitsReverse_eq] at hreverse
      have h := Int.ofNat_inj.mp hreverse
      simpa [d, hsize] using h
    have hdRecover := recoverReciprocalNat_eval b hb d len hdFit
    rw [hforwardNat, hreverseNat] at hdRecover
    calc
      candidate = ((List.range len).map d).toArray := by
        rw [← hsize]
        exact (array_range_getD candidate).symm
      _ = recoverReciprocalNat b (natEval b c len) (reverseNatEval b c len) len :=
        hdRecover.symm
      _ = ((List.range len).map c).toArray :=
        recoverReciprocalNat_eval b hb c len hfit
  · rw [_root_.ite_eq_right hvalid]
    exact recoverReciprocalNat_eval b hb c len hfit

private theorem ofCoeffs_unbias (r : ZPoly) (bias slots : Nat)
    (hsize : r.size ≤ slots)
    (hbound : ∀ i, (r.coeff i).natAbs ≤ bias) :
    DensePoly.ofCoeffs
      (((List.range slots).map fun i => (r.coeff i + (bias : Int)).toNat).toArray.map
        fun d => Int.ofNat d - Int.ofNat bias) = r := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_ofCoeffs]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  by_cases hi : i < slots
  · rw [Array.getElem?_eq_getElem (by simpa using hi), Option.map_some, Option.getD_some]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    have hnonneg : 0 ≤ r.coeff i + (bias : Int) := by
      have habs := Int.le_natAbs (a := -r.coeff i)
      rw [Int.natAbs_neg] at habs
      have hb := hbound i
      have hbInt : ((r.coeff i).natAbs : Int) ≤ (bias : Int) := by
        exact_mod_cast hb
      omega
    have hcast : Int.ofNat (r.coeff i + (bias : Int)).toNat =
        r.coeff i + (bias : Int) := Int.toNat_of_nonneg hnonneg
    rw [hcast]
    exact Int.add_sub_cancel _ _
  · have hnone :
        ((List.range slots).map
          (fun i => (r.coeff i + (bias : Int)).toNat)).toArray[i]? = none := by
      rw [Array.getElem?_eq_none]
      simp only [List.size_toArray, List.length_map, List.length_range]
      exact Nat.le_of_not_gt hi
    rw [hnone, Option.map_none, Option.getD_none]
    exact (DensePoly.coeff_eq_zero_of_size_le r (by omega)).symm

/-- Reciprocal Kronecker identity with explicit bias and slot width. -/
theorem kronecker3_identity (p q : ZPoly) (b bias : Nat)
    (hb : 0 < b) (hp : 0 < p.size) (hq : 0 < q.size)
    (hbound : ∀ i, ((p * q).coeff i).natAbs ≤ bias)
    (hfit : ∀ i, i < p.size + q.size - 1 →
      ((p * q).coeff i + (bias : Int)).toNat < 2 ^ b * (2 ^ b - 1)) :
    let slots := p.size + q.size - 1
    let forward := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
    let reverse := packReverse b p * packReverse b q
    let biasPack := constPack b (bias : Int) slots
    let digits := recoverReciprocalChecked b (forward + biasPack).toNat
      (reverse + biasPack).toNat slots
    DensePoly.ofCoeffs (digits.map fun d => Int.ofNat d - Int.ofNat bias) = p * q := by
  dsimp only
  let r := p * q
  let slots := p.size + q.size - 1
  have hsize : r.size ≤ slots := DensePoly.size_mul_le p q
  let c : Nat → Nat := fun i => (r.coeff i + (bias : Int)).toNat
  have hcast : ∀ i, Int.ofNat (c i) = r.coeff i + (bias : Int) := by
    intro i
    unfold c
    have habs := Int.le_natAbs (a := -r.coeff i)
    rw [Int.natAbs_neg] at habs
    have hbias : (r.coeff i).natAbs ≤ bias := by simpa [r] using hbound i
    have hbiasInt : ((r.coeff i).natAbs : Int) ≤ (bias : Int) := by
      exact_mod_cast hbias
    apply Int.toNat_of_nonneg
    omega
  have hforward :
      packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size +
          constPack b (bias : Int) slots = (natEval b c slots : Int) := by
    rw [packProduct_eq p q b slots hsize, constPack_eq,
      ← packSpec_add_fun, ← packSpec_natCast b c slots]
    apply packSpec_congr
    intro i hi
    exact (hcast i).symm
  have hreverse :
      packReverse b p * packReverse b q + constPack b (bias : Int) slots =
        (reverseNatEval b c slots : Int) := by
    rw [packReverseProduct_eq b p q hp hq, constPack_eq]
    change packSpec b (fun i => r.coeff (slots - 1 - i)) slots +
      packSpec b (fun _ => (bias : Int)) slots = _
    rw [← packSpec_add_fun]
    rw [reverseNatEval_eq, ← packSpec_natCast]
    apply packSpec_congr
    intro i hi
    exact (hcast (slots - 1 - i)).symm
  rw [hforward, hreverse]
  simp only [Int.toNat_natCast]
  rw [recoverReciprocalChecked_eval b hb c slots (by
    intro i hi
    exact hfit i hi)]
  exact ofCoeffs_unbias r bias slots hsize hbound

private theorem twice_lt_overlap (bound : Nat) :
    let b := (bitLen bound + 3) / 2
    2 * bound < 2 ^ b * (2 ^ b - 1) := by
  dsimp only
  let k := bitLen bound
  let b := (k + 3) / 2
  have hb : 0 < b := by dsimp [b, k]; omega
  have hbound := lt_two_pow_bitLen bound
  have htwice : 2 * bound < 2 ^ (k + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    exact (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hbound
  have hexp : k + 1 ≤ 2 * b - 1 := by dsimp [b]; omega
  have hpows : 2 ^ (k + 1) ≤ 2 ^ (2 * b - 1) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hhalf : 2 ^ (b - 1) ≤ 2 ^ b - 1 := by
    have := Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : b - 1 < b)
    omega
  have hoverlap : 2 ^ (2 * b - 1) ≤ 2 ^ b * (2 ^ b - 1) := by
    rw [show 2 * b - 1 = b + (b - 1) by omega, Nat.pow_add]
    exact Nat.mul_le_mul_left _ hhalf
  exact Nat.lt_of_lt_of_le htwice (Nat.le_trans hpows hoverlap)

/-- KS3 with no dispatcher guard.  It performs one forward and one reciprocal
packed multiplication.  A coefficient-level bias makes the signed product
stream nonnegative before reciprocal reconstruction. -/
@[expose]
def mulKronecker3 (p q : ZPoly) : ZPoly :=
  if p.isZero || q.isZero then 0
  else
    let terms := min p.size q.size
    let bound := terms * (maxAbs p * maxAbs q)
    let b := (bitLen bound + 3) / 2
    let slots := p.size + q.size - 1
    let forward := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
    let reverse := packReverse b p * packReverse b q
    let biasPack := constPack b (bound : Int) slots
    let digits := recoverReciprocalChecked b (forward + biasPack).toNat
      (reverse + biasPack).toNat slots
    DensePoly.ofCoeffs (digits.map fun d => Int.ofNat d - Int.ofNat bound)

/-- The forced reciprocal kernel computes the ordinary dense product. -/
theorem mulKronecker3_eq (p q : ZPoly) : mulKronecker3 p q = p * q := by
  unfold mulKronecker3
  by_cases hz : p.isZero || q.isZero
  · rw [_root_.ite_eq_left hz]
    have h := mulKroneckerAt_eq 0 0 p q
    unfold mulKroneckerAt at h
    rw [_root_.ite_eq_left hz] at h
    exact h
  · rw [_root_.ite_eq_right hz]
    let terms := min p.size q.size
    let bound := terms * (maxAbs p * maxAbs q)
    let b := (bitLen bound + 3) / 2
    have hpFalse : p.isZero = false := by
      cases hpz : p.isZero <;> cases hqz : q.isZero <;> simp [hpz, hqz] at hz ⊢
    have hqFalse : q.isZero = false := by
      cases hpz : p.isZero <;> cases hqz : q.isZero <;> simp [hpz, hqz] at hz ⊢
    apply kronecker3_identity p q b bound
    · dsimp [b]
      omega
    · exact (DensePoly.isZero_eq_false_iff p).1 hpFalse
    · exact (DensePoly.isZero_eq_false_iff q).1 hqFalse
    · intro i
      exact natAbs_coeff_mul_le_separate p q (maxAbs p) (maxAbs q)
        (natAbs_coeff_le_maxAbs p) (natAbs_coeff_le_maxAbs q) i
    · intro i hi
      have hcoeff := natAbs_coeff_mul_le_separate p q (maxAbs p) (maxAbs q)
        (natAbs_coeff_le_maxAbs p) (natAbs_coeff_le_maxAbs q) i
      have hupper : (p * q).coeff i ≤ (bound : Int) := by
        have habs := Int.le_natAbs (a := (p * q).coeff i)
        have hboundInt : (((p * q).coeff i).natAbs : Int) ≤ (bound : Int) := by
          exact_mod_cast hcoeff
        omega
      have hdigit : ((p * q).coeff i + (bound : Int)).toNat ≤ 2 * bound := by
        rw [Int.toNat_le]
        push_cast
        omega
      exact Nat.lt_of_le_of_lt hdigit (twice_lt_overlap bound)

/-! # Negated reciprocal four-product substitution -/

/-- Pack the reciprocal coefficient stream with alternating signs in reciprocal
order.  Together with `packReverse`, this separates the even and odd streams
of the reversed product. -/
@[inline]
def packReverseAlternating (b : Nat) (p : ZPoly) : Int :=
  packAux b (fun i =>
    if i % 2 = 0 then p.coeff (p.size - 1 - i)
    else -p.coeff (p.size - 1 - i)) 0 p.size

private theorem packReverse_eq_pack (b : Nat) (p : ZPoly) :
    packReverse b p = packAux b (reverseFixed p p.size).coeff 0
      (reverseFixed p p.size).size := by
  rw [packReverse_eq_eval]
  rw [packAux_eq]
  simp only [Nat.zero_add]
  rw [packSpec_eq_eval b (reverseFixed p p.size)
    (reverseFixed p p.size).size (Nat.le_refl _)]

private theorem packReverseAlternating_eq_pack (b : Nat) (p : ZPoly) :
    packReverseAlternating b p =
      packAux b (alternatingCoeff (reverseFixed p p.size)) 0
        (reverseFixed p p.size).size := by
  rw [packAlternating_eq_eval]
  unfold packReverseAlternating
  rw [packAux_eq]
  simp only [Nat.zero_add]
  rw [← packAlternatingSpec_eq_eval b (reverseFixed p p.size) p.size (by
    unfold reverseFixed
    exact Nat.le_trans (DensePoly.size_ofList_le _) (by simp))]
  apply packSpec_congr
  intro i hi
  unfold alternatingCoeff
  rw [coeff_reverseFixed, _root_.ite_eq_left hi]

private theorem splitProduct_eq (p q : ZPoly) (b slots : Nat)
    (hsize : (p * q).size ≤ slots) :
    let plus := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
    let minus := packAux b (alternatingCoeff p) 0 p.size *
      packAux b (alternatingCoeff q) 0 q.size
    ((plus + minus) / 2 =
      packSpec (2 * b) (evenPart (p * q)).coeff ((slots + 1) / 2)) ∧
    ((plus - minus) / (2 ^ (b + 1) : Nat) =
      packSpec (2 * b) (oddPart (p * q)).coeff (slots / 2)) := by
  dsimp only
  let r := p * q
  let evenSlots := (slots + 1) / 2
  let oddSlots := slots / 2
  let evenPacked := packSpec (2 * b) (evenPart r).coeff evenSlots
  let oddPacked := packSpec (2 * b) (oddPart r).coeff oddSlots
  have hplus := packProduct_eq p q b slots hsize
  rw [packSpec_evenOdd] at hplus
  have hevenFun : (fun i => r.coeff (2 * i)) = (evenPart r).coeff := by
    funext i
    exact (coeff_evenPart r i).symm
  have hoddFun : (fun i => r.coeff (2 * i + 1)) = (oddPart r).coeff := by
    funext i
    exact (coeff_oddPart r i).symm
  change _ = packSpec (2 * b) (fun i => r.coeff (2 * i)) evenSlots +
    (2 : Int) ^ b * packSpec (2 * b) (fun i => r.coeff (2 * i + 1)) oddSlots at hplus
  rw [hevenFun, hoddFun] at hplus
  change _ = evenPacked + (2 : Int) ^ b * oddPacked at hplus
  have hminus := packAlternatingProduct_eq p q b slots hsize
  change packAux b (alternatingCoeff p) 0 p.size *
      packAux b (alternatingCoeff q) 0 q.size =
    packSpec b (fun i => if i % 2 = 0 then r.coeff i else -r.coeff i) slots at hminus
  rw [packSpec_alternating_evenOdd] at hminus
  change _ = packSpec (2 * b) (fun i => r.coeff (2 * i)) evenSlots -
    (2 : Int) ^ b * packSpec (2 * b) (fun i => r.coeff (2 * i + 1)) oddSlots at hminus
  rw [hevenFun, hoddFun] at hminus
  change _ = evenPacked - (2 : Int) ^ b * oddPacked at hminus
  constructor
  · apply Int.ediv_eq_of_eq_mul_right (by omega)
    grind
  · have hden : ((2 ^ (b + 1) : Nat) : Int) = 2 * (2 : Int) ^ b := by
      rw [Nat.pow_succ]
      push_cast
      grind
    apply Int.ediv_eq_of_eq_mul_right (by
      rw [hden]
      have : (0 : Int) < 2 ^ b := Int.pow_pos (by omega)
      omega)
    rw [hden]
    grind

private theorem coeff_evenPart_reverseFixed (r : ZPoly) (slots i : Nat)
    (hi : i < (slots + 1) / 2) :
    (evenPart (reverseFixed r slots)).coeff i =
      if slots % 2 = 1 then
        (evenPart r).coeff ((slots + 1) / 2 - 1 - i)
      else
        (oddPart r).coeff (slots / 2 - 1 - i) := by
  rw [coeff_evenPart, coeff_reverseFixed, _root_.ite_eq_left (by omega)]
  by_cases hs : slots % 2 = 1
  · rw [_root_.ite_eq_left hs, coeff_evenPart]
    congr 1
    omega
  · rw [_root_.ite_eq_right hs, coeff_oddPart]
    congr 1
    omega

private theorem coeff_oddPart_reverseFixed (r : ZPoly) (slots i : Nat)
    (hi : i < slots / 2) :
    (oddPart (reverseFixed r slots)).coeff i =
      if slots % 2 = 1 then
        (oddPart r).coeff (slots / 2 - 1 - i)
      else
        (evenPart r).coeff ((slots + 1) / 2 - 1 - i) := by
  rw [coeff_oddPart, coeff_reverseFixed, _root_.ite_eq_left (by omega)]
  by_cases hs : slots % 2 = 1
  · rw [_root_.ite_eq_left hs, coeff_oddPart]
    congr 1
    omega
  · rw [_root_.ite_eq_right hs, coeff_evenPart]
    congr 1
    omega

private theorem recoverBiased_eq (s : ZPoly) (b bias slots : Nat)
    (hb : 0 < b) (hsize : s.size ≤ slots)
    (hbound : ∀ i, (s.coeff i).natAbs ≤ bias)
    (hfit : ∀ i, i < slots →
      (s.coeff i + (bias : Int)).toNat < 2 ^ b * (2 ^ b - 1))
    (forward reverse : Int)
    (hforward : forward = packSpec b s.coeff slots)
    (hreverse : reverse = packSpec b (fun i => s.coeff (slots - 1 - i)) slots) :
    DensePoly.ofCoeffs
      ((recoverReciprocalChecked b (forward + constPack b (bias : Int) slots).toNat
        (reverse + constPack b (bias : Int) slots).toNat slots).map
          fun d => Int.ofNat d - Int.ofNat bias) = s := by
  let c : Nat → Nat := fun i => (s.coeff i + (bias : Int)).toNat
  have hcast : ∀ i, Int.ofNat (c i) = s.coeff i + (bias : Int) := by
    intro i
    unfold c
    have habs := Int.le_natAbs (a := -s.coeff i)
    rw [Int.natAbs_neg] at habs
    have hbias := hbound i
    have hbiasInt : ((s.coeff i).natAbs : Int) ≤ (bias : Int) := by
      exact_mod_cast hbias
    apply Int.toNat_of_nonneg
    omega
  have hforwardNat :
      forward + constPack b (bias : Int) slots = (natEval b c slots : Int) := by
    rw [hforward, constPack_eq, ← packSpec_add_fun, ← packSpec_natCast b c slots]
    apply packSpec_congr
    intro i hi
    exact (hcast i).symm
  have hreverseNat :
      reverse + constPack b (bias : Int) slots =
        (reverseNatEval b c slots : Int) := by
    rw [hreverse, constPack_eq]
    rw [← packSpec_add_fun]
    rw [reverseNatEval_eq, ← packSpec_natCast]
    apply packSpec_congr
    intro i hi
    exact (hcast (slots - 1 - i)).symm
  rw [hforwardNat, hreverseNat]
  simp only [Int.toNat_natCast]
  rw [recoverReciprocalChecked_eval b hb c slots hfit]
  exact ofCoeffs_unbias s bias slots hsize hbound

/-- Four-point Kronecker identity with explicit bias and quarter-slot width. -/
theorem kronecker4_identity (p q : ZPoly) (b bias : Nat)
    (hb : 0 < b) (hp : 0 < p.size) (hq : 0 < q.size)
    (hbound : ∀ i, ((p * q).coeff i).natAbs ≤ bias)
    (hfit : ∀ i, i < p.size + q.size - 1 →
      ((p * q).coeff i + (bias : Int)).toNat <
        2 ^ (2 * b) * (2 ^ (2 * b) - 1)) :
    let slots := p.size + q.size - 1
    let evenSlots := (slots + 1) / 2
    let oddSlots := slots / 2
    let plus := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
    let minus := packAux b (alternatingCoeff p) 0 p.size *
      packAux b (alternatingCoeff q) 0 q.size
    let plusReverse := packReverse b p * packReverse b q
    let minusReverse := packReverseAlternating b p * packReverseAlternating b q
    let evenForward := (plus + minus) / 2
    let oddForward := (plus - minus) / (2 ^ (b + 1) : Nat)
    let reverseEven := (plusReverse + minusReverse) / 2
    let reverseOdd := (plusReverse - minusReverse) / (2 ^ (b + 1) : Nat)
    let evenReverse := if slots % 2 = 1 then reverseEven else reverseOdd
    let oddReverse := if slots % 2 = 1 then reverseOdd else reverseEven
    let evenBias := constPack (2 * b) (bias : Int) evenSlots
    let oddBias := constPack (2 * b) (bias : Int) oddSlots
    let evenDigits := recoverReciprocalChecked (2 * b)
      (evenForward + evenBias).toNat (evenReverse + evenBias).toNat evenSlots
    let oddDigits := recoverReciprocalChecked (2 * b)
      (oddForward + oddBias).toNat (oddReverse + oddBias).toNat oddSlots
    DensePoly.ofCoeffs (interleave
      (evenDigits.map fun d => Int.ofNat d - Int.ofNat bias)
      (oddDigits.map fun d => Int.ofNat d - Int.ofNat bias) slots) = p * q := by
  dsimp only
  let r := p * q
  let slots := p.size + q.size - 1
  let evenSlots := (slots + 1) / 2
  let oddSlots := slots / 2
  let plus := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
  let minus := packAux b (alternatingCoeff p) 0 p.size *
    packAux b (alternatingCoeff q) 0 q.size
  let plusReverse := packReverse b p * packReverse b q
  let minusReverse := packReverseAlternating b p * packReverseAlternating b q
  let evenForward := (plus + minus) / 2
  let oddForward := (plus - minus) / (2 ^ (b + 1) : Nat)
  let reverseEven := (plusReverse + minusReverse) / 2
  let reverseOdd := (plusReverse - minusReverse) / (2 ^ (b + 1) : Nat)
  let evenReverse := if slots % 2 = 1 then reverseEven else reverseOdd
  let oddReverse := if slots % 2 = 1 then reverseOdd else reverseEven
  have hsize : r.size ≤ slots := DensePoly.size_mul_le p q
  have hsplit := splitProduct_eq p q b slots hsize
  change evenForward = packSpec (2 * b) (evenPart r).coeff evenSlots ∧
    oddForward = packSpec (2 * b) (oddPart r).coeff oddSlots at hsplit
  rcases hsplit with ⟨hevenForward, hoddForward⟩
  let rp := reverseFixed p p.size
  let rq := reverseFixed q q.size
  have hreverseMul : rp * rq = reverseFixed r slots := by
    dsimp [rp, rq, r, slots]
    exact reverseFixed_mul p q hp hq
  have hreverseSize : (rp * rq).size ≤ slots := by
    rw [hreverseMul]
    unfold reverseFixed
    exact Nat.le_trans (DensePoly.size_ofList_le _) (by simp [slots])
  have hsplitReverse := splitProduct_eq rp rq b slots hreverseSize
  rcases hsplitReverse with ⟨hevenReverseRaw, hoddReverseRaw⟩
  change
    ((packAux b rp.coeff 0 rp.size * packAux b rq.coeff 0 rq.size +
      packAux b (alternatingCoeff rp) 0 rp.size *
        packAux b (alternatingCoeff rq) 0 rq.size) / 2 = _) at hevenReverseRaw
  change
    ((packAux b rp.coeff 0 rp.size * packAux b rq.coeff 0 rq.size -
      packAux b (alternatingCoeff rp) 0 rp.size *
        packAux b (alternatingCoeff rq) 0 rq.size) /
          (2 ^ (b + 1) : Nat) = _) at hoddReverseRaw
  rw [← packReverse_eq_pack b p, ← packReverse_eq_pack b q,
    ← packReverseAlternating_eq_pack b p,
    ← packReverseAlternating_eq_pack b q, hreverseMul] at hevenReverseRaw hoddReverseRaw
  change reverseEven =
    packSpec (2 * b) (evenPart (reverseFixed r slots)).coeff evenSlots at hevenReverseRaw
  change reverseOdd =
    packSpec (2 * b) (oddPart (reverseFixed r slots)).coeff oddSlots at hoddReverseRaw
  have hevenReversePack : evenReverse =
      packSpec (2 * b) (fun i => (evenPart r).coeff (evenSlots - 1 - i))
        evenSlots := by
    by_cases hs : slots % 2 = 1
    · rw [show evenReverse = reverseEven by simp [evenReverse, hs], hevenReverseRaw]
      apply packSpec_congr
      intro i hi
      rw [coeff_evenPart_reverseFixed r slots i hi, _root_.ite_eq_left hs]
    · rw [show evenReverse = reverseOdd by simp [evenReverse, hs], hoddReverseRaw]
      have hlens : oddSlots = evenSlots := by
        dsimp [oddSlots, evenSlots]
        have hmod : slots % 2 = 0 := by omega
        omega
      rw [hlens]
      apply packSpec_congr
      intro i hi
      have hiOdd : i < oddSlots := by omega
      rw [coeff_oddPart_reverseFixed r slots i hiOdd, _root_.ite_eq_right hs]
  have hoddReversePack : oddReverse =
      packSpec (2 * b) (fun i => (oddPart r).coeff (oddSlots - 1 - i))
        oddSlots := by
    by_cases hs : slots % 2 = 1
    · rw [show oddReverse = reverseOdd by simp [oddReverse, hs], hoddReverseRaw]
      apply packSpec_congr
      intro i hi
      rw [coeff_oddPart_reverseFixed r slots i hi, _root_.ite_eq_left hs]
    · rw [show oddReverse = reverseEven by simp [oddReverse, hs], hevenReverseRaw]
      have hlens : evenSlots = oddSlots := by
        dsimp [oddSlots, evenSlots]
        have hmod : slots % 2 = 0 := by omega
        omega
      rw [hlens]
      apply packSpec_congr
      intro i hi
      have hiEven : i < evenSlots := by omega
      rw [coeff_evenPart_reverseFixed r slots i hiEven, _root_.ite_eq_right hs]
  have hevenSize : (evenPart r).size ≤ evenSlots := by
    unfold evenPart
    refine Nat.le_trans (DensePoly.size_ofList_le _) ?_
    simpa only [List.length_map, List.length_range] using
      (Nat.div_le_div_right (Nat.add_le_add_right hsize 1) :
        (r.size + 1) / 2 ≤ (slots + 1) / 2)
  have hoddSize : (oddPart r).size ≤ oddSlots := by
    unfold oddPart
    refine Nat.le_trans (DensePoly.size_ofList_le _) ?_
    simpa only [List.length_map, List.length_range] using
      (Nat.div_le_div_right hsize : r.size / 2 ≤ slots / 2)
  have hevenBound : ∀ i, ((evenPart r).coeff i).natAbs ≤ bias := by
    intro i
    rw [coeff_evenPart]
    exact hbound (2 * i)
  have hoddBound : ∀ i, ((oddPart r).coeff i).natAbs ≤ bias := by
    intro i
    rw [coeff_oddPart]
    exact hbound (2 * i + 1)
  have hevenFit : ∀ i, i < evenSlots →
      ((evenPart r).coeff i + (bias : Int)).toNat <
        2 ^ (2 * b) * (2 ^ (2 * b) - 1) := by
    intro i hi
    rw [coeff_evenPart]
    exact hfit (2 * i) (by omega)
  have hoddFit : ∀ i, i < oddSlots →
      ((oddPart r).coeff i + (bias : Int)).toNat <
        2 ^ (2 * b) * (2 ^ (2 * b) - 1) := by
    intro i hi
    rw [coeff_oddPart]
    exact hfit (2 * i + 1) (by omega)
  apply ofCoeffs_interleave r _ _ slots hsize
  · exact recoverBiased_eq (evenPart r) (2 * b) bias evenSlots (by omega)
      hevenSize hevenBound hevenFit evenForward evenReverse
      hevenForward hevenReversePack
  · exact recoverBiased_eq (oddPart r) (2 * b) bias oddSlots (by omega)
      hoddSize hoddBound hoddFit oddForward oddReverse hoddForward hoddReversePack

/-- KS4 with no dispatcher guard.  Forward, negated, reciprocal, and negated
reciprocal evaluations give four packed integer products.  Even and odd
coefficient streams are then reconstructed independently at the squared base. -/
@[expose]
def mulKronecker4 (p q : ZPoly) : ZPoly :=
  if p.isZero || q.isZero then 0
  else
    let terms := min p.size q.size
    let bound := terms * (maxAbs p * maxAbs q)
    let overlapBits := (bitLen bound + 3) / 2
    let b := (overlapBits + 1) / 2
    let slotBits := 2 * b
    let slots := p.size + q.size - 1
    let evenSlots := (slots + 1) / 2
    let oddSlots := slots / 2
    let plus := packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
    let minus := packAux b (alternatingCoeff p) 0 p.size *
      packAux b (alternatingCoeff q) 0 q.size
    let plusReverse := packReverse b p * packReverse b q
    let minusReverse := packReverseAlternating b p * packReverseAlternating b q
    let evenForward := (plus + minus) / 2
    let oddForward := (plus - minus) / (2 ^ (b + 1) : Nat)
    let reverseEven := (plusReverse + minusReverse) / 2
    let reverseOdd := (plusReverse - minusReverse) / (2 ^ (b + 1) : Nat)
    let evenReverse := if slots % 2 = 1 then reverseEven else reverseOdd
    let oddReverse := if slots % 2 = 1 then reverseOdd else reverseEven
    let evenBias := constPack slotBits (bound : Int) evenSlots
    let oddBias := constPack slotBits (bound : Int) oddSlots
    let evenDigits := recoverReciprocalChecked slotBits
      (evenForward + evenBias).toNat (evenReverse + evenBias).toNat evenSlots
    let oddDigits := recoverReciprocalChecked slotBits
      (oddForward + oddBias).toNat (oddReverse + oddBias).toNat oddSlots
    DensePoly.ofCoeffs (interleave
      (evenDigits.map fun d => Int.ofNat d - Int.ofNat bound)
      (oddDigits.map fun d => Int.ofNat d - Int.ofNat bound) slots)

/-- The forced four-product kernel computes the ordinary dense product. -/
theorem mulKronecker4_eq (p q : ZPoly) : mulKronecker4 p q = p * q := by
  unfold mulKronecker4
  by_cases hz : p.isZero || q.isZero
  · rw [_root_.ite_eq_left hz]
    have h := mulKroneckerAt_eq 0 0 p q
    unfold mulKroneckerAt at h
    rw [_root_.ite_eq_left hz] at h
    exact h
  · rw [_root_.ite_eq_right hz]
    let terms := min p.size q.size
    let bound := terms * (maxAbs p * maxAbs q)
    let overlapBits := (bitLen bound + 3) / 2
    let b := (overlapBits + 1) / 2
    have hpFalse : p.isZero = false := by
      cases hpz : p.isZero <;> cases hqz : q.isZero <;> simp [hpz, hqz] at hz ⊢
    have hqFalse : q.isZero = false := by
      cases hpz : p.isZero <;> cases hqz : q.isZero <;> simp [hpz, hqz] at hz ⊢
    apply kronecker4_identity p q b bound
    · dsimp [b, overlapBits]
      omega
    · exact (DensePoly.isZero_eq_false_iff p).1 hpFalse
    · exact (DensePoly.isZero_eq_false_iff q).1 hqFalse
    · intro i
      exact natAbs_coeff_mul_le_separate p q (maxAbs p) (maxAbs q)
        (natAbs_coeff_le_maxAbs p) (natAbs_coeff_le_maxAbs q) i
    · intro i hi
      have hcoeff := natAbs_coeff_mul_le_separate p q (maxAbs p) (maxAbs q)
        (natAbs_coeff_le_maxAbs p) (natAbs_coeff_le_maxAbs q) i
      have hupper : (p * q).coeff i ≤ (bound : Int) := by
        have habs := Int.le_natAbs (a := (p * q).coeff i)
        have hboundInt : (((p * q).coeff i).natAbs : Int) ≤ (bound : Int) := by
          exact_mod_cast hcoeff
        omega
      have hdigit : ((p * q).coeff i + (bound : Int)).toNat ≤ 2 * bound := by
        rw [Int.toNat_le]
        push_cast
        omega
      have hoverlap : overlapBits ≤ 2 * b := by
        dsimp [b]
        omega
      have hpows : 2 ^ overlapBits ≤ 2 ^ (2 * b) :=
        Nat.pow_le_pow_right (by omega) hoverlap
      have hproduct :
          2 ^ overlapBits * (2 ^ overlapBits - 1) ≤
            2 ^ (2 * b) * (2 ^ (2 * b) - 1) :=
        Nat.mul_le_mul hpows (Nat.sub_le_sub_right hpows 1)
      exact Nat.lt_of_le_of_lt hdigit
        (Nat.lt_of_lt_of_le (twice_lt_overlap bound) hproduct)

end ZPoly
end Hex
