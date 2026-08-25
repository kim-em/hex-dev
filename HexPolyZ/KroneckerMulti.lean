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

end ZPoly
end Hex
