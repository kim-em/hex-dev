/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public import HexPolyZ.IntegerPolynomial

public section
set_option backward.proofsInPublic true

/-!
Kronecker substitution for the integer dense polynomial product.

The schoolbook convolution `Hex.DensePoly.mul` issues one coefficient
multiplication per index pair. When the coefficients are multi-limb integers
that is `Θ(n²)` GMP calls with a fresh allocation each; packing both operands
into single integers and issuing **one** GMP multiplication instead hands the
work to GMP's Toom/FFT ladder.

The substitution evaluates both operands at `2 ^ b` for a slot width `b` wide
enough that no product coefficient overflows its slot, multiplies the two
integers, and reads the product coefficients back off as base-`2 ^ b` digits.
Evaluation at a point is multiplicative (`Hex.DensePoly.eval_mul_commring`), so
the packed product *is* the packed answer; the only obligation left is that the
slots do not overlap.

Coefficients are signed, so every slot carries the bias `2 ^ (b - 1)`: a
coefficient `c` with `|c| < 2 ^ (b - 1)` becomes the digit `c + 2 ^ (b - 1)` in
`[0, 2 ^ b)`. Biasing the packed *product* by the same amount in every slot is
one addition of a precomputed constant, and turns digit extraction back into
plain base-`2 ^ b` division — no borrow propagation, so both packing and
unpacking run as balanced divide-and-conquer over shifts, `O(n log n)` limb
operations rather than the `O(n²)` of a sequential Horner scan.

The slot width is **measured at runtime**, not assumed: `Hex.ZPoly.maxAbs`
scans the actual coefficients and `Hex.ZPoly.mulKroneckerAt` derives `b`
from that scan, so the no-overlap bound is re-established on every call.

Below the measured cutoff the schoolbook loop still wins and is what runs; see
`HexPolyZ/SPEC/hex-poly-z.md` for the sweep behind `Hex.ZPoly.kroneckerCutoff`.
-/

namespace Hex

namespace ZPoly

/-! # Bit-width bookkeeping -/

/-- The number of bits in `n`: the least `k` with `n < 2 ^ k`. -/
@[expose]
def bitLen (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- `n` fits in {name}`bitLen` bits. -/
theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n := by
  unfold bitLen
  by_cases h : n = 0
  · simp [h]
  · rw [if_neg h]
    exact Nat.lt_log2_self

/-- The least `k` with `n ≤ 2 ^ k`. -/
@[expose]
def ceilLog2 (n : Nat) : Nat :=
  bitLen (n - 1)

/-- `n` is at most `2 ^ ceilLog2 n`. -/
theorem le_two_pow_ceilLog2 (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  by_cases h : n = 0
  · simp [h]
  · have := lt_two_pow_bitLen (n - 1)
    omega

/-! # The coefficient bound -/

/-- The largest absolute value of a stored coefficient. -/
@[expose]
def maxAbs (p : ZPoly) : Nat :=
  p.toArray.foldl (fun m c => max m c.natAbs) 0

private theorem le_foldl_max (f : Int → Nat) :
    ∀ (l : List Int) (a : Nat), a ≤ l.foldl (fun m c => max m (f c)) a := by
  intro l
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons x xs ih =>
      intro a
      exact Nat.le_trans (Nat.le_max_left a (f x)) (ih (max a (f x)))

private theorem foldl_max_ge (f : Int → Nat) :
    ∀ (l : List Int) (a : Nat) (x : Int), x ∈ l →
      f x ≤ l.foldl (fun m c => max m (f c)) a := by
  intro l
  induction l with
  | nil => intro a x hx; exact absurd hx (List.not_mem_nil)
  | cons y ys ih =>
      intro a x hx
      rcases List.mem_cons.mp hx with hxy | hxs
      · subst hxy
        exact Nat.le_trans (Nat.le_max_right a (f x)) (le_foldl_max f ys (max a (f x)))
      · exact ih (max a (f y)) x hxs

/-- Every coefficient is bounded in absolute value by {name}`maxAbs`. -/
theorem natAbs_coeff_le_maxAbs (p : ZPoly) (i : Nat) :
    (p.coeff i).natAbs ≤ maxAbs p := by
  unfold maxAbs
  by_cases hi : i < p.size
  · have hi' : i < p.toArray.toList.length := by simpa using hi
    have heq : p.toArray.toList[i] = p.coeff i := by
      rw [Array.getElem_toList, ← DensePoly.toArray_getD p i]
      exact Array.getElem_eq_getD (Zero.zero : Int)
    have hmem : p.coeff i ∈ p.toArray.toList := heq ▸ List.getElem_mem hi'
    rw [← Array.foldl_toList]
    exact foldl_max_ge Int.natAbs p.toArray.toList 0 (p.coeff i) hmem
  · rw [DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hi)]
    exact Nat.zero_le _

private theorem foldl_add_natAbs_le (f : Nat → Int) (B : Nat) (hf : ∀ i, (f i).natAbs ≤ B) :
    ∀ (l : List Nat) (acc : Int),
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

/-- A product coefficient is bounded by the number of diagonal terms times the
square of the coefficient bound. This is the no-overlap budget: it is what the
slot width has to accommodate. -/
theorem natAbs_coeff_mul_le (p q : ZPoly) (A : Nat)
    (hp : ∀ i, (p.coeff i).natAbs ≤ A) (hq : ∀ j, (q.coeff j).natAbs ≤ A) (n : Nat) :
    ((p * q).coeff n).natAbs ≤ p.size * (A * A) := by
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_diagonal]
  have hterm : ∀ i, (DensePoly.diagonalMulCoeffTerm p q n i).natAbs ≤ A * A := by
    intro i
    unfold DensePoly.diagonalMulCoeffTerm
    by_cases h : n < i
    · simp [h]
    · rw [if_neg h, Int.natAbs_mul]
      exact Nat.mul_le_mul (hp i) (hq (n - i))
  have := foldl_add_natAbs_le (DensePoly.diagonalMulCoeffTerm p q n) (A * A) hterm
    (List.range p.size) 0
  simpa using this

/-- The `min`-symmetric form of {name}`natAbs_coeff_mul_le`. -/
theorem natAbs_coeff_mul_le_min (p q : ZPoly) (A : Nat)
    (hp : ∀ i, (p.coeff i).natAbs ≤ A) (hq : ∀ j, (q.coeff j).natAbs ≤ A) (n : Nat) :
    ((p * q).coeff n).natAbs ≤ min p.size q.size * (A * A) := by
  by_cases h : p.size ≤ q.size
  · rw [Nat.min_eq_left h]
    exact natAbs_coeff_mul_le p q A hp hq n
  · rw [Nat.min_eq_right (Nat.le_of_not_ge h), DensePoly.mul_comm_poly]
    exact natAbs_coeff_mul_le q p A hq hp n

/-! # Base-`2 ^ b` Horner specifications -/

/-- `∑_{i < len} f i * (2 ^ b) ^ i`, as an integer. -/
@[expose]
def packSpec (b : Nat) (f : Nat → Int) : Nat → Int
  | 0 => 0
  | len + 1 => f 0 + 2 ^ b * packSpec b (fun i => f (i + 1)) len

/-- `∑_{i < len} c i * (2 ^ b) ^ i`, as a natural number. -/
@[expose]
def natEval (b : Nat) (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => c 0 + 2 ^ b * natEval b (fun i => c (i + 1)) len

/-- Splitting a packed range at `m`. -/
theorem packSpec_add (b : Nat) (f : Nat → Int) :
    ∀ (m k : Nat),
      packSpec b f (m + k) = packSpec b f m + 2 ^ (b * m) * packSpec b (fun i => f (m + i)) k := by
  intro m
  induction m generalizing f with
  | zero => intro k; simp [packSpec]
  | succ m ih =>
      intro k
      have h : m + 1 + k = (m + k) + 1 := by omega
      rw [h]
      show f 0 + 2 ^ b * packSpec b (fun i => f (i + 1)) (m + k) = _
      rw [ih (fun i => f (i + 1)) k]
      show _ = (f 0 + 2 ^ b * packSpec b (fun i => f (i + 1)) m)
        + 2 ^ (b * (m + 1)) * packSpec b (fun i => f (m + 1 + i)) k
      have hpow : (2 : Int) ^ (b * (m + 1)) = 2 ^ b * 2 ^ (b * m) := by
        rw [show b * (m + 1) = b + b * m by rw [Nat.mul_succ]; omega, Int.pow_add]
      have hfun : (fun i => f (m + 1 + i)) = (fun i => (fun j => f (j + 1)) (m + i)) := by
        funext i
        congr 1
        omega
      rw [hpow, hfun]
      grind

/-- Splitting a `Nat`-valued packed range at `m`. -/
theorem natEval_add (b : Nat) (c : Nat → Nat) :
    ∀ (m k : Nat),
      natEval b c (m + k) = natEval b c m + 2 ^ (b * m) * natEval b (fun i => c (m + i)) k := by
  intro m
  induction m generalizing c with
  | zero => intro k; simp [natEval]
  | succ m ih =>
      intro k
      have h : m + 1 + k = (m + k) + 1 := by omega
      rw [h]
      show c 0 + 2 ^ b * natEval b (fun i => c (i + 1)) (m + k) = _
      rw [ih (fun i => c (i + 1)) k]
      show _ = (c 0 + 2 ^ b * natEval b (fun i => c (i + 1)) m)
        + 2 ^ (b * (m + 1)) * natEval b (fun i => c (m + 1 + i)) k
      have hpow : (2 : Nat) ^ (b * (m + 1)) = 2 ^ b * 2 ^ (b * m) := by
        rw [show b * (m + 1) = b + b * m by rw [Nat.mul_succ]; omega, Nat.pow_add]
      have hfun : (fun i => c (m + 1 + i)) = (fun i => (fun j => c (j + 1)) (m + i)) := by
        funext i
        congr 1
        omega
      rw [hpow, hfun]
      grind

/-- A packed range of `len` digits below `2 ^ b` stays below `2 ^ (b * len)`. -/
theorem natEval_lt (b : Nat) :
    ∀ (c : Nat → Nat) (len : Nat), (∀ i, c i < 2 ^ b) → natEval b c len < 2 ^ (b * len) := by
  intro c len
  induction len generalizing c with
  | zero => intro _; simp [natEval]
  | succ len ih =>
      intro hc
      have hrec := ih (fun i => c (i + 1)) (fun i => hc (i + 1))
      show c 0 + 2 ^ b * natEval b (fun i => c (i + 1)) len < 2 ^ (b * (len + 1))
      have hpow : (2 : Nat) ^ (b * (len + 1)) = 2 ^ b * 2 ^ (b * len) := by
        rw [show b * (len + 1) = b + b * len by rw [Nat.mul_succ]; omega, Nat.pow_add]
      rw [hpow]
      have h0 : c 0 < 2 ^ b := hc 0
      have hstep : natEval b (fun i => c (i + 1)) len + 1 ≤ 2 ^ (b * len) := hrec
      calc c 0 + 2 ^ b * natEval b (fun i => c (i + 1)) len
          < 2 ^ b + 2 ^ b * natEval b (fun i => c (i + 1)) len := by omega
        _ = 2 ^ b * (natEval b (fun i => c (i + 1)) len + 1) := by
              rw [Nat.mul_succ]; omega
        _ ≤ 2 ^ b * 2 ^ (b * len) := Nat.mul_le_mul_left _ hstep

/-- The `Nat` and `Int` packed evaluations agree on nonnegative digits. -/
theorem packSpec_natCast (b : Nat) :
    ∀ (c : Nat → Nat) (len : Nat),
      packSpec b (fun i => (c i : Int)) len = (natEval b c len : Int) := by
  intro c len
  induction len generalizing c with
  | zero => simp [packSpec, natEval]
  | succ len ih =>
      show (c 0 : Int) + 2 ^ b * packSpec b (fun i => ((c (i + 1) : Nat) : Int)) len = _
      rw [ih (fun i => c (i + 1))]
      show _ = ((c 0 + 2 ^ b * natEval b (fun i => c (i + 1)) len : Nat) : Int)
      push_cast
      rfl

/-- Adding a constant to every slot adds the constant's packed range. -/
theorem packSpec_add_fun (b : Nat) (f g : Nat → Int) :
    ∀ (len : Nat),
      packSpec b (fun i => f i + g i) len = packSpec b f len + packSpec b g len := by
  intro len
  induction len generalizing f g with
  | zero => simp [packSpec]
  | succ len ih =>
      show f 0 + g 0 + 2 ^ b * packSpec b (fun i => f (i + 1) + g (i + 1)) len = _
      rw [ih (fun i => f (i + 1)) (fun i => g (i + 1))]
      show _ = (f 0 + 2 ^ b * packSpec b (fun i => f (i + 1)) len)
        + (g 0 + 2 ^ b * packSpec b (fun i => g (i + 1)) len)
      grind

/-! # Packing is evaluation at `2 ^ b` -/

private theorem packSpec_evalCoeffList (b : Nat) :
    ∀ (cs : List Int) (len : Nat), cs.length ≤ len →
      packSpec b (fun i => cs.getD i 0) len =
        DensePoly.evalCoeffList cs ((2 : Int) ^ b) := by
  intro cs
  induction cs with
  | nil =>
      intro len _
      have hzero : ∀ len, packSpec b (fun _ => (0 : Int)) len = 0 := by
        intro len
        induction len with
        | zero => rfl
        | succ len ih =>
            show (0 : Int) + 2 ^ b * packSpec b (fun _ => (0 : Int)) len = 0
            rw [ih]
            grind
      have hfun : (fun i => List.getD ([] : List Int) i 0) = (fun _ => (0 : Int)) := by
        funext i
        rfl
      show packSpec b (fun i => List.getD ([] : List Int) i 0) len = _
      rw [hfun, hzero len]
      rfl
  | cons c cs ih =>
      intro len hlen
      match len with
      | 0 => simp at hlen
      | len + 1 =>
          have hlen' : cs.length ≤ len := by simpa using hlen
          show (List.getD (c :: cs) 0 0 : Int)
            + 2 ^ b * packSpec b (fun i => List.getD (c :: cs) (i + 1) 0) len = _
          have hshift : (fun i => List.getD (c :: cs) (i + 1) 0) = (fun i => cs.getD i 0) := by
            funext i
            rfl
          rw [hshift, ih len hlen']
          show c + 2 ^ b * DensePoly.evalCoeffList cs ((2 : Int) ^ b) =
            DensePoly.evalCoeffList cs ((2 : Int) ^ b) * 2 ^ b + c
          grind

/-- Packing a polynomial's coefficients is Horner evaluation at `2 ^ b`. -/
theorem packSpec_eq_eval (b : Nat) (p : ZPoly) (len : Nat) (hlen : p.size ≤ len) :
    packSpec b p.coeff len = DensePoly.eval p ((2 : Int) ^ b) := by
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
  rw [← hcoeff, packSpec_evalCoeffList b p.toList len (by simpa using hlen)]
  rfl

/-! # Divide-and-conquer packing -/

/-- Balanced packing of `len` slots of width `b` starting at index `lo`. Halving
keeps the running integers balanced, so the shifts cost `O(n log n)` limb
operations instead of the `O(n²)` a sequential Horner scan would pay. -/
@[expose]
def packAux (b : Nat) (f : Nat → Int) (lo len : Nat) : Int :=
  if len = 0 then 0
  else if len = 1 then f lo
  else
    let h := len / 2
    packAux b f lo h + (packAux b f (lo + h) (len - h)) <<< (b * h)
termination_by len
decreasing_by
  · omega
  · omega

/-- The divide-and-conquer packing computes the packed range. -/
theorem packAux_eq (b : Nat) :
    ∀ (len : Nat) (f : Nat → Int) (lo : Nat),
      packAux b f lo len = packSpec b (fun i => f (lo + i)) len := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
      intro f lo
      unfold packAux
      match hlen : len with
      | 0 => simp [packSpec]
      | 1 =>
          simp only [Nat.one_ne_zero, ↓reduceIte]
          show f lo = f (lo + 0) + 2 ^ b * packSpec b (fun i => f (lo + (i + 1))) 0
          simp [packSpec]
      | (n + 2) =>
          have hne0 : n + 2 ≠ 0 := by omega
          have hne1 : n + 2 ≠ 1 := by omega
          simp only [hne0, hne1, ↓reduceIte]
          have hh : (n + 2) / 2 < n + 2 := by omega
          have ht : (n + 2) - (n + 2) / 2 < n + 2 := by omega
          rw [ih _ hh f lo, ih _ ht f (lo + (n + 2) / 2), Int.shiftLeft_eq]
          have hfun : (fun i => f (lo + (n + 2) / 2 + i)) =
              (fun i => (fun j => f (lo + j)) ((n + 2) / 2 + i)) := by
            funext i
            congr 1
            omega
          have hkey : packSpec b (fun i => f (lo + i)) (n + 2)
              = packSpec b (fun i => f (lo + i)) ((n + 2) / 2)
                + 2 ^ (b * ((n + 2) / 2))
                  * packSpec b (fun i => (fun j => f (lo + j)) ((n + 2) / 2 + i))
                    ((n + 2) - (n + 2) / 2) := by
            have h := packSpec_add b (fun i => f (lo + i)) ((n + 2) / 2) ((n + 2) - (n + 2) / 2)
            rw [show (n + 2) / 2 + ((n + 2) - (n + 2) / 2) = n + 2 by omega] at h
            exact h
          rw [hkey, hfun]
          grind

/-- Packing a *constant* slot value. The recursion doubles rather than walking
the slots, so the bias repunit costs `O(log n)` big-integer operations instead
of the `O(n)` a general `packAux` would pay for it — which measured as the
single largest cost in the Kronecker path before it was split out. -/
@[expose]
def constPack (b : Nat) (c : Int) (len : Nat) : Int :=
  if len = 0 then 0
  else
    let h := len / 2
    let lo := constPack b c h
    if len % 2 = 0 then lo + lo <<< (b * h)
    else lo + (c + lo <<< b) <<< (b * h)
termination_by len
decreasing_by omega

/-- The doubling recursion computes the constant packed range. -/
theorem constPack_eq (b : Nat) (c : Int) :
    ∀ (len : Nat), constPack b c len = packSpec b (fun _ => c) len := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
      unfold constPack
      by_cases hlen : len = 0
      · rw [if_pos hlen, hlen]
        rfl
      · rw [if_neg hlen]
        have hh : len / 2 < len := by omega
        have hsucc : ∀ m, packSpec b (fun _ => c) (m + 1)
            = c + 2 ^ b * packSpec b (fun _ => c) m := fun _ => rfl
        by_cases hpar : len % 2 = 0
        · have hsplit : packSpec b (fun _ => c) len
              = packSpec b (fun _ => c) (len / 2)
                + 2 ^ (b * (len / 2)) * packSpec b (fun _ => c) (len / 2) := by
            have h := packSpec_add b (fun _ => c) (len / 2) (len / 2)
            rw [show len / 2 + len / 2 = len by omega] at h
            exact h
          rw [if_pos hpar, ih _ hh, Int.shiftLeft_eq, hsplit]
          grind
        · have hsplit : packSpec b (fun _ => c) len
              = packSpec b (fun _ => c) (len / 2)
                + 2 ^ (b * (len / 2)) * packSpec b (fun _ => c) (len / 2 + 1) := by
            have h := packSpec_add b (fun _ => c) (len / 2) (len / 2 + 1)
            rw [show len / 2 + (len / 2 + 1) = len by omega] at h
            exact h
          rw [if_neg hpar, ih _ hh, Int.shiftLeft_eq, Int.shiftLeft_eq, hsplit, hsucc]
          grind

/-! # Divide-and-conquer digit extraction -/

/-- Balanced base-`2 ^ b` digit extraction of `n` into `len` slots. -/
@[expose]
def unpackAux (b n len : Nat) : Array Nat :=
  if len = 0 then #[]
  else if len = 1 then #[n]
  else
    let h := len / 2
    let d := b * h
    let hi := n >>> d
    let lo := n - (hi <<< d)
    unpackAux b lo h ++ unpackAux b hi (len - h)
termination_by len
decreasing_by
  · omega
  · omega

/-- Digit extraction inverts packing, given digits that fit their slots. -/
theorem unpackAux_natEval :
    ∀ (len : Nat) (b : Nat) (c : Nat → Nat), (∀ i, c i < 2 ^ b) →
      unpackAux b (natEval b c len) len = ((List.range len).map c).toArray := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
      intro b c hc
      unfold unpackAux
      match hlen : len with
      | 0 => simp
      | 1 =>
          simp only [Nat.one_ne_zero, ↓reduceIte]
          show #[natEval b c 1] = _
          simp [natEval]
      | (n + 2) =>
          have hne0 : n + 2 ≠ 0 := by omega
          have hne1 : n + 2 ≠ 1 := by omega
          simp only [hne0, hne1, ↓reduceIte]
          have hsplit : natEval b c (n + 2) =
              natEval b c ((n + 2) / 2)
                + 2 ^ (b * ((n + 2) / 2))
                  * natEval b (fun i => c ((n + 2) / 2 + i)) ((n + 2) - (n + 2) / 2) := by
            have h := natEval_add b c ((n + 2) / 2) ((n + 2) - (n + 2) / 2)
            rw [show (n + 2) / 2 + ((n + 2) - (n + 2) / 2) = n + 2 by omega] at h
            exact h
          have hlow : natEval b c ((n + 2) / 2) < 2 ^ (b * ((n + 2) / 2)) :=
            natEval_lt b c ((n + 2) / 2) hc
          have hhi : (natEval b c (n + 2)) >>> (b * ((n + 2) / 2))
              = natEval b (fun i => c ((n + 2) / 2 + i)) ((n + 2) - (n + 2) / 2) := by
            rw [Nat.shiftRight_eq_div_pow, hsplit,
              Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
              Nat.div_eq_of_lt hlow]
            omega
          have hlo : (natEval b c (n + 2))
              - ((natEval b c (n + 2)) >>> (b * ((n + 2) / 2))) <<< (b * ((n + 2) / 2))
              = natEval b c ((n + 2) / 2) := by
            rw [hhi, Nat.shiftLeft_eq, hsplit,
              Nat.mul_comm (2 ^ (b * ((n + 2) / 2)))
                (natEval b (fun i => c ((n + 2) / 2 + i)) ((n + 2) - (n + 2) / 2))]
            omega
          rw [hlo, hhi]
          have hh1 : (n + 2) / 2 < n + 2 := by omega
          have ht1 : (n + 2) - (n + 2) / 2 < n + 2 := by omega
          rw [ih ((n + 2) / 2) hh1 b c hc,
            ih ((n + 2) - (n + 2) / 2) ht1 b (fun i => c ((n + 2) / 2 + i))
              (fun i => hc ((n + 2) / 2 + i))]
          have hrange : List.range (n + 2) = List.range ((n + 2) / 2)
              ++ (List.range ((n + 2) - (n + 2) / 2)).map (fun i => (n + 2) / 2 + i) := by
            have h := List.range_add (n := (n + 2) / 2) (m := (n + 2) - (n + 2) / 2)
            rw [show (n + 2) / 2 + ((n + 2) - (n + 2) / 2) = n + 2 by omega] at h
            exact h
          rw [hrange]
          simp

/-! # The kernel -/

/-- The substitution identity. Given a slot width `b` whose half-range strictly
dominates every coefficient of the product, packing both operands at `2 ^ b`,
multiplying once, biasing every slot and reading the base-`2 ^ b` digits back
off recovers the schoolbook product exactly.

`hbudget` is the no-overlap bound; `Hex.ZPoly.mulKroneckerAt` discharges it from
a runtime scan of the actual coefficients rather than assuming it. -/
theorem kronecker_identity (p q : ZPoly) (b slots : Nat)
    (hb : 0 < b)
    (hsize : (p * q).size ≤ slots)
    (hbudget : ∀ n, ((p * q).coeff n).natAbs < 2 ^ (b - 1)) :
    DensePoly.ofCoeffs
      ((unpackAux b
        (packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
          + constPack b ((2 ^ (b - 1) : Nat) : Int) slots).toNat
        slots).map (fun d : Nat => (d : Int) - ((2 ^ (b - 1) : Nat) : Int)))
      = p * q := by
  have hcast : ∀ k, ((((p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int)).toNat : Nat) : Int)
      = (p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int) := by
    intro k
    have := hbudget k
    omega
  have hclt : ∀ k, (((p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int)).toNat) < 2 ^ b := by
    intro k
    have hb1 : (2 : Nat) ^ b = 2 ^ (b - 1) + 2 ^ (b - 1) := by
      have hstep : (2 : Nat) ^ ((b - 1) + 1) = 2 ^ (b - 1) * 2 := Nat.pow_succ 2 (b - 1)
      rw [show (b - 1) + 1 = b by omega] at hstep
      omega
    have h1 := hbudget k
    have h2 := hcast k
    omega
  have hpp : packAux b p.coeff 0 p.size = DensePoly.eval p ((2 : Int) ^ b) := by
    rw [packAux_eq]
    simpa using packSpec_eq_eval b p p.size (Nat.le_refl _)
  have hpq : packAux b q.coeff 0 q.size = DensePoly.eval q ((2 : Int) ^ b) := by
    rw [packAux_eq]
    simpa using packSpec_eq_eval b q q.size (Nat.le_refl _)
  have hpo : constPack b ((2 ^ (b - 1) : Nat) : Int) slots
      = packSpec b (fun _ => ((2 ^ (b - 1) : Nat) : Int)) slots :=
    constPack_eq b _ slots
  have hdigits :
      (packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
        + constPack b ((2 ^ (b - 1) : Nat) : Int) slots).toNat
      = natEval b (fun k => ((p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int)).toNat) slots := by
    rw [hpp, hpq, hpo, ← DensePoly.eval_mul_commring,
      ← packSpec_eq_eval b (p * q) slots hsize, ← packSpec_add_fun]
    have hfun : (fun i => (p * q).coeff i + ((2 ^ (b - 1) : Nat) : Int))
        = (fun i => (((((p * q).coeff i + ((2 ^ (b - 1) : Nat) : Int)).toNat) : Nat) : Int)) := by
      funext i
      rw [hcast i]
    rw [hfun, packSpec_natCast]
    exact Int.toNat_natCast _
  rw [hdigits, unpackAux_natEval slots b _ hclt]
  apply DensePoly.ext_coeff
  intro k
  rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?]
  by_cases hk : k < slots
  · have hsz : k < (((List.range slots).map
        (fun k => ((p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int)).toNat)).toArray.map
        (fun d : Nat => (d : Int) - ((2 ^ (b - 1) : Nat) : Int))).size := by simpa using hk
    rw [Array.getElem?_eq_getElem hsz]
    have hget : (((List.range slots).map
        (fun k => ((p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int)).toNat)).toArray.map
        (fun d : Nat => (d : Int) - ((2 ^ (b - 1) : Nat) : Int)))[k]
        = ((((p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int)).toNat : Nat) : Int)
          - ((2 ^ (b - 1) : Nat) : Int) := by
      simp
    rw [Option.getD_some, hget, hcast k]
    omega
  · have hsz : (((List.range slots).map
        (fun k => ((p * q).coeff k + ((2 ^ (b - 1) : Nat) : Int)).toNat)).toArray.map
        (fun d : Nat => (d : Int) - ((2 ^ (b - 1) : Nat) : Int))).size ≤ k := by
      simpa using Nat.le_of_not_gt hk
    rw [Array.getElem?_eq_none hsz, Option.getD_none]
    exact (DensePoly.coeff_eq_zero_of_size_le (p * q) (by omega)).symm

/-- The measured size cutoff: the shorter operand must store at least this many
coefficients before the substitution pays for its packing, single GMP
multiplication and unpacking. -/
@[expose]
def kroneckerSizeCutoff : Nat := 24

/-- The measured coefficient-width cutoff, in bits. Schoolbook cost per
coefficient pair steps twice as coefficients widen — about 9 ns up to 12 bits,
about 53 ns at 16, about 120 ns at 20 — and packing only amortises against the
widest regime at the size cutoff. Below 20 bits the schoolbook loop is what
runs, at any degree. -/
@[expose]
def kroneckerBitCutoff : Nat := 20

/-- Kronecker substitution with explicit cutoffs, so the kernel benchmark can
sweep them. Production uses `Hex.ZPoly.mulKronecker`, which fixes them to the
measured `Hex.ZPoly.kroneckerSizeCutoff` and `Hex.ZPoly.kroneckerBitCutoff`.

Both guards are checked before the coefficient scan is used, and the size guard
is checked before the scan is run at all, so a product that stays on the
schoolbook path for its size pays nothing for the test. -/
@[expose]
def mulKroneckerAt (sizeCutoff bitCutoff : Nat) (p q : ZPoly) : ZPoly :=
  if p.isZero || q.isZero then 0
  else if min p.size q.size < sizeCutoff then DensePoly.mulImpl p q
  else
    let width := bitLen (max (maxAbs p) (maxAbs q))
    if width < bitCutoff then DensePoly.mulImpl p q
    else
      let b := 2 * width + ceilLog2 (min p.size q.size) + 1
      let slots := p.size + q.size - 1
      DensePoly.ofCoeffs
        ((unpackAux b
          (packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size
            + constPack b ((2 ^ (b - 1) : Nat) : Int) slots).toNat
          slots).map (fun d : Nat => (d : Int) - ((2 ^ (b - 1) : Nat) : Int)))

private theorem mul_eq_zero_of_isZero (p q : ZPoly) (h : p.isZero = true ∨ q.isZero = true) :
    p * q = 0 := by
  show DensePoly.mul p q = 0
  unfold DensePoly.mul
  rcases h with h | h <;> rw [if_pos (by simp [h])]

/-- The Kronecker kernel computes the schoolbook product, at every cutoff. -/
theorem mulKroneckerAt_eq (sizeCutoff bitCutoff : Nat) (p q : ZPoly) :
    mulKroneckerAt sizeCutoff bitCutoff p q = p * q := by
  unfold mulKroneckerAt
  by_cases hz : p.isZero || q.isZero
  · rw [if_pos hz]
    exact (mul_eq_zero_of_isZero p q (by simpa using hz)).symm
  rw [if_neg hz]
  by_cases hsmall : min p.size q.size < sizeCutoff
  · rw [if_pos hsmall]
    exact (DensePoly.mul_eq_mulImpl p q).symm
  rw [if_neg hsmall]
  by_cases hnarrow : bitLen (max (maxAbs p) (maxAbs q)) < bitCutoff
  · simp only [hnarrow, ↓reduceIte]
    exact (DensePoly.mul_eq_mulImpl p q).symm
  simp only [hnarrow, ↓reduceIte]
  apply kronecker_identity p q _ _ (by omega) (DensePoly.size_mul_le p q)
  -- The runtime coefficient scan supplies the no-overlap bound.
  intro n
  have hpb : ∀ i, (p.coeff i).natAbs ≤ max (maxAbs p) (maxAbs q) := fun i =>
    Nat.le_trans (natAbs_coeff_le_maxAbs p i) (Nat.le_max_left _ _)
  have hqb : ∀ j, (q.coeff j).natAbs ≤ max (maxAbs p) (maxAbs q) := fun j =>
    Nat.le_trans (natAbs_coeff_le_maxAbs q j) (Nat.le_max_right _ _)
  have hle := natAbs_coeff_mul_le_min p q (max (maxAbs p) (maxAbs q)) hpb hqb n
  have hpow : (2 : Nat) ^ (2 * bitLen (max (maxAbs p) (maxAbs q))
        + ceilLog2 (min p.size q.size) + 1 - 1)
      = 2 ^ ceilLog2 (min p.size q.size)
        * (2 ^ bitLen (max (maxAbs p) (maxAbs q)) * 2 ^ bitLen (max (maxAbs p) (maxAbs q))) := by
    rw [show 2 * bitLen (max (maxAbs p) (maxAbs q)) + ceilLog2 (min p.size q.size) + 1 - 1
        = ceilLog2 (min p.size q.size)
          + (bitLen (max (maxAbs p) (maxAbs q)) + bitLen (max (maxAbs p) (maxAbs q))) by omega,
      Nat.pow_add, Nat.pow_add]
  have hA := lt_two_pow_bitLen (max (maxAbs p) (maxAbs q))
  have hxpos : 0 < 2 ^ bitLen (max (maxAbs p) (maxAbs q)) := Nat.two_pow_pos _
  have haa : max (maxAbs p) (maxAbs q) * max (maxAbs p) (maxAbs q)
      < 2 ^ bitLen (max (maxAbs p) (maxAbs q)) * 2 ^ bitLen (max (maxAbs p) (maxAbs q)) := by
    have h1 : max (maxAbs p) (maxAbs q) * max (maxAbs p) (maxAbs q)
        ≤ max (maxAbs p) (maxAbs q) * 2 ^ bitLen (max (maxAbs p) (maxAbs q)) :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt hA)
    have h2 : max (maxAbs p) (maxAbs q) * 2 ^ bitLen (max (maxAbs p) (maxAbs q))
        < 2 ^ bitLen (max (maxAbs p) (maxAbs q)) * 2 ^ bitLen (max (maxAbs p) (maxAbs q)) :=
      (Nat.mul_lt_mul_right hxpos).mpr hA
    omega
  have hMpos : 0 < 2 ^ ceilLog2 (min p.size q.size) := Nat.two_pow_pos _
  have h3 : min p.size q.size * (max (maxAbs p) (maxAbs q) * max (maxAbs p) (maxAbs q))
      ≤ 2 ^ ceilLog2 (min p.size q.size)
        * (max (maxAbs p) (maxAbs q) * max (maxAbs p) (maxAbs q)) :=
    Nat.mul_le_mul_right _ (le_two_pow_ceilLog2 _)
  have h4 : 2 ^ ceilLog2 (min p.size q.size)
        * (max (maxAbs p) (maxAbs q) * max (maxAbs p) (maxAbs q))
      < 2 ^ ceilLog2 (min p.size q.size)
        * (2 ^ bitLen (max (maxAbs p) (maxAbs q)) * 2 ^ bitLen (max (maxAbs p) (maxAbs q))) :=
    (Nat.mul_lt_mul_left hMpos).mpr haa
  omega

/-- Kronecker substitution at the measured cutoffs. -/
@[expose]
def mulKronecker (p q : ZPoly) : ZPoly :=
  mulKroneckerAt kroneckerSizeCutoff kroneckerBitCutoff p q

/-- The production kernel computes the schoolbook product. -/
theorem mulKronecker_eq (p q : ZPoly) : mulKronecker p q = p * q :=
  mulKroneckerAt_eq kroneckerSizeCutoff kroneckerBitCutoff p q

end ZPoly

end Hex
