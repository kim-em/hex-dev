import Std

/-!
Wide-word helper operations for `UInt64`.

This module provides the executable logical definitions of fused and projected
`UInt64 × UInt64` products together with add-with-carry and
subtract-with-borrow operations. Later Barrett and Montgomery reductions use
these operations as the only interface to machine-word overflow behavior.
-/
namespace UInt64

/-- The radix for a single `UInt64` word. -/
def word : Nat := 2 ^ 64

/-- The `UInt64` word radix is positive. -/
theorem word_pos : 0 < word := by
  simp [word]

/-- Every `UInt64` value is strictly below the word radix. -/
theorem toNat_lt_word (a : UInt64) : a.toNat < word := by
  simpa [word, UInt64.size] using UInt64.toNat_lt_size a

/-- `UInt64.ofNat` reduces Nat values modulo the word radix. -/
theorem toNat_ofNat_mod_word (n : Nat) :
    (UInt64.ofNat n).toNat = n % word := by
  simp [word]

/-- The high 64 bits of the product `a * b`, viewed in radix `2^64`. -/
@[extern "lean_hex_uint64_mul_hi"]
def mulHi (a b : UInt64) : UInt64 :=
  .ofNat (a.toNat * b.toNat / word)

/-- The full `UInt64 × UInt64` product, split into high and low radix-`2^64` words. -/
@[extern "lean_hex_uint64_mul_full"]
def mulFull (a b : UInt64) : UInt64 × UInt64 :=
  let p := a.toNat * b.toNat
  (.ofNat (p / word), .ofNat p)

/--
Add `a`, `b`, and an incoming carry bit, returning the wrapped low word and the
outgoing carry bit.
-/
@[extern "lean_hex_uint64_add_carry"]
def addCarry (a b : UInt64) (cin : Bool) : UInt64 × Bool :=
  let total := a.toNat + b.toNat + cin.toNat
  (.ofNat total, decide (word ≤ total))

/--
Subtract `b` and an incoming borrow bit from `a`, returning the wrapped low
word and the outgoing borrow bit.
-/
@[extern "lean_hex_uint64_sub_borrow"]
def subBorrow (a b : UInt64) (bin : Bool) : UInt64 × Bool :=
  let rhs := b.toNat + bin.toNat
  if rhs ≤ a.toNat then
    (.ofNat (a.toNat - rhs), false)
  else
    (.ofNat (word + a.toNat - rhs), true)

/-- Low-word projection of `addCarry` as Nat reduction modulo `2^64`. -/
@[simp]
theorem toNat_addCarry_fst (a b : UInt64) (cin : Bool) :
    (addCarry a b cin).1.toNat = (a.toNat + b.toNat + cin.toNat) % word := by
  simp [addCarry, word]

/-- The outgoing carry bit of `addCarry` is set exactly when the exact sum overflows. -/
theorem addCarry_snd (a b : UInt64) (cin : Bool) :
    (addCarry a b cin).2 = decide (word ≤ a.toNat + b.toNat + cin.toNat) := by
  simp [addCarry]

/-- The outgoing carry bit is true exactly when exact add-with-carry overflows. -/
theorem addCarry_snd_eq_true (a b : UInt64) (cin : Bool) :
    (addCarry a b cin).2 = true ↔ word ≤ a.toNat + b.toNat + cin.toNat := by
  rw [addCarry_snd]
  simp

/-- The outgoing carry bit is false exactly when exact add-with-carry fits in one word. -/
theorem addCarry_snd_eq_false (a b : UInt64) (cin : Bool) :
    (addCarry a b cin).2 = false ↔ a.toNat + b.toNat + cin.toNat < word := by
  rw [addCarry_snd]
  by_cases h : word ≤ a.toNat + b.toNat + cin.toNat
  · simp [h]
  · have hlt : a.toNat + b.toNat + cin.toNat < word := by omega
    simp [h, hlt]

/-- If exact add-with-carry does not overflow, `addCarry` returns the exact low word. -/
theorem addCarry_eq_of_no_overflow (a b : UInt64) (cin : Bool)
    (h : a.toNat + b.toNat + cin.toNat < word) :
    addCarry a b cin = (UInt64.ofNat (a.toNat + b.toNat + cin.toNat), false) := by
  have hnot : ¬ word ≤ a.toNat + b.toNat + cin.toNat := by omega
  simp [addCarry, hnot]

/-- If exact add-with-carry does not overflow, the low word is the exact sum. -/
theorem addCarry_fst_eq_of_no_overflow (a b : UInt64) (cin : Bool)
    (h : a.toNat + b.toNat + cin.toNat < word) :
    (addCarry a b cin).1 = UInt64.ofNat (a.toNat + b.toNat + cin.toNat) := by
  simpa using congrArg Prod.fst (addCarry_eq_of_no_overflow a b cin h)

/-- If exact add-with-carry overflows, `addCarry` returns the wrapped low word and carry bit. -/
theorem addCarry_eq_of_overflow (a b : UInt64) (cin : Bool)
    (h : word ≤ a.toNat + b.toNat + cin.toNat) :
    addCarry a b cin = (UInt64.ofNat (a.toNat + b.toNat + cin.toNat), true) := by
  simp [addCarry, h]

/-- If exact add-with-carry overflows, the low word is the wrapped exact sum. -/
theorem addCarry_fst_eq_of_overflow (a b : UInt64) (cin : Bool)
    (h : word ≤ a.toNat + b.toNat + cin.toNat) :
    (addCarry a b cin).1 = UInt64.ofNat (a.toNat + b.toNat + cin.toNat) := by
  simpa using congrArg Prod.fst (addCarry_eq_of_overflow a b cin h)

/-- Low-word projection of `subBorrow` after one-word wrapping. -/
@[simp]
theorem toNat_subBorrow_fst (a b : UInt64) (bin : Bool) :
    (subBorrow a b bin).1.toNat =
      (word + a.toNat - (b.toNat + bin.toNat)) % word := by
  let rhs := b.toNat + bin.toNat
  have ha : a.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size a
  have hb : b.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size b
  have hbin : bin.toNat ≤ 1 := by
    cases bin <;> decide
  by_cases hle : rhs ≤ a.toNat
  · have hdiff_lt : a.toNat - rhs < word := by omega
    have hdiff_lt' : a.toNat - rhs < 2 ^ 64 := by
      simpa [word] using hdiff_lt
    have hwrap_eq : word + a.toNat - rhs = word + (a.toNat - rhs) := by omega
    have hmod : (word + a.toNat - rhs) % word = a.toNat - rhs := by
      rw [hwrap_eq, Nat.add_mod_left, Nat.mod_eq_of_lt hdiff_lt]
    dsimp [subBorrow]
    simp [rhs, hle]
    rw [Nat.mod_eq_of_lt hdiff_lt']
    simpa [rhs] using hmod.symm
  · have hwrap_lt : word + a.toNat - rhs < word := by omega
    have hwrap_lt' : word + a.toNat - rhs < 2 ^ 64 := by
      simpa [word] using hwrap_lt
    have hmod : (word + a.toNat - rhs) % word = word + a.toNat - rhs :=
      Nat.mod_eq_of_lt hwrap_lt
    dsimp [subBorrow]
    simp [rhs, hle]
    rw [Nat.mod_eq_of_lt hwrap_lt']
    simpa [rhs] using hmod.symm

/-- The outgoing borrow bit of `subBorrow` is set exactly when the subtrahend is larger. -/
theorem subBorrow_snd (a b : UInt64) (bin : Bool) :
    (subBorrow a b bin).2 = decide (a.toNat < b.toNat + bin.toNat) := by
  by_cases hle : b.toNat + bin.toNat ≤ a.toNat
  · have hnot : ¬ a.toNat < b.toNat + bin.toNat := by omega
    simp [subBorrow, hle, hnot]
  · have hlt : a.toNat < b.toNat + bin.toNat := by omega
    simp [subBorrow, hle, hlt]

/-- The outgoing borrow bit is true exactly when the subtrahend is larger. -/
theorem subBorrow_snd_eq_true (a b : UInt64) (bin : Bool) :
    (subBorrow a b bin).2 = true ↔ a.toNat < b.toNat + bin.toNat := by
  rw [subBorrow_snd]
  simp

/-- The outgoing borrow bit is false exactly when subtraction does not borrow. -/
theorem subBorrow_snd_eq_false (a b : UInt64) (bin : Bool) :
    (subBorrow a b bin).2 = false ↔ b.toNat + bin.toNat ≤ a.toNat := by
  rw [subBorrow_snd]
  by_cases h : a.toNat < b.toNat + bin.toNat
  · simp [h]
  · have hle : b.toNat + bin.toNat ≤ a.toNat := by omega
    simp [h, hle]

/-- If subtraction does not borrow, `subBorrow` returns the exact difference. -/
theorem subBorrow_eq_of_no_borrow (a b : UInt64) (bin : Bool)
    (h : b.toNat + bin.toNat ≤ a.toNat) :
    subBorrow a b bin = (UInt64.ofNat (a.toNat - (b.toNat + bin.toNat)), false) := by
  simp [subBorrow, h]

/-- If subtraction does not borrow, the low word is the exact difference. -/
theorem subBorrow_fst_eq_of_no_borrow (a b : UInt64) (bin : Bool)
    (h : b.toNat + bin.toNat ≤ a.toNat) :
    (subBorrow a b bin).1 =
      UInt64.ofNat (a.toNat - (b.toNat + bin.toNat)) := by
  simpa using congrArg Prod.fst (subBorrow_eq_of_no_borrow a b bin h)

/-- If subtraction borrows, `subBorrow` returns the one-word wrapped difference. -/
theorem subBorrow_eq_of_borrow (a b : UInt64) (bin : Bool)
    (h : a.toNat < b.toNat + bin.toNat) :
    subBorrow a b bin =
      (UInt64.ofNat (word + a.toNat - (b.toNat + bin.toNat)), true) := by
  have hnot : ¬ b.toNat + bin.toNat ≤ a.toNat := by omega
  simp [subBorrow, hnot]

/-- If subtraction borrows, the low word is the wrapped difference. -/
theorem subBorrow_fst_eq_of_borrow (a b : UInt64) (bin : Bool)
    (h : a.toNat < b.toNat + bin.toNat) :
    (subBorrow a b bin).1 =
      UInt64.ofNat (word + a.toNat - (b.toNat + bin.toNat)) := by
  simpa using congrArg Prod.fst (subBorrow_eq_of_borrow a b bin h)

private theorem toNat_ofNat_quot_mul_lt_word (a b : UInt64) :
    (UInt64.ofNat (a.toNat * b.toNat / word)).toNat =
      a.toNat * b.toNat / word := by
  have ha : a.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size a
  have hb : b.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size b
  have hprod : a.toNat * b.toNat < word * word := Nat.mul_lt_mul'' ha hb
  have hquot : a.toNat * b.toNat / word < word := Nat.div_lt_of_lt_mul hprod
  simpa [UInt64.toNat_ofNat, word] using Nat.mod_eq_of_lt hquot

/-- `mulHi` agrees with Nat-level division by `2^64`. -/
theorem toNat_mulHi (a b : UInt64) :
    (mulHi a b).toNat = a.toNat * b.toNat / word := by
  simpa [mulHi] using toNat_ofNat_quot_mul_lt_word a b

/-- `mulFull` agrees with Nat-level division and remainder by `2^64`. -/
theorem toNat_mulFull (a b : UInt64) :
    let (hi, lo) := mulFull a b
    hi.toNat = a.toNat * b.toNat / word ∧
    lo.toNat = a.toNat * b.toNat % word := by
  dsimp [mulFull]
  constructor
  · exact toNat_ofNat_quot_mul_lt_word a b
  · simp [word]

/--
`mulFull` returns the same high word as `mulHi` and the same low word as
ordinary wrapped `UInt64` multiplication, while computing both halves in one
extern call.
-/
theorem mulFull_eq_mulHi_mul (a b : UInt64) :
    mulFull a b = (mulHi a b, a * b) := by
  cases h : mulFull a b with
  | mk hi lo =>
      have hfull := toNat_mulFull a b
      simp [h] at hfull
      apply Prod.ext
      · apply UInt64.toNat_inj.mp
        rw [toNat_mulHi]
        exact hfull.1
      · apply UInt64.toNat_inj.mp
        simpa [UInt64.toNat_mul, word] using hfull.2

/-- The high component of `mulFull` is the same value returned by `mulHi`. -/
@[simp]
theorem mulFull_fst_eq_mulHi (a b : UInt64) :
    (mulFull a b).1 = mulHi a b := by
  simpa using congrArg Prod.fst (mulFull_eq_mulHi_mul a b)

/-- The low component of `mulFull` is ordinary wrapped `UInt64` multiplication. -/
@[simp]
theorem mulFull_snd_eq_mul (a b : UInt64) :
    (mulFull a b).2 = a * b := by
  simpa using congrArg Prod.snd (mulFull_eq_mulHi_mul a b)

/-- Nat-level view of the high component returned by `mulFull`. -/
@[simp]
theorem toNat_mulFull_fst (a b : UInt64) :
    (mulFull a b).1.toNat = a.toNat * b.toNat / word := by
  rw [mulFull_fst_eq_mulHi, toNat_mulHi]

/-- Nat-level view of the low component returned by `mulFull`. -/
@[simp]
theorem toNat_mulFull_snd (a b : UInt64) :
    (mulFull a b).2.toNat = a.toNat * b.toNat % word := by
  simp [mulFull_snd_eq_mul, UInt64.toNat_mul, word]

/--
Splitting the product into high and low words reconstructs the original
Nat-level product.
-/
theorem mulHi_mulLo (a b : UInt64) :
    (mulHi a b).toNat * word + (a * b).toNat = a.toNat * b.toNat := by
  have h := Nat.div_add_mod (a.toNat * b.toNat) word
  simpa [toNat_mulHi, UInt64.toNat_mul, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

/--
Low-word-first product reconstruction for callers that encode a two-word value
as `lo + hi * word`.
-/
theorem mulLo_add_mulHi (a b : UInt64) :
    (a * b).toNat + (mulHi a b).toNat * word = a.toNat * b.toNat := by
  rw [Nat.add_comm]
  exact mulHi_mulLo a b

/--
The components returned by `mulFull` reconstruct the original Nat-level
product in low-word-first order.
-/
theorem mulFull_snd_add_fst (a b : UInt64) :
    (mulFull a b).2.toNat + (mulFull a b).1.toNat * word =
      a.toNat * b.toNat := by
  rw [mulFull_snd_eq_mul, mulFull_fst_eq_mulHi]
  exact mulLo_add_mulHi a b

/--
`addCarry` represents exact Nat addition split into a low word and a carry bit.
-/
theorem toNat_addCarry (a b : UInt64) (cin : Bool) :
    let (s, cout) := addCarry a b cin
    s.toNat + cout.toNat * word = a.toNat + b.toNat + cin.toNat := by
  let total := a.toNat + b.toNat + cin.toNat
  have ha : a.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size a
  have hb : b.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size b
  have htotal_lt : total < 2 * word := by
    cases cin <;> simp [total] at * <;> omega
  dsimp [addCarry]
  change (UInt64.ofNat total).toNat +
      (decide (word ≤ total)).toNat * word = total
  by_cases hcarry : word ≤ total
  · have hdiv : total / word = 1 :=
      Nat.div_eq_of_lt_le (by simpa using hcarry) (by omega)
    have hsplit := Nat.mod_add_div total word
    rw [toNat_ofNat_mod_word,
      show (decide (word ≤ total)).toNat = 1 by simp [hcarry]]
    rw [hdiv] at hsplit
    omega
  · have htotal_word : total < word := by omega
    rw [toNat_ofNat_mod_word,
      show (decide (word ≤ total)).toNat = 0 by simp [hcarry],
      Nat.mod_eq_of_lt htotal_word]
    omega

/--
`subBorrow` represents exact subtraction with borrow after one-word wrapping.
-/
theorem toNat_subBorrow (a b : UInt64) (bin : Bool) :
    let (d, bout) := subBorrow a b bin
    d.toNat + (b.toNat + bin.toNat) = a.toNat + bout.toNat * word := by
  have ha : a.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size a
  have hb : b.toNat < word := by
    simpa [word, UInt64.size] using UInt64.toNat_lt_size b
  by_cases hle : b.toNat + bin.toNat ≤ a.toNat
  · have hdiff_lt' : a.toNat - (b.toNat + bin.toNat) < 2 ^ 64 := by
      have : a.toNat - (b.toNat + bin.toNat) < word := by omega
      simpa [word] using this
    have hsub_eq :
        a.toNat - (b.toNat + bin.toNat) + (b.toNat + bin.toNat) =
          a.toNat :=
      Nat.sub_add_cancel hle
    dsimp [subBorrow]
    simp [hle]
    rw [Nat.mod_eq_of_lt hdiff_lt']
    exact hsub_eq
  · have hwrap_lt' :
        word + a.toNat - (b.toNat + bin.toNat) < 2 ^ 64 := by
      have : word + a.toNat - (b.toNat + bin.toNat) < word := by
        cases bin <;> simp at * <;> omega
      simpa [word] using this
    have hwrap_eq :
        word + a.toNat - (b.toNat + bin.toNat) + (b.toNat + bin.toNat) =
          a.toNat + word := by
      cases bin <;> simp at * <;> omega
    dsimp [subBorrow]
    simp [hle]
    rw [Nat.mod_eq_of_lt hwrap_lt']
    exact hwrap_eq

end UInt64
