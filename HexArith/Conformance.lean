import HexArith.ExtGcd
import HexArith.Barrett.Context
import HexArith.Montgomery.Context
import HexArith.UInt64.Wide

/-!
Core conformance checks for the first `hex-arith` Phase 3 slice.

Oracle: Lean built-in `Nat` / `Int` arithmetic
Mode: always
Covered operations:
- `HexArith.extGcd` on `Nat`
- `HexArith.Int.extGcd`
- `HexArith.UInt64.extGcd`
- `UInt64.mulHi`
- `UInt64.mulFull`
- `UInt64.addCarry`
- `UInt64.subBorrow`
- `BarrettCtx.mulMod`
- `barrettReduce`
- `MontCtx.toMont`
- `MontCtx.fromMont`
- `MontCtx.mulMont`
- `HexArith.powMod`
Covered properties:
- each extended-GCD API returns the same gcd as Lean's built-in arithmetic on committed fixtures
- each extended-GCD API returns Bezout coefficients satisfying the advertised identity
- `mulHi` and `mulFull` reconstruct the committed Nat-level products
- `addCarry` and `subBorrow` satisfy the committed one-word reconstruction laws
- `BarrettCtx.mulMod` agrees with ordinary modular multiplication on committed residues
- `barrettReduce` follows the corrective-subtraction branch and still returns `T % p`
- Montgomery round-trips preserve reduced residues and Montgomery multiplication agrees with `Nat`-level modular products
- `HexArith.powMod` agrees with ordinary modular exponentiation on committed fixtures
Covered edge cases:
- zero-left and zero-right extended-GCD inputs
- signed extended-GCD inputs with mixed signs
- wide-word products crossing the `2^64` boundary
- add-with-carry and subtract-with-borrow cases with and without overflow
- Barrett multiplication at the `p < 2^32` boundary
- the Montgomery modulus-`1` degenerate case
- a near-`2^64` odd Montgomery modulus with near-modulus residues
- `powMod` exponent zero, base larger than the modulus, even-modulus fallback, and large-`Nat` fallback
-/

namespace HexArith

private def wordBase : Nat := UInt64.word
private def maxWord : UInt64 := UInt64.ofNat (wordBase - 1)

/-- info: (6, 1, -2) -/
#guard_msgs in #eval HexArith.extGcd 30 12

#guard let (g, _, _) := HexArith.extGcd 30 12
  g = Nat.gcd 30 12
#guard let (g, s, t) := HexArith.extGcd 30 12
  s * 30 + t * 12 = g

#guard let (g, _, _) := HexArith.extGcd 0 37
  g = Nat.gcd 0 37
#guard let (g, s, t) := HexArith.extGcd 0 37
  s * 0 + t * 37 = g

#guard let (g, _, _) := HexArith.extGcd 144 89
  g = Nat.gcd 144 89
#guard let (g, s, t) := HexArith.extGcd 144 89
  s * 144 + t * 89 = g

/-- info: (6, 1, -2) -/
#guard_msgs in #eval HexArith.Int.extGcd 30 12

#guard let (g, _, _) := HexArith.Int.extGcd 30 12
  g = Int.gcd 30 12
#guard let (g, s, t) := HexArith.Int.extGcd 30 12
  s * 30 + t * 12 = Int.ofNat g

#guard let (g, _, _) := HexArith.Int.extGcd 37 0
  g = Int.gcd 37 0
#guard let (g, s, t) := HexArith.Int.extGcd 37 0
  s * 37 + t * 0 = Int.ofNat g

#guard let (g, _, _) := HexArith.Int.extGcd (-144) 89
  g = Int.gcd (-144) 89
#guard let (g, s, t) := HexArith.Int.extGcd (-144) 89
  s * (-144) + t * 89 = Int.ofNat g

/-- info: (6, 1, -2) -/
#guard_msgs in #eval HexArith.UInt64.extGcd 30 12

#guard let (g, _, _) := HexArith.UInt64.extGcd 30 12
  g.toNat = Nat.gcd 30 12
#guard let (g, s, t) := HexArith.UInt64.extGcd 30 12
  s * 30 + t * 12 = Int.ofNat g.toNat

#guard let (g, _, _) := HexArith.UInt64.extGcd 0 37
  g.toNat = Nat.gcd 0 37
#guard let (g, s, t) := HexArith.UInt64.extGcd 0 37
  s * 0 + t * 37 = Int.ofNat g.toNat

#guard let a := UInt64.ofNat (2 ^ 32 + 15)
  let b := UInt64.ofNat (2 ^ 31 - 1)
  let (g, _, _) := HexArith.UInt64.extGcd a b
  g.toNat = Nat.gcd a.toNat b.toNat
#guard let a := UInt64.ofNat (2 ^ 32 + 15)
  let b := UInt64.ofNat (2 ^ 31 - 1)
  let (g, s, t) := HexArith.UInt64.extGcd a b
  s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat

namespace ProofMode

example (a b : Nat) :
    (let (g, s, t) := HexArith.extGcd a b;
      g = Nat.gcd a b ∧ s * a + t * b = g) := by
  simp

example :
    (let (g, s, t) := HexArith.Int.extGcd (-144) 89;
      g = Int.gcd (-144) 89 ∧ s * (-144) + t * 89 = g) := by
  simp

example (a b : Nat) :
    (let (g, s, t) := HexArith.Int.extGcd (Int.ofNat a) (Int.ofNat b);
      g = Nat.gcd a b ∧ s * Int.ofNat a + t * Int.ofNat b = g) := by
  simp

example (a b : UInt64) :
    (let (g, s, t) := HexArith.UInt64.extGcd a b;
      g.toNat = Nat.gcd a.toNat b.toNat ∧
        s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat) := by
  grind [HexArith.UInt64.extGcd_spec]

end ProofMode

/-- info: 2 -/
#guard_msgs in #eval UInt64.mulHi (UInt64.ofNat (2 ^ 63)) 4

#guard UInt64.mulHi 0 17 = 0
#guard UInt64.mulHi (UInt64.ofNat (2 ^ 63)) 4 = UInt64.ofNat 2
#guard let a := maxWord
  let b := maxWord
  (UInt64.mulHi a b).toNat * wordBase + (a * b).toNat = a.toNat * b.toNat

/-- info: (2, 0) -/
#guard_msgs in #eval UInt64.mulFull (UInt64.ofNat (2 ^ 63)) 4

#guard let (hi, lo) := UInt64.mulFull 0 17
  hi = 0 ∧ lo = 0
#guard let (hi, lo) := UInt64.mulFull (UInt64.ofNat (2 ^ 63)) 4
  hi = UInt64.ofNat 2 ∧ lo = 0
#guard let a := maxWord
  let b := UInt64.ofNat (2 ^ 32 + 1)
  let (hi, lo) := UInt64.mulFull a b
  hi.toNat * wordBase + lo.toNat = a.toNat * b.toNat

example (a b : UInt64) :
    (UInt64.mulFull a b).2.toNat + (UInt64.mulFull a b).1.toNat * UInt64.word =
      a.toNat * b.toNat := by
  have h := UInt64.mulFull_snd_add_fst a b
  grind only

/-- info: (0, true) -/
#guard_msgs in #eval UInt64.addCarry maxWord 1 false

#guard let (s, cout) := UInt64.addCarry 0 0 false
  s = 0 ∧ cout = false
#guard let (s, cout) := UInt64.addCarry maxWord 1 false
  s = 0 ∧ cout = true
#guard let (s, cout) := UInt64.addCarry maxWord maxWord true
  s = maxWord ∧ cout = true
#guard let a := UInt64.ofNat (2 ^ 63)
  let b := UInt64.ofNat (2 ^ 63)
  let (s, cout) := UInt64.addCarry a b false
  s.toNat + cout.toNat * wordBase = a.toNat + b.toNat

example (a b : UInt64) (cin : Bool) :
    (UInt64.addCarry a b cin).1.toNat +
        (UInt64.addCarry a b cin).2.toNat * UInt64.word =
      a.toNat + b.toNat + cin.toNat := by
  have h := UInt64.toNat_addCarry_proj a b cin
  grind only

/-- info: (2, false) -/
#guard_msgs in #eval UInt64.subBorrow 5 3 false

#guard let (d, bout) := UInt64.subBorrow 5 3 false
  d = 2 ∧ bout = false
#guard let (d, bout) := UInt64.subBorrow 0 1 false
  d = maxWord ∧ bout = true
#guard let (d, bout) := UInt64.subBorrow 0 0 true
  d = maxWord ∧ bout = true
#guard let a := UInt64.ofNat (2 ^ 63)
  let b := UInt64.ofNat (2 ^ 63 - 1)
  let (d, bout) := UInt64.subBorrow a b true
  d.toNat + (b.toNat + 1) = a.toNat + bout.toNat * wordBase

example (a b : UInt64) (bin : Bool) :
    (UInt64.subBorrow a b bin).1.toNat + (b.toNat + bin.toNat) =
      a.toNat + (UInt64.subBorrow a b bin).2.toNat * UInt64.word := by
  have h := UInt64.toNat_subBorrow_proj a b bin
  grind only

/-- info: 4 -/
#guard_msgs in #eval let p := UInt64.ofNat 17
  let ctx := BarrettCtx.mk p (by decide) (by decide)
  (ctx.mulMod 5 11).toNat

#guard let p := UInt64.ofNat (2 ^ 32 - 5)
  let ctx := BarrettCtx.mk p (by decide) (by decide)
  let a := UInt64.ofNat (2 ^ 32 - 6)
  let b := UInt64.ofNat (2 ^ 32 - 7)
  (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat

#guard let p := UInt64.ofNat 65521
  let ctx := BarrettCtx.mk p (by decide) (by decide)
  let a := UInt64.ofNat 65520
  let b := UInt64.ofNat 65520
  (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat

#guard let p := UInt64.ofNat 257
  let ctx := BarrettCtx.mk p (by decide) (by decide)
  let T := UInt64.ofNat 64250
  let q := UInt64.mulHi T ctx.pinv
  let r := T - q * p
  r ≥ p ∧ (barrettReduce ctx T).toNat = T.toNat % p.toNat

/-- info: (17, 13, 61) -/
#guard_msgs in #eval let p := UInt64.ofNat 97
  let ctx := MontCtx.mk p (by decide)
  let a := UInt64.ofNat 13
  let b := UInt64.ofNat 42
  ((ctx.toMont a).toNat,
    (ctx.fromMont (ctx.toMont a)).toNat,
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat)

#guard let p := UInt64.ofNat 1
  let ctx := MontCtx.mk p (by decide)
  let z := (0 : UInt64)
  ctx.toMont z = 0 ∧
    ctx.fromMont (ctx.toMont z) = 0 ∧
    (ctx.fromMont (ctx.mulMont (ctx.toMont z) (ctx.toMont z))).toNat = 0

#guard let p := UInt64.ofNat 17
  let ctx := MontCtx.mk p (by decide)
  let a := UInt64.ofNat 5
  let b := UInt64.ofNat 11
  ctx.fromMont (ctx.toMont a) = a ∧
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat

#guard let p := UInt64.ofNat 18446744073709551557
  let ctx := MontCtx.mk p (by decide)
  let a := UInt64.ofNat 18446744073709551556
  let b := UInt64.ofNat 18446744073709551555
  ctx.fromMont (ctx.toMont a) = a ∧
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat

#guard HexArith.powMod 1234 13 97 = 1234 ^ 13 % 97
#guard HexArith.powMod 123456 0 64 = 123456 ^ 0 % 64
#guard let p := wordBase + 59
  HexArith.powMod (p + 123) 5 p = (p + 123) ^ 5 % p
#guard HexArith.powMod 42 99 1 = 42 ^ 99 % 1

end HexArith
