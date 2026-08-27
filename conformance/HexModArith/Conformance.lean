/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModArith.HotLoop
import HexModArith.Ntt.Catalogue
import HexModArith.Ntt.Convolution
import HexModArith.Ntt.Transform
import HexModArith.Prime
import HexModArith.Ring

/-!
Core conformance checks for `HexModArith`.

Oracle: none.
Mode: always.

Covered operations:
- `ZMod64.ofNat`, `zero`, `one`, `add`, `sub`, `mul`, `pow`, `inv`, `neg`
- natural and integer casts
- natural and integer scalar multiplication
- `BarrettCtx.mulMod`
- `MontCtx.toMont`, `mulMont`, `fromMont`
- `ZMod64.NttPlan.build?`, reusable Shoup twiddle tables, bounded butterflies,
  radix-two transforms, and cyclic, ordinary, and negacyclic convolution

Covered properties:
- constructors and casts reduce representatives modulo the committed modulus
- additive, subtractive, multiplicative, exponentiation, negation, and scalar
  operations agree with the corresponding Nat-level modular contracts
- inverse candidates multiply back to one on committed coprime cases
- Barrett hot-loop multiplication agrees with the core `ZMod64`
  multiplication contract
- Montgomery round-trips preserve standard residues and Montgomery hot-loop
  multiplication agrees with the core `ZMod64` multiplication contract
- every checked result remains in canonical range through `toNat`
- NTT plans validate power-of-two lengths and exact-order roots
- the fixed NTT-prime catalogue supports its advertised length ladder and
  rejects invalid or out-of-capacity requests
- Shoup multiplication and forward/inverse butterflies preserve their residues
  while remaining in their advertised redundant ranges
- checked NTT convolution agrees with direct cyclic, zero-padded ordinary, and
  primitive-`2n` negacyclic products

Covered edge cases:
- modulus `1`
- small prime modulus `7`
- small prime modulus `5`, including a primitive fourth root
- composite modulus `15`, including the exact non-coprime inverse convention
- power-of-two modulus `16`
- small Barrett-friendly moduli `2`, `7`, and `65535`
- odd Montgomery-friendly moduli `3`, `7`, and `65537`
- large small-modulus prime `2^31 - 1` (the Mersenne prime `M31`, the largest
  admissible modulus under the `p < 2^31` bound)
- zero operands, wraparound operands, and negative integer representatives
-/

namespace Hex
namespace ZMod64

private abbrev LargeMod : Nat := 2 ^ 31 - 1
private abbrev BarrettWideMod : Nat := 65535
private abbrev MontWideMod : Nat := 65537

private instance conformanceBoundsOne : Bounds 1 := ⟨by decide, by decide⟩
private instance conformanceBoundsTwo : Bounds 2 := ⟨by decide, by decide⟩
private instance conformanceBoundsThree : Bounds 3 := ⟨by decide, by decide⟩
private instance conformanceBoundsFive : Bounds 5 := ⟨by decide, by decide⟩
private instance conformanceBoundsSeven : Bounds 7 := ⟨by decide, by decide⟩
private instance conformanceBoundsFifteen : Bounds 15 := ⟨by decide, by decide⟩
private instance conformanceBoundsSixteen : Bounds 16 := ⟨by decide, by decide⟩
private instance conformanceBoundsBarrettWide : Bounds BarrettWideMod := ⟨by decide, by decide⟩
private instance conformanceBoundsMontWide : Bounds MontWideMod := ⟨by decide, by decide⟩
private instance conformanceBoundsLarge : Bounds LargeMod := ⟨by decide, by decide⟩

section PrimeModulusAutomation

private theorem conformancePrimeSeven : Hex.Nat.Prime 7 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 7 := Nat.le_of_dvd (by decide : 0 < 7) hm
    have hcases :
        m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private instance conformancePrimeModulusSeven : PrimeModulus 7 :=
  primeModulusOfPrime conformancePrimeSeven

private theorem conformancePrimeFive : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private instance conformancePrimeModulusFive : PrimeModulus 5 :=
  primeModulusOfPrime conformancePrimeFive

example {a : ZMod64 7} (ha : a ≠ 0) : ZMod64.inv a * a = 1 := by
  grind

example (a : ZMod64 7) : a ^ 7 = a := by
  simp only [pow_prime_of_prime_modulus]

example {a b : ZMod64 7} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  grind

end PrimeModulusAutomation

/-! Reusable NTT plan validation and observations. -/

#guard (NttPlan.build? (p := 7) (n := 0) (ofNat 7 1)).isNone
#guard (NttPlan.build? (p := 7) (n := 4) (ofNat 7 6)).isNone
#guard (NttPlan.build? (p := 7) (n := 2) (ofNat 7 1)).isNone

#guard
  match NttPlan.build? (p := 7) (n := 2) (ofNat 7 6) with
  | none => false
  | some plan =>
      plan.root.toNat == 6 && plan.invRoot.toNat == 6 &&
        plan.invLength.toNat == 4 &&
        plan.forwardTwiddles.size == 2 &&
        plan.forwardTwiddles.map (fun twiddle => twiddle.value.toNat) == #[1, 6] &&
        plan.inverseTwiddles.map (fun twiddle => twiddle.value.toNat) == #[1, 6]

#guard
  match NttPlan.build? (p := 7) (n := 2) (ofNat 7 6) with
  | none => false
  | some plan =>
      match Ntt.forward? plan #[ofNat 7 3, ofNat 7 5] with
      | none => false
      | some transformed => transformed.map ZMod64.toNat == #[1, 5]

#guard
  match NttPlan.build? (p := 7) (n := 2) (ofNat 7 6) with
  | none => false
  | some plan =>
      match Ntt.forward? plan #[ofNat 7 3, ofNat 7 5] with
      | none => false
      | some transformed =>
          match Ntt.inverse? plan transformed with
          | none => false
          | some values => values.map ZMod64.toNat == #[3, 5]

#guard
  match NttPlan.build? (p := 7) (n := 2) (ofNat 7 6) with
  | none => false
  | some plan =>
      (Ntt.forward? plan #[ofNat 7 3]).isNone &&
        (Ntt.inverse? plan #[ofNat 7 3]).isNone

#guard nttPrimes.map NttPrime.modulus ==
  [167772161, 469762049, 754974721, 998244353, 1004535809, 1224736769, 2013265921]

#guard nttPrimes.map NttPrime.maxLog == [25, 26, 24, 23, 21, 24, 27]

#guard
  match nttPrimes with
  | first :: _ =>
      (first.plan? 8).isSome && (first.plan? 3).isNone &&
        (first.plan? (2 ^ 26)).isNone
  | [] => false

#guard
  match nttPrimes with
  | first :: _ =>
      first.convolution? 4 #[1, -2, 3] #[4, 5] ==
        some #[4, Int.ofNat (first.modulus - 3), 2, 15]
  | [] => false

#guard
  match nttPrimes with
  | first :: _ => (first.convolution? 3 #[1] #[1]).isNone
  | [] => false

/-- The largest advertised catalogue length is supported without constructing
its enormous twiddle array during conformance elaboration. -/
example :
    ((nttPrimes[6]'(by decide)).plan? (2 ^ 27)).isSome = true := by
  apply NttPrime.plan?_isSome_of_supported
  · decide
  · decide

private def negacyclicPlanFive? : Option (Ntt.NegacyclicPlan 5 2) :=
  match NttPlan.build? (p := 5) (n := 2) (ofNat 5 4) with
  | none => none
  | some transform =>
      if hroot : transform.root = (ofNat 5 2) ^ 2 then
        if horder : ExactOrder (ofNat 5 2) 4 then
          some { transform, twist := ofNat 5 2, twist_order := horder, root_eq := hroot }
        else none
      else none

#guard
  match NttPlan.build? (p := 5) (n := 2) (ofNat 5 4) with
  | none => false
  | some plan =>
      match Ntt.cyclic? plan #[ofNat 5 1, ofNat 5 1] #[ofNat 5 1, ofNat 5 2] with
      | none => false
      | some result => result.map ZMod64.toNat == #[3, 3]

#guard
  match NttPlan.build? (p := 5) (n := 2) (ofNat 5 4) with
  | none => false
  | some plan =>
      match Ntt.ordinary? plan #[ofNat 5 1] #[ofNat 5 1, ofNat 5 2] with
      | none => false
      | some result => result.map ZMod64.toNat == #[1, 2]

#guard
  match negacyclicPlanFive? with
  | none => false
  | some plan =>
      match Ntt.negacyclic? plan #[ofNat 5 1, ofNat 5 1] #[ofNat 5 1, ofNat 5 2] with
      | none => false
      | some result => result.map ZMod64.toNat == #[4, 3]

private def nttTwiddleSeven : NttTwiddle 7 :=
  NttTwiddle.ofValue (ofNat 7 6)

private def nttForwardSeven : NttRaw2 7 × NttRaw2 7 :=
  Ntt.forwardButterfly nttTwiddleSeven
    (NttRaw2.ofZMod (ofNat 7 3)) (NttRaw2.ofZMod (ofNat 7 5))

private def nttInverseSeven : NttRaw4 7 × NttRaw4 7 :=
  Ntt.inverseButterfly nttTwiddleSeven
    (NttRaw4.ofZMod (ofNat 7 1)) (NttRaw4.ofZMod (ofNat 7 2))

private def nttForwardImplSeven : NttRaw2 7 × NttRaw2 7 :=
  Ntt.forwardButterflyImpl nttTwiddleSeven
    (NttRaw2.ofZMod (ofNat 7 3)) (NttRaw2.ofZMod (ofNat 7 5))

private def nttInverseImplSeven : NttRaw4 7 × NttRaw4 7 :=
  Ntt.inverseButterflyImpl nttTwiddleSeven
    (NttRaw4.ofZMod (ofNat 7 1)) (NttRaw4.ofZMod (ofNat 7 2))

#guard nttTwiddleSeven.precon.toNat = 6 * UInt64.word / 7
#guard (Ntt.shoupMul nttTwiddleSeven (NttRaw4.ofZMod (ofNat 7 5))).val.toNat < 14
#guard (Ntt.shoupMul nttTwiddleSeven (NttRaw4.ofZMod (ofNat 7 5))).normalize.toNat = 2
#guard nttForwardSeven.1.val.toNat < 14
#guard nttForwardSeven.2.val.toNat < 14
#guard nttForwardSeven.1.normalize.toNat = 1
#guard nttForwardSeven.2.normalize.toNat = 2
#guard nttInverseSeven.1.val.toNat < 28
#guard nttInverseSeven.2.val.toNat < 28
#guard nttInverseSeven.1.normalize.toNat = 6
#guard nttInverseSeven.2.normalize.toNat = 3
#guard nttForwardImplSeven.1.val = nttForwardSeven.1.val
#guard nttForwardImplSeven.2.val = nttForwardSeven.2.val
#guard nttInverseImplSeven.1.val = nttInverseSeven.1.val
#guard nttInverseImplSeven.2.val = nttInverseSeven.2.val

section BasicConstructorAutomation

example (n : Nat) : (ZMod64.ofNat 7 n).toNat = n % 7 := by
  simp

example (a : ZMod64 7) : ZMod64.ofNat 7 a.toNat = a := by
  simp only [ZMod64.ofNat_toNat]

example {a b : ZMod64 7} (h : a.toNat = b.toNat) : a = b := by
  grind

example (a b : ZMod64 7) : a = b ↔ a.toNat = b.toNat := by
  grind

example (x y : Nat) : ZMod64.ofNat 7 x = ZMod64.ofNat 7 y ↔ x % 7 = y % 7 := by
  grind

example (a : ZMod64 7) : a ∈ ZMod64.values 7 := by
  simp

end BasicConstructorAutomation

private def oneOnly : ZMod64 1 := ofNat 1 37
private def a2 : ZMod64 2 := ofNat 2 1
private def b2 : ZMod64 2 := ofNat 2 1
private def a3 : ZMod64 3 := ofNat 3 2
private def b3 : ZMod64 3 := ofNat 3 2
private def a7 : ZMod64 7 := ofNat 7 3
private def b7 : ZMod64 7 := ofNat 7 5
private def nonCoprime15 : ZMod64 15 := ofNat 15 6
private def c16 : ZMod64 16 := ofNat 16 15
private def d16 : ZMod64 16 := ofNat 16 9
private def barrettWideA : ZMod64 BarrettWideMod := ofNat BarrettWideMod 65534
private def barrettWideB : ZMod64 BarrettWideMod := ofNat BarrettWideMod 32769
private def montWideA : ZMod64 MontWideMod := ofNat MontWideMod 65536
private def montWideB : ZMod64 MontWideMod := ofNat MontWideMod 32771
private def wideA : ZMod64 LargeMod := ofNat LargeMod (2 ^ 31 - 2)
private def wideB : ZMod64 LargeMod := ofNat LargeMod (2 ^ 31 - 17)

private def barrettCtx2 : Hex.BarrettCtx 2 :=
  Hex.BarrettCtx.ofModulus (p := 2) (by decide) (by decide)

private def barrettCtx7 : Hex.BarrettCtx 7 :=
  Hex.BarrettCtx.ofModulus (p := 7) (by decide) (by decide)

private def barrettCtxWide : Hex.BarrettCtx BarrettWideMod :=
  Hex.BarrettCtx.ofModulus (p := BarrettWideMod) (by decide) (by decide)

private def montCtx3 : Hex.MontCtx 3 :=
  Hex.MontCtx.ofOddModulus (by decide) (by decide)

private def montCtx7 : Hex.MontCtx 7 :=
  Hex.MontCtx.ofOddModulus (by decide) (by decide)

private def montCtxWide : Hex.MontCtx MontWideMod :=
  Hex.MontCtx.ofOddModulus (by decide) (by decide)

#guard barrettCtx2.modulus.toNat = 2
#guard barrettCtx7.modulus.toNat = 7
#guard barrettCtxWide.modulus.toNat = BarrettWideMod
#guard barrettCtx7.toUInt64Ctx.pinv = UInt64.ofNat (barrettRadix / 7)
#guard montCtx3.modulus.toNat = 3
#guard montCtx7.modulus.toNat = 7
#guard montCtxWide.modulus.toNat = MontWideMod
#guard (decide (montCtx7.modulus % 2 = 1))

#guard (ofNat 7 17).toNat = 17 % 7
#guard (ofNat 1 42).toNat = 42 % 1
#guard (ofNat LargeMod (LargeMod + 12345)).toNat = (LargeMod + 12345) % LargeMod

#guard (0 : ZMod64 7).toNat = 0 % 7
#guard (0 : ZMod64 1).toNat = 0 % 1
#guard (0 : ZMod64 LargeMod).toNat = 0 % LargeMod

#guard (1 : ZMod64 7).toNat = 1 % 7
#guard (1 : ZMod64 1).toNat = 1 % 1
#guard (1 : ZMod64 LargeMod).toNat = 1 % LargeMod

#guard (a7 + b7).toNat = (a7.toNat + b7.toNat) % 7
#guard (oneOnly + oneOnly).toNat = (oneOnly.toNat + oneOnly.toNat) % 1
#guard (wideA + wideB).toNat = (wideA.toNat + wideB.toNat) % LargeMod

#guard (a7 - b7).toNat = (a7.toNat + (7 - b7.toNat)) % 7
#guard (oneOnly - oneOnly).toNat = (oneOnly.toNat + (1 - oneOnly.toNat)) % 1
#guard (wideA - wideB).toNat = (wideA.toNat + (LargeMod - wideB.toNat)) % LargeMod

#guard (a7 * b7).toNat = (a7.toNat * b7.toNat) % 7
#guard (oneOnly * oneOnly).toNat = (oneOnly.toNat * oneOnly.toNat) % 1
#guard (wideA * wideB).toNat = (wideA.toNat * wideB.toNat) % LargeMod

#guard (barrettCtx2.mulMod a2 b2).toNat = (a2 * b2).toNat
#guard (barrettCtx7.mulMod a7 b7).toNat = (a7 * b7).toNat
#guard (barrettCtxWide.mulMod barrettWideA barrettWideB).toNat =
  (barrettWideA.toNat * barrettWideB.toNat) % BarrettWideMod

#guard (montCtx3.fromMont (montCtx3.toMont a3)).toNat = a3.toNat
#guard (montCtx7.fromMont (montCtx7.toMont a7)).toNat = a7.toNat
#guard (montCtxWide.fromMont (montCtxWide.toMont montWideA)).toNat = montWideA.toNat

#guard (montCtx3.fromMont (montCtx3.mulMont (montCtx3.toMont a3) (montCtx3.toMont b3))).toNat =
  (a3 * b3).toNat
#guard (montCtx7.fromMont (montCtx7.mulMont (montCtx7.toMont a7) (montCtx7.toMont b7))).toNat =
  (a7 * b7).toNat
#guard (montCtxWide.fromMont
    (montCtxWide.mulMont (montCtxWide.toMont montWideA) (montCtxWide.toMont montWideB))).toNat =
  (montWideA.toNat * montWideB.toNat) % MontWideMod

#guard (a7 ^ 5).toNat = (a7.toNat ^ 5) % 7
#guard (oneOnly ^ 0).toNat = (oneOnly.toNat ^ 0) % 1
#guard (c16 ^ 3).toNat = (c16.toNat ^ 3) % 16

#guard (inv a7 * a7).toNat = 1 % 7
#guard (inv oneOnly * oneOnly).toNat = 1 % 1
#guard (inv nonCoprime15).toNat = 13
#guard (List.range 15).all fun n =>
  let a : ZMod64 15 := ofNat 15 n
  (inv a * a).toNat == Nat.gcd n 15 % 15
#guard (inv wideA * wideA).toNat = 1 % LargeMod

/-- The logical reference separately pins the non-coprime cofactor convention. -/
example : (HexArith.Int.extGcd 6 15).2.1 % 15 = 13 := by
  simp [HexArith.Int.extGcd, Hex.pureIntExtGcd, Hex.pureIntExtGcd.go.eq_def]

#guard (-a7).toNat = (7 - a7.toNat) % 7
#guard (-oneOnly).toNat = (1 - oneOnly.toNat) % 1
#guard (-c16).toNat = (16 - c16.toNat) % 16

#guard ((19 : Nat) : ZMod64 7).toNat = 19 % 7
#guard ((8 : Nat) : ZMod64 1).toNat = 8 % 1
#guard ((LargeMod + 99 : Nat) : ZMod64 LargeMod).toNat = (LargeMod + 99) % LargeMod

#guard (ZMod64.intCast 7 (-3)).toNat = (7 - 3) % 7
#guard (ZMod64.intCast 1 (-3)).toNat = (1 - 0) % 1
#guard (ZMod64.intCast LargeMod (-5)).toNat = (LargeMod - 5) % LargeMod

#guard (ZMod64.nsmul 4 a7).toNat = (4 * a7.toNat) % 7
#guard (ZMod64.nsmul 9 oneOnly).toNat = (9 * oneOnly.toNat) % 1
#guard (ZMod64.nsmul 3 wideA).toNat = (3 * wideA.toNat) % LargeMod

#guard (ZMod64.zsmul 4 a7).toNat = (4 * a7.toNat) % 7
#guard (ZMod64.zsmul (-3) a7).toNat = (7 - ((3 * a7.toNat) % 7)) % 7
#guard (ZMod64.zsmul (-2) wideA).toNat = (LargeMod - ((2 * wideA.toNat) % LargeMod)) % LargeMod

#guard (a7 + b7).toNat < 7
#guard (c16 * d16).toNat < 16
#guard (wideA ^ 4).toNat < LargeMod

end ZMod64
end Hex
