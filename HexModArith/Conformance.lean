import HexModArith.HotLoop
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

Covered edge cases:
- modulus `1`
- small prime modulus `7`
- power-of-two modulus `16`
- small Barrett-friendly moduli `2`, `7`, and `65535`
- odd Montgomery-friendly moduli `3`, `7`, and `65537`
- large word-sized modulus `2^63 + 29`
- zero operands, wraparound operands, and negative integer representatives
-/

namespace Hex
namespace ZMod64

private abbrev LargeMod : Nat := 2 ^ 63 + 29
private abbrev BarrettWideMod : Nat := 65535
private abbrev MontWideMod : Nat := 65537

private instance conformanceBoundsOne : Bounds 1 := ⟨by decide, by decide⟩
private instance conformanceBoundsTwo : Bounds 2 := ⟨by decide, by decide⟩
private instance conformanceBoundsThree : Bounds 3 := ⟨by decide, by decide⟩
private instance conformanceBoundsSeven : Bounds 7 := ⟨by decide, by decide⟩
private instance conformanceBoundsSixteen : Bounds 16 := ⟨by decide, by decide⟩
private instance conformanceBoundsBarrettWide : Bounds BarrettWideMod := ⟨by decide, by decide⟩
private instance conformanceBoundsMontWide : Bounds MontWideMod := ⟨by decide, by decide⟩
private instance conformanceBoundsLarge : Bounds LargeMod := ⟨by decide, by decide⟩

private def oneOnly : ZMod64 1 := ofNat 1 37
private def a2 : ZMod64 2 := ofNat 2 1
private def b2 : ZMod64 2 := ofNat 2 1
private def a3 : ZMod64 3 := ofNat 3 2
private def b3 : ZMod64 3 := ofNat 3 2
private def a7 : ZMod64 7 := ofNat 7 3
private def b7 : ZMod64 7 := ofNat 7 5
private def c16 : ZMod64 16 := ofNat 16 15
private def d16 : ZMod64 16 := ofNat 16 9
private def barrettWideA : ZMod64 BarrettWideMod := ofNat BarrettWideMod 65534
private def barrettWideB : ZMod64 BarrettWideMod := ofNat BarrettWideMod 32769
private def montWideA : ZMod64 MontWideMod := ofNat MontWideMod 65536
private def montWideB : ZMod64 MontWideMod := ofNat MontWideMod 32771
private def wideA : ZMod64 LargeMod := ofNat LargeMod (2 ^ 63 + 1)
private def wideB : ZMod64 LargeMod := ofNat LargeMod (2 ^ 63 - 17)

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
#guard (inv wideA * wideA).toNat = 1 % LargeMod

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
