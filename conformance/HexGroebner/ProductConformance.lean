/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Packed
import HexGroebner.Native

namespace Hex.Groebner.ProductConformance

private def check (width : Width) (arity count multiplier start terms : UInt64)
    (arena base result : ByteArray) (expected : Bool) : Bool :=
  Native.Monomial.products width.bytes.toUInt8 arity count multiplier start terms arena base result == expected &&
    Native.Monomial.productsPortable width.bytes.toUInt8 arity count multiplier start terms arena base result == expected

/-- Independent arithmetic rows, all coordinate widths, final-lane mismatches,
empty slices, overflow-sized arguments and exact native/portable rejection. -/
def runtimeChecks (seed : Nat) : Bool := Id.run do
  for width in [Width.u8,.u16,.u32] do
    for arity in [1,2,63,4096] do
      let mut arena : ByteArray := {}
      let x := 3 + seed%17
      for value in [0,x,2*x] do
        for _ in [:arity] do arena := Packed.push width arena value.toUInt64
      let base := Packed.push .u32 {} 1
      let result := Packed.push .u32 {} 2
      if !check width arity.toUInt64 3 1 0 1 arena base result true then return false
      if !check width arity.toUInt64 3 0 0 1 arena base base true then return false
      if !check width arity.toUInt64 3 1 1 0 arena base result true then return false
      let changed := Packed.set width arena (3*arity-1) (2*x+1).toUInt64
      if !check width arity.toUInt64 3 1 0 1 changed base result false then return false
      for (n,count,multiplier,start,terms) in [
          (0,3,1,0,0),(4097,3,1,0,0),(arity,3,3,0,1),
          (arity,3,1,1,1),(arity,3,1,2,0),(arity,3,1,0,4097),
          (arity,18446744073709551615,1,0,1),
          (arity,3,1,18446744073709551615,0)] do
        if !check width n.toUInt64 count.toUInt64 multiplier.toUInt64 start.toUInt64 terms.toUInt64
            arena base result false then return false
    let x := 3 + seed%17
    let arena := ([0,x,2*x,3*x] : List Nat).foldl (fun bytes n => Packed.push width bytes n.toUInt64) {}
    let base := ([0,1,2] : List UInt64).foldl (fun bytes n => Packed.push .u32 bytes n) {}
    let result := ([1,2,2] : List UInt64).foldl (fun bytes n => Packed.push .u32 bytes n) {}
    -- The first two terms are valid; only the final in-range ID has wrong exponents.
    if !check width 1 4 1 0 2 arena base result true ||
        !check width 1 4 1 1 2 arena base result false ||
        !check width 1 4 1 2 1 arena base result false then return false
  let arena := Packed.push .u32 (Packed.push .u32 (Packed.push .u32 {} 0) 4294967295) 4294967294
  if !check .u32 1 3 1 0 1 arena (Packed.push .u32 {} 1) (Packed.push .u32 {} 2) false then return false
  return true

#guard runtimeChecks 0

example : Native.Monomial.productsPortable 1 1 3 1 0 1
    (ByteArray.mk #[0,1,2]) (ByteArray.mk #[1,0,0,0]) (ByteArray.mk #[2,0,0,0]) = true := by decide +kernel

example : Native.Monomial.productsPortable 1 0 3 1 0 0
    (ByteArray.mk #[]) (ByteArray.mk #[]) (ByteArray.mk #[]) = false := by decide +kernel

end Hex.Groebner.ProductConformance
