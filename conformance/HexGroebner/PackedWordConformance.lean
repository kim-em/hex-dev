/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.PackedWord
import HexGroebner.Native

namespace Hex.Groebner.PackedWordConformance

private def checked : Bool := Id.run do
  for size in [8:81] do
    for seed in [:16] do
      let bytes : ByteArray := ⟨(Array.range size).map fun i =>
        if seed == 0 then 255 else if seed == 1 then 0 else
          UInt8.ofNat ((seed*7919+i*69069) % 256)⟩
      for offset in [:size-7] do
        let expected := (Native.read bytes 8 offset).toUInt64
        if Packed.read64 bytes offset != expected || Packed.read64Fast bytes offset != expected then
          return false
  return true

#guard checked

-- The compiler replacement does not change ordinary-kernel evaluation.
example : Packed.read64 ⟨#[1,2,3,4,5,6,7,8]⟩ 0 = 0x0807060504030201 := by decide +kernel
example : Packed.read64 ⟨#[0,255,255,255,255,255,255,255,255]⟩ 1 = 18446744073709551615 := by decide +kernel
example : Packed.read64 ⟨#[255,255,255,255,255,255,255,255]⟩ 4 = 4294967295 := by decide +kernel

end Hex.Groebner.PackedWordConformance
