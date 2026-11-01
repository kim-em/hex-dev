/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Native

namespace Hex.Groebner.ByteConformance

/-- Compiled native/portable comparison, including arbitrary-size Nat bounds. -/
def runtimeChecks : Bool := Id.run do
  let left : ByteArray := ⟨(Array.range 8193).map fun i => UInt8.ofNat (i*7919+17)⟩
  for changed in [0,1,4095,4096,8192] do
    let right := left.set! changed (left[changed]! + 1)
    for size in [0,1,7,4095,4096,4097,8193] do
      let a := left.extract 0 size
      let b := right.extract 0 size
      for start in [0,1,size/2,size,size+1,2^64,2^90] do
        for count in [0,1,7,4095,4096,4097,2^64,2^90] do
          if Native.Bytes.equal a b start count != Native.Bytes.equalPortable a b start count then
            return false
          if Native.Bytes.equal a a start count != Native.Bytes.equalPortable a a start count then
            return false
  return true

#guard runtimeChecks

example : Native.Bytes.equal ⟨#[1,2,3]⟩ ⟨#[1,2,4]⟩ 0 2 = true := by decide +kernel
example : Native.Bytes.equal ⟨#[1,2,3]⟩ ⟨#[1,2,4]⟩ 0 3 = false := by decide +kernel
example : Native.Bytes.equal ⟨#[1]⟩ ⟨#[1]⟩ (2^90) 0 = false := by decide +kernel

end Hex.Groebner.ByteConformance
