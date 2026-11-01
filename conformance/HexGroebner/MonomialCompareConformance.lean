/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Native
import HexGroebner.Packed

namespace Hex.Groebner.MonomialCompareConformance

private def encode (width : Width) (values : Array Nat) : ByteArray :=
  values.foldl (fun bytes value => Packed.push width bytes value.toUInt64) {}

private def expected (operation : Nat) (a b : Array Nat) : UInt8 :=
  if operation == 2 then
    if (a.toList.zip b.toList).all (fun (x,y) => x ≤ y) then 1 else 0
  else
    let order := if operation == 1 then compare b.toList.reverse a.toList.reverse
      else compare a.toList b.toList
    match order with
    | .lt => 0 | .eq => 1 | .gt => 2

/-- Compare packed native reads with ordinary list ordering and pointwise
integer inequalities, including maximum coordinates and bounded-call edges. -/
def runtimeChecks (seed : Nat) : Bool := Id.run do
  for width in [Width.u8,.u16,.u32] do
    let bound := 2^(width.bytes*8)
    for n in [0,1,2,7,8,31,64,65,129,4096] do
      for trial in [:if n > 129 then 4 else 8] do
        let a := (Array.range n).map fun i =>
          if (i+trial)%7 == 0 then bound-1 else (seed+i*37+trial*11)%bound
        let b := (Array.range n).map fun i =>
          if trial%4 == 0 then a[i]! else if trial%4 == 1 then a[i]!/2
          else (seed+i*19+trial*13)%bound
        let arena := encode width (a++b)
        for operation in [:3] do
          let code := expected operation a b
          let actual := Native.Monomial.compareCode operation.toUInt8 width.bytes.toUInt8 n 0 1 arena
          if Native.Monomial.compareCode operation.toUInt8 width.bytes.toUInt8 n 0 1 (arena.push 255) != code then return false
          if actual != code || actual != Native.Monomial.comparePortable operation.toUInt8
              width.bytes.toUInt8 n 0 1 arena then return false
          if Native.Monomial.compareCode operation.toUInt8 width.bytes.toUInt8 n 0 0 arena != 1 then return false
        -- No comparison may mutate the borrowed source, including equal rows.
        if arena != encode width (a++b) then return false
    for operation in [0,1,2,3,255] do
      for n in [0,1,4096,4097,2^90] do
        for left in [0,1,2,2^31,2^32,2^90] do
          for right in [0,1,2,2^31,2^32,2^90] do
            let arena := encode width #[0,1]
            for w in [0,1,2,3,4,8,255] do
              let a := Native.Monomial.compareCode operation.toUInt8 w.toUInt8 n left right arena
              let b := Native.Monomial.comparePortable operation.toUInt8 w.toUInt8 n left right arena
              if a != b then return false
  return true

#guard runtimeChecks 0

example : Native.Monomial.compareCode 0 1 2 0 1 ⟨#[1,2,1,3]⟩ = 0 := by decide +kernel
example : Native.Monomial.compareCode 2 1 2 0 1 ⟨#[1,2,1,3]⟩ = 1 := by decide +kernel
example : Native.Monomial.compareCode 1 1 (2^90) 0 0 {} = 3 := by decide +kernel

example : Native.Monomial.comparePortable 0 1 2 0 1 ⟨#[1,2,1,3]⟩ = 0 := by decide +kernel
example : Native.Monomial.comparePortable 1 1 2 0 1 ⟨#[1,2,1,3]⟩ = 2 := by decide +kernel
example : Native.Monomial.comparePortable 2 1 2 0 1 ⟨#[1,2,1,3]⟩ = 1 := by decide +kernel
example : Native.Monomial.comparePortable 2 1 4097 0 0 {} = 3 := by decide +kernel

/-- info: 'Hex.Groebner.Native.Monomial.compareCode_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Native.Monomial.compareCode_eq

end Hex.Groebner.MonomialCompareConformance
