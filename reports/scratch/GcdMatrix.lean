/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus

public section

open Hex

private def zp (cs : Array Int) : ZPoly := DensePoly.ofCoeffs cs

private def splitProduct (n : Nat) : ZPoly := Id.run do
  let mut acc : ZPoly := 1
  for i in [1:n+1] do
    acc := acc * (zp #[-(Int.ofNat i), 1])
  return acc

private instance b3  : ZMod64.Bounds 3  := ⟨by decide, by decide⟩
private instance b5  : ZMod64.Bounds 5  := ⟨by decide, by decide⟩
private instance b7  : ZMod64.Bounds 7  := ⟨by decide, by decide⟩
private instance b11 : ZMod64.Bounds 11 := ⟨by decide, by decide⟩
private instance b13 : ZMod64.Bounds 13 := ⟨by decide, by decide⟩
private instance b17 : ZMod64.Bounds 17 := ⟨by decide, by decide⟩
private instance b19 : ZMod64.Bounds 19 := ⟨by decide, by decide⟩
private instance b23 : ZMod64.Bounds 23 := ⟨by decide, by decide⟩
private instance b31 : ZMod64.Bounds 31 := ⟨by decide, by decide⟩
private instance b71 : ZMod64.Bounds 71 := ⟨by decide, by decide⟩

structure Row where
  p : Nat
  toNat : ZMod64 p → Nat
  inst : ZMod64.Bounds p

private def row (p : Nat) (inst : ZMod64.Bounds p) (f : ZPoly) : (Nat × Nat × Nat × Bool × Bool) :=
  let fModP := @ZPoly.modP p inst f
  let fp' := DensePoly.derivative fModP
  let g := DensePoly.gcd fModP fp'
  let gIs1 := g == 1
  let lead : ZMod64 p := g.toArray[0]?.getD 0
  let gDegZero := g.toArray.size > 0 && lead != 0
  (p, g.toArray.size, lead.toNat, gIs1, gDegZero)

@[expose]
def main : IO Unit := do
  for n in [3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 22, 24] do
    let f := splitProduct n
    let r11 := row 11 b11 f
    let r13 := row 13 b13 f
    let r17 := row 17 b17 f
    let r23 := row 23 b23 f
    let r31 := row 31 b31 f
    let r71 := row 71 b71 f
    IO.println s!"n={n}"
    for (p, sz, c0, is1, deg0) in [r11, r13, r17, r23, r31, r71] do
      IO.println s!"  p={p}: gcd size={sz} leading={c0} ==1?{is1} (degree-zero-and-nonzero={deg0})"
