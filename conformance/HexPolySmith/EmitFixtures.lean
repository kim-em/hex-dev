/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexPolyFp.PrimeField
import HexPolySmith

/-!
Deterministic polynomial-matrix Smith fixtures. The external oracle compares
only the canonical diagonal; transform identities are checked by the Lean
conformance driver.
-/

namespace Hex.PolySmithEmit

open Hex Hex.PolyMatrix Hex.Conformance.Emit

private def lib := "HexPolySmith"

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem primeFive : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private theorem primeTwo : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

private instance primeModFive : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime primeFive
private instance primeModTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime primeTwo

private def zp (p : Nat) [ZMod64.Bounds p] (coeffs : List Nat) : DensePoly (ZMod64 p) :=
  DensePoly.ofList (coeffs.map fun c => ZMod64.ofNat p c)

private def qp (coeffs : List Rat) : DensePoly Rat :=
  DensePoly.ofList coeffs

private def zcoeffs {p : Nat} [ZMod64.Bounds p] (f : DensePoly (ZMod64 p)) : List Int :=
  f.toArray.toList.map fun c => (c.toNat : Int)

private def qcoeffs (f : DensePoly Rat) : List Rat := f.toArray.toList

private def zentries {p : Nat} [ZMod64.Bounds p] {n m : Nat}
    (A : Matrix (DensePoly (ZMod64 p)) n m) : List (List (List Int)) :=
  A.rows.toList.map fun row => row.toList.map zcoeffs

private def qentries {n m : Nat} (A : Matrix (DensePoly Rat) n m) :
    List (List (List Rat)) :=
  A.rows.toList.map fun row => row.toList.map qcoeffs

private def emitZMod {p n m : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (id : String) (A : Matrix (DensePoly (ZMod64 p)) n m) : IO Unit := do
  emitPolyMatrixZModFixture lib id p n m (if n = 0 ∨ m = 0 then [] else zentries A)
  let S := snfData A
  emitResult lib id "smith" (polyListValue (S.diag.toList.map zcoeffs))

private def emitRat {n m : Nat} (id : String) (A : Matrix (DensePoly Rat) n m) : IO Unit := do
  emitPolyMatrixRatFixture lib id n m (if n = 0 ∨ m = 0 then [] else qentries A)
  let S := snfData A
  emitResult lib id "smith" (polyRatListValue (S.diag.toList.map qcoeffs))

private def emitCases : IO Unit := do
  let x5 := zp 5 [0, 1]
  let xp15 := zp 5 [1, 1]
  let x25 := x5 * x5
  let x35 := x25 * x5
  emitZMod "zmod5/coprime-diagonal" (#m[x5, 0; 0, xp15] : Matrix _ 2 2)
  -- A nondivisible pivot-row entry forces the two-entry Bezout update before
  -- the canonical diagonal can be read off.
  emitZMod "zmod5/bezout-pivot" (#m[x5, xp15; x25, x5] : Matrix _ 2 2)
  emitZMod "zmod5/chain-three" (#m[x5, 0, 0; 0, x25, 0; 0, 0, x35] : Matrix _ 3 3)
  emitZMod "zmod5/rank-deficient-wide" (#m[x5, xp15, 0; 0, 0, 0] : Matrix _ 2 3)
  emitZMod "zmod5/rank-deficient-tall" (#m[x5, 0; xp15, 0; 0, 0] : Matrix _ 3 2)
  emitZMod "zmod5/gcd-order-a" (#m[x25 - 1; x25 + x5] : Matrix _ 2 1)
  emitZMod "zmod5/gcd-order-b" (#m[x25 + x5; x25 - 1] : Matrix _ 2 1)
  emitZMod "zmod5/unit-entry" (#m[1, x5; 0, x25] : Matrix _ 2 2)
  emitZMod "zmod5/already-smith" (#m[x5, 0; 0, x25] : Matrix _ 2 2)
  emitZMod "zmod5/one-by-one-nonmonic"
    (#m[DensePoly.scale (ZMod64.ofNat 5 2) x5] : Matrix _ 1 1)
  emitZMod "zmod5/diagonal-zero-leading"
    (#m[0, 0; 0, x5] : Matrix _ 2 2)
  emitZMod "zmod5/diagonal-nonmonic-zero"
    (#m[DensePoly.scale (ZMod64.ofNat 5 2) x5, 0; 0, 0] : Matrix _ 2 2)
  emitZMod "zmod5/diagonal-zero" (0 : Matrix (DensePoly (ZMod64 5)) 2 2)
  emitZMod "zmod5/zero" (0 : Matrix (DensePoly (ZMod64 5)) 2 3)
  emitZMod "zmod5/zero-by-three" (0 : Matrix (DensePoly (ZMod64 5)) 0 3)
  emitZMod "zmod5/three-by-zero" (0 : Matrix (DensePoly (ZMod64 5)) 3 0)
  let x2 := zp 2 [0, 1]
  emitZMod "zmod2/degree-two" (#m[x2 * x2 + 1, x2; 0, x2 * x2] : Matrix _ 2 2)

  let x := qp [0, 1]
  let half : Rat := 1 / 2
  let third : Rat := 1 / 3
  emitRat "rat/nonmonic" (#m[DensePoly.scale half x, qp [third, 2];
      qp [2, 2], DensePoly.scale (3 : Rat) (x * x)] : Matrix _ 2 2)
  emitRat "rat/coprime-diagonal" (#m[x, 0; 0, x + 1] : Matrix _ 2 2)

end Hex.PolySmithEmit

def main : IO Unit := Hex.PolySmithEmit.emitCases
