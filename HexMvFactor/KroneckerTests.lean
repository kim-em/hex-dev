/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Irred
public meta import HexMvPoly.Ring
public import HexMvFactor.Irred

public section

/-! Executable checks for mixed-radix substitution and the complete route. -/

namespace Hex.MvFactor.KroneckerTests

open Hex
open Hex.MvPoly
open Hex.MvFactor

private abbrev P2 := MvPoly 2 Int Mono.lex

private def x : P2 := X 0
private def y : P2 := X 1

private def degrees : Fin 2 → Nat := fun _ => 1

example : radixWeight degrees 0 = 1 := by
  decide +kernel

example : radixWeight degrees 1 = 2 := by
  decide +kernel

example : radixWeights degrees = #v[1, 2] := by
  decide +kernel

example : radixSize degrees = 4 := by
  decide +kernel

private def packed : P2 := C 3 + C 2 * x + y + x * y

#guard kron degrees packed == DensePoly.ofList [3, 2, 1, 1]

#guard kronDegree? degrees packed == some 3

#guard kronDegreeUpTo? 2 degrees packed == some 3

#guard kronDegreeUpTo? 3 degrees packed == some 3

#guard unKron? (cmp := Mono.lex) degrees (kron degrees packed) == some packed

#guard
  (unKron? (cmp := Mono.lex) degrees (DensePoly.monomial 4 1)).isNone

private def px : ZPoly := DensePoly.ofList [0, 1]
private def px1 : ZPoly := DensePoly.ofList [1, 1]
private def xyImage : List (ZPoly × Nat) := [(px, 1), (px1, 1)]

#guard properExponentVectors xyImage == [[0, 1], [1, 0]]

private def irreducible : P2 := x + y
private def irreducibleCert : IrredCert 2 Mono.lex :=
  .kronecker 1 xyImage

#guard checkIrred irreducible irreducibleCert

#guard obligations irreducible irreducibleCert == [px, px1]

private def completeIrreducible : Complete 2 Mono.lex :=
  ⟨⟨1, [⟨irreducible, 1⟩]⟩, [irreducibleCert]⟩

example : NoKronecker completeIrreducible = false := by
  decide +kernel

#guard
  match kronDecide irreducible with
  | .irreducible cert => checkIrred irreducible cert
  | .reducible _ => false

private def reducible : P2 := (x + 1) * (y + 1)

#guard
  match kronDecide reducible with
  | .irreducible _ => false
  | .reducible split => checkSplit reducible split

#guard !checkIrred irreducible (.kronecker 1 [(px1, 1)])

#guard !checkIrred irreducible (.kronecker 1 [(px, 1), (px1, 1), (px + 1, 0)])

end Hex.MvFactor.KroneckerTests
