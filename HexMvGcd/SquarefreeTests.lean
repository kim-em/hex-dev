/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvGcd.Gcd
public meta import HexMvGcd.Prs
public meta import HexMvGcd.Squarefree
public meta import HexMvPoly.Ring
public import HexMvGcd.Squarefree

public section

/-! Focused finite-field squarefree decision regressions. -/

namespace Hex.MvPoly

private theorem boundsThree : ZMod64.Bounds 3 :=
  ⟨by decide, by decide⟩
attribute [local instance] boundsThree

private theorem primeThree : ZMod64.PrimeModulus 3 :=
  ZMod64.primeModulusOfPrime (by decide)
attribute [local instance] primeThree

private abbrev F3P1 := MvPoly 1 (ZMod64 3) Mono.lex
private abbrev F3P2 := MvPoly 2 (ZMod64 3) Mono.lex

example : Hex.Fraction.NonzeroOne (ZMod64 3) := inferInstance
example : PerfectFrac (ZMod64 3) := inferInstance

example (p : F3P1) : isSquarefree p = true ↔ Squarefree p :=
  isSquarefree_iff p

#guard
  let x : F3P1 := X 0
  isSquarefree (x * (x + 1))

-- One partial derivative vanishes, while the other witnesses squarefreeness.
#guard
  let x : F3P2 := X 0
  let y : F3P2 := X 1
  isSquarefree (x ^ 3 + y)

#guard
  let x : F3P1 := X 0
  !isSquarefree ((x + 1) ^ 2)

#guard
  let x : F3P2 := X 0
  let y : F3P2 := X 1
  !isSquarefree ((x ^ 3 + y) ^ 2)

#guard !isSquarefree (0 : F3P1)

-- In characteristic three this is `(x + 1)^3`, and its derivative vanishes.
#guard
  let x : F3P1 := X 0
  !isSquarefree (x ^ 3 + 1)

end Hex.MvPoly
