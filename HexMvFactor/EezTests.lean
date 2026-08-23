/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMvFactor.Eez
public import HexMvFactor.Eez

public section

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

private abbrev P1 := MvPoly 1 Int Mono.lex
private abbrev P2 := MvPoly 2 Int Mono.lex

private def x : P2 := X 0
private def y : P2 := X 1
private def innerY : P1 := X 0

/- A constant leading coefficient wins before support size and main degree. -/
#guard chooseMain (x ^ 3 + y * x + 1) == some 0

/- Complementary subsets occur once.  Level one contains the four singleton
   sides of a four-way split; level two contains every proper pair. -/
#guard (recombinationMasks 2 3).isEmpty
#guard (recombinationMasks 4 1).length == 4
#guard (recombinationMasks 4 2).length == 7
#guard (recombinationMasks 4 2).all fun mask =>
  mask.length == 4 && 0 < selectedCount mask && selectedCount mask < 4

/- Direct cardinality generation preserves the previous stable order:
   increasing smaller side, then false-before-true lexicographic masks. -/
#guard recombinationMasks 4 2 ==
  [[true, false, false, false],
   [true, false, true, true],
   [true, true, false, true],
   [true, true, true, false],
   [true, false, false, true],
   [true, false, true, false],
   [true, true, false, false]]

/- Level-one work has one candidate per image even at a size where full
   power-set materialization would be infeasible. -/
#guard
  let candidates := recombinationMasks 64 1
  candidates.length == 64 && candidates.all fun mask =>
    mask.length == 64 && maskLevel mask == 1 && mask.head? == some true

private def threeProbe : Probe 1 Mono.lex Mono.lex :=
  { point := fun _ => 0
    images := [DensePoly.ofList [1, 1], DensePoly.ofList [2, 1],
      DensePoly.ofList [3, 1]]
    leading := [innerY, innerY + 1, innerY + 2]
    uni := [] }

/- Grouping multiplies both image and leading-coefficient blocks and rejects
   malformed masks. -/
#guard
  match groupProbe threeProbe [true, false, true] with
  | none => false
  | some grouped =>
      match threeProbe.images, threeProbe.leading with
      | [f₁, f₂, f₃], [l₁, l₂, l₃] =>
          grouped.images == [f₁ * f₃, f₂] &&
            grouped.leading == [l₁ * l₃, l₂]
      | _, _ => false

#guard groupProbe threeProbe [true, false] |>.isNone

private def structuralLower : LowerFactor 1 := fun p r =>
  match h : structural? p with
  | some D => .ok (⟨⟨D, structural_checks h⟩, r⟩)
  | none => .error ⟨⟨.lift .arity, r⟩, none⟩

/- The executable embedding keeps lower multiplicities.  This deliberately
   feeds a nonsquarefree subject to the internal component routine: the
   lower `y^2` decomposition must emerge as two embedded copies, preserving
   the exact product without relying on a squarefree theorem. -/
private def contentMultiplicityPreserved : Bool :=
  let target := y ^ 2 * (x + 1)
  match factorSquarefree structuralLower Config.default target (Rand.ofSeed 4) with
  | .error _ => false
  | .ok result =>
      result.factors.length == 3 &&
        MvHensel.mvProduct result.factors == target

#guard contentMultiplicityPreserved

/- A stopped lower-arity content recursion contributes every factor it has
   already checked, while the unfactored main-variable primitive part remains
   as one exact queue entry. -/
private def partialLower : LowerFactor 1 := fun p r =>
  let left := innerY + 1
  let right := innerY + 2
  let D : Decomp 1 Mono.lex := ⟨1, [⟨left, 1⟩, ⟨right, 1⟩]⟩
  if h : checkDecomp p D = true then
    .error ⟨⟨.recombine 0, r⟩, some ⟨D, h⟩⟩
  else
    .error ⟨⟨.recombine 0, r⟩, none⟩

#guard
  let coefficient := (y + 1) * (y + 2)
  let mainPart := x ^ 3 + x ^ 2 + x + 1
  let target := coefficient * mainPart
  match factorSquarefree partialLower Config.default target (Rand.ofSeed 5) with
  | .ok _ => false
  | .error progress =>
      progress.factors.length == 3 &&
        progress.content == 1 &&
        MvHensel.mvProduct progress.factors == target

private def unluckyProbe : Probe 1 Mono.lex Mono.lex :=
  { point := fun _ => -1
    images := [DensePoly.ofList [-1, 1], DensePoly.ofList [1, 1]]
    leading := [1, 1]
    uni := [] }

private def noPrimes : Config :=
  { Config.default with primeFuel := 0 }

private def oneOrigin : Config :=
  { Config.default with
    pointFuel := 1
    pointShell := 0 }

/- Prime/V6 exhaustion abandons the point without being mislabeled as
   subset recombination. -/
#guard
  match tryProbe noPrimes 0 (x ^ 2 + y) unluckyProbe (Rand.ofSeed 7) with
  | .ok (.declined .primes) => true
  | _ => false

/- At `y = -1`, `x^2 + y` has two image factors but no two-block
   recombination distinct from the failed full split.  The checked lift
   reaches reconstruction and the decline is specifically recombination. -/
#guard
  match tryProbe Config.default 0 (x ^ 2 + y) unluckyProbe (Rand.ofSeed 7) with
  | .ok (.declined .recombine) => true
  | _ => false

/- Queue failure retains both an already accepted atom and the exact pending
   work.  The second target has nonsquarefree origin image `x^2`, providing a
   controlled failure after the first target succeeds. -/
#guard
  let first := x + 1
  let later := x ^ 2 + y
  match factorQueue structuralLower oneOrigin 0 5 [first, later] []
      (Rand.ofSeed 11) with
  | .ok _ => false
  | .error progress =>
      (match progress.error.reason with
       | .point _ (some .notSquarefree) => true
       | _ => false) &&
        progress.factors.length == 2 &&
        MvHensel.mvProduct progress.factors == first * later

end Hex.MvFactor
