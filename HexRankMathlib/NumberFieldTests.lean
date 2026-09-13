/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexRankMathlib.NumberFieldTactic
import HexNumberFieldMathlib.Exact

open Hex
open scoped Hex.PolyQuot.QAdjoinField

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def p : ZPoly := DensePoly.ofList [-2, 0, 1]
private def square : DyadicSquare := ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩
private def root : SimpleRoot p := SimpleRoot.ofSquare p square
private instance : ZPoly.CheckedIrreducible p :=
  ⟨(ZPoly.isIrreducible_iff p).mpr (by irreducibility), by decide⟩
private abbrev K := PolyQuot p root
private def α : K := PolyQuot.Rank.generator p root

example : α.coeffs = DensePoly.ofList [0, 1] := by decide +kernel
example : α * 1 = α := by decide +kernel

private theorem algebraicRank : (!![α, 1; 1, α] : _root_.Matrix (Fin 2) (Fin 2) K).rank = 2 := by
  rank

/-- info: '_private.HexRankMathlib.NumberFieldTests.0.algebraicRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms algebraicRank

example : (!![α, 1; 2, α] : _root_.Matrix (Fin 2) (Fin 2) K).rank = 1 := by rank
example : (!![α / 2, 1 / 2; 2 / 3, α / 3] : _root_.Matrix (Fin 2) (Fin 2) K).rank = 1 := by
  rank
example : (!![α, 1, 0; 1, α, 0] : _root_.Matrix (Fin 2) (Fin 3) K).rank ≤ 2 := by rank
example : (!![α ^ 2 - 2] : _root_.Matrix (Fin 1) (Fin 1) K).rank = 0 := by rank
example : _root_.Matrix.rank (fun (_ : Fin 0) (_ : Fin 2) => (0 : K)) = 0 := by rank

private def rep : RefinedIsolation p := ⟨⟨square, .ofWitness (by decide)⟩, by decide⟩
private theorem primitive : ZPoly.Primitive p := by rfl
private theorem leading : 0 < p.leadingCoeff := by decide
private theorem degree : 0 < p.natDegree := by decide
private theorem simple : HasOnlySimpleRoots p := by decide +kernel
private def a : AlgebraicNumber := AlgebraicNumber.ofNormalized p primitive leading degree
  inferInstance simple rep
  (AlgebraicNumber.ofNormalized?_isSome p primitive leading degree inferInstance simple rep)
private def β : QAdjoin a := a.toQAdjoin

private theorem canonicalRank :
    (!![β, 1; 1, β] : _root_.Matrix (Fin 2) (Fin 2) (QAdjoin a)).rank = 2 := by rank

/-- info: '_private.HexRankMathlib.NumberFieldTests.0.canonicalRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonicalRank

example : (!![β / 2, 1 / 2; 2 / 3, β / 3] :
    _root_.Matrix (Fin 2) (Fin 2) (QAdjoin a)).rank = 1 := by rank

example : (!![β ^ 2 - 2] : _root_.Matrix (Fin 1) (Fin 1) (QAdjoin a)).rank = 0 := by rank
example : (!![β ^ (-1 : Int), 1; 1, β] :
    _root_.Matrix (Fin 2) (Fin 2) (QAdjoin a)).rank = 1 := by rank

/-- error: rank: the target is false: the rank is 2 -/
#guard_msgs in
example : (!![β, 1; 1, β] : _root_.Matrix (Fin 2) (Fin 2) (QAdjoin a)).rank = 1 := by rank

private def nonmonic : ZPoly := DensePoly.ofList [-1, 0, 2]
private def nonmonicRoot : SimpleRoot nonmonic :=
  SimpleRoot.ofSquare nonmonic ⟨Dyadic.ofIntWithPrec 46341 16, 0, 16⟩
private instance : ZPoly.CheckedIrreducible nonmonic :=
  ⟨(ZPoly.isIrreducible_iff nonmonic).mpr (by irreducibility), by decide⟩
private abbrev K₂ := PolyQuot nonmonic nonmonicRoot
private def γ : K₂ := PolyQuot.Rank.generator nonmonic nonmonicRoot

example : (!![γ, 1; 1, 2 * γ] : _root_.Matrix (Fin 2) (Fin 2) K₂).rank = 1 := by rank
example : (!![γ ^ 2 - 1 / 2] : _root_.Matrix (Fin 1) (Fin 1) K₂).rank = 0 := by rank

private def cubic : ZPoly := DensePoly.ofList [-2, 0, 0, 1]
private def cubicRoot : SimpleRoot cubic :=
  SimpleRoot.ofSquare cubic ⟨Dyadic.ofIntWithPrec 82570 16, 0, 16⟩
private instance : ZPoly.CheckedIrreducible cubic :=
  ⟨(ZPoly.isIrreducible_iff cubic).mpr (by irreducibility), by decide⟩
private abbrev K₃ := PolyQuot cubic cubicRoot
private def δ : K₃ := PolyQuot.Rank.generator cubic cubicRoot

example : (!![δ, 1; δ ^ 2, δ] : _root_.Matrix (Fin 2) (Fin 2) K₃).rank = 1 := by rank
example : (!![δ, 1; 1, δ] : _root_.Matrix (Fin 2) (Fin 2) K₃).rank = 2 := by rank
