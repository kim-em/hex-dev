/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexLLL.Basic

/-!
Core conformance checks for `HexLLL`.

Oracle: core uses Lean-only checks; the CI oracle profile uses `fpylll` via
`scripts/oracle/lll_fpylll.py`.
Mode: always for core, if_available for the `fpylll` oracle profile.

Covered operations:
- `Hex.Matrix.memLattice`
- `Hex.Matrix.independent`
- `Hex.isLLLReduced`
- `Hex.lll`
- `Hex.lll.firstShortVector`
- `Hex.lll.shortVectors`
- `Hex.certCheck`
- `Hex.Internal.LLLState.sizeReduceColumn`
- `Hex.Internal.LLLState.sizeReduce`
- `Hex.Internal.LLLState.swapStep`
- `Hex.Internal.LLLState.gramSchmidtCoeff`
- `Hex.Internal.LLLState.potential`

Covered properties:
- committed row-combination witnesses satisfy lattice membership.
- independence distinguishes nonsingular bases from zero and dependent inputs.
- reducedness predicates accept small already-reduced bases and reject an
  unreduced basis with a large Gram-Schmidt coefficient.
- size-reduction updates perform the specified integer row operation and leave
  stored Gram determinants unchanged.
- adjacent swaps perform the specified row swap and update the affected stored
  determinant and scaled coefficients.
- downstream short-vector entry points expose the first reduced row and the
  ordered reduced rows on a BZ-shaped integer coefficient basis.
- certified-dispatch certificates accept a known-good reduced basis and reject
  tampered basis/transform witnesses, malformed flat provider payloads, and
  an `η = 11/20` size-reduction boundary violation.
- stored rational Gram-Schmidt coefficients recover the quotient `ν[i][j]/d[j+1]`.
- potential multiplies the stored determinant prefix `d₁, ..., dₙ₋₁`.

Covered edge cases:
- an identity basis with zero off-diagonal Gram-Schmidt coefficients.
- a zero basis and a dependent rectangular basis.
- a size-reduction pivot with positive quotient and an already-small pivot that
  does not change the state.
- adjacent swaps at the first two nonzero row positions and at a higher-index
  orthogonal-block position that exercises the multi-row update loop.
- size-reduction at the highest valid row index that exercises the full
  earlier-row loop.
- a certified-dispatch payload for a `2 × 2` triangular basis, including
  explicit transforms in both row-lattice directions.
- a downstream basis with one integer coefficient row per lifted local factor.
- out-of-range `sizeReduce` / `swapStep` calls that leave the state unchanged.
-/

namespace Hex
namespace LLLConformance

open Hex.Internal

private def identity8 : Matrix Int 8 8 := Matrix.identity 8

private def zero8 : Matrix Int 8 8 := 0

private def dependent8x4 : Matrix Int 8 4 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 2
    | 1, 0 => 4
    | 2, 0 => -1
    | 2, 1 => 3
    | 3, 2 => 1
    | 4, 3 => 1
    | 5, 0 => 1
    | 5, 2 => 2
    | 6, 1 => 1
    | 6, 3 => -1
    | 7, 2 => -1
    | _, _ => 0

private def unreduced8 : Matrix Int 8 8 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 1, 0 => 3
    | 1, 1 => 1
    | 2, 2 => 1
    | 3, 3 => 1
    | 4, 4 => 1
    | 5, 5 => 1
    | 6, 6 => 1
    | 7, 7 => 1
    | _, _ => 0

private def typical8 : Matrix Int 8 8 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 2 => 1
    | 2, 1 => 1
    | 2, 2 => 1
    | 3, 3 => 1
    | 4, 4 => 1
    | 5, 5 => 1
    | 6, 6 => 1
    | 7, 7 => 1
    | _, _ => 0

private def bzStyleBasis : Matrix Int 3 4 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 3 => 1
    | 1, 1 => 1
    | 1, 3 => -1
    | 2, 2 => 1
    | 2, 3 => 2
    | _, _ => 0

private def certInput2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 12
    | 1, 1 => 1
    | _, _ => 0

private def certReduced2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 1 => 1
    | 1, 0 => 1
    | _, _ => 0

private def certTransform2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 1 => -12
    | _, _ => 0

private def certInverse2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 12
    | 0, 1 => 1
    | 1, 0 => 1
    | _, _ => 0

private def tamperedReduced2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 1, 1 => 1
    | _, _ => 0

private def tamperedTransform2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 1 => -12
    | _, _ => 0

private def tamperedInverse2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 12
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 1 => 1
    | _, _ => 0

private def etaBoundary2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 10
    | 1, 0 => 6
    | 1, 1 => 1
    | _, _ => 0

private def goodFlat2 : Array Int :=
  #[0, 2, 2, 1,
    0, 1,
    1, 0,
    0, 1,
    1, -12,
    12, 1,
    1, 0]

private def malformedFlat2 : Array Int :=
  #[0, 2, 3, 1,
    0, 1,
    1, 0,
    0, 1,
    1, -12,
    12, 1,
    1, 0]

private abbrev f0_2 : Fin 2 := ⟨0, by decide⟩
private abbrev f1_2 : Fin 2 := ⟨1, by decide⟩
private abbrev f0_3 : Fin 3 := ⟨0, by decide⟩
private abbrev f1_3 : Fin 3 := ⟨1, by decide⟩
private abbrev f2_3 : Fin 3 := ⟨2, by decide⟩
private abbrev f0_4 : Fin 4 := ⟨0, by decide⟩
private abbrev f1_4 : Fin 4 := ⟨1, by decide⟩
private abbrev f2_4 : Fin 4 := ⟨2, by decide⟩
private abbrev f3_4 : Fin 4 := ⟨3, by decide⟩
private abbrev f0_8 : Fin 8 := ⟨0, by decide⟩
private abbrev f1_8 : Fin 8 := ⟨1, by decide⟩
private abbrev f2_8 : Fin 8 := ⟨2, by decide⟩
private abbrev f3_8 : Fin 8 := ⟨3, by decide⟩
private abbrev f4_8 : Fin 8 := ⟨4, by decide⟩
private abbrev f5_8 : Fin 8 := ⟨5, by decide⟩
private abbrev f6_8 : Fin 8 := ⟨6, by decide⟩
private abbrev f7_8 : Fin 8 := ⟨7, by decide⟩
private abbrev f0_9 : Fin 9 := ⟨0, by decide⟩
private abbrev f1_9 : Fin 9 := ⟨1, by decide⟩
private abbrev f2_9 : Fin 9 := ⟨2, by decide⟩
private abbrev f3_9 : Fin 9 := ⟨3, by decide⟩
private abbrev f4_9 : Fin 9 := ⟨4, by decide⟩
private abbrev f5_9 : Fin 9 := ⟨5, by decide⟩
private abbrev f6_9 : Fin 9 := ⟨6, by decide⟩
private abbrev f7_9 : Fin 9 := ⟨7, by decide⟩
private abbrev f8_9 : Fin 9 := ⟨8, by decide⟩

private def identityLatticeVec : Vector Int 8 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 7
    | 1 => -2
    | 2 => 5
    | 3 => -1
    | 4 => 3
    | 5 => 0
    | 6 => 2
    | _ => -4

private def dependentLatticeVec : Vector Int 4 :=
  Vector.ofFn fun i =>
    match i.val with
    | 1 => 6
    | _ => 0

private def typicalLatticeVec : Vector Int 8 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 2
    | 1 => -1
    | 2 => -1
    | 3 => 5
    | 4 => -1
    | 5 => 0
    | 6 => 2
    | _ => 3

private def identityWitness : Vector Int 8 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 7
    | 1 => -2
    | 2 => 5
    | 3 => -1
    | 4 => 3
    | 5 => 0
    | 6 => 2
    | _ => -4

private def dependentWitness : Vector Int 8 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 3
    | 1 => -1
    | 2 => 2
    | _ => 0

private def typicalWitness : Vector Int 8 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => -2
    | 3 => 5
    | 4 => -1
    | 5 => 0
    | 6 => 2
    | _ => 3

example : Matrix.memLattice identity8 identityLatticeVec := by
  refine ⟨identityWitness, ?_⟩
  decide

example : Matrix.memLattice dependent8x4 dependentLatticeVec := by
  refine ⟨dependentWitness, ?_⟩
  decide

example : Matrix.memLattice typical8 typicalLatticeVec := by
  refine ⟨typicalWitness, ?_⟩
  decide

private def independentCheck (b : Matrix Int n m) : Bool :=
  (List.finRange n).all fun k =>
    0 < GramSchmidt.Int.gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt)

#guard independentCheck identity8
#guard !independentCheck zero8
#guard !independentCheck dependent8x4

-- `lllReducedExact` is the executable reducedness oracle over
-- `GramSchmidt.Int.data`: identity is fully (3/4, 1/2)-reduced, while zero
-- and dependent bases fail independence.
#guard lllReducedExact identity8 (3/4 : Rat) (1/2 : Rat)
#guard !lllReducedExact zero8 (3/4 : Rat) (1/2 : Rat)
#guard !lllReducedExact dependent8x4 (3/4 : Rat) (1/2 : Rat)

#guard Matrix.row certReduced2 f0_2 = Matrix.row certInput2 f1_2
#guard Matrix.row certReduced2 f1_2 =
  (Vector.ofFn fun j => if j.val = 0 then 1 else 0)

#guard certCheck certInput2 certReduced2 certTransform2 certInverse2
  (3/4 : Rat) (11/20 : Rat)
#guard !certCheck certInput2 tamperedReduced2 certTransform2 certInverse2
  (3/4 : Rat) (11/20 : Rat)
#guard !certCheck certInput2 certReduced2 tamperedTransform2 certInverse2
  (3/4 : Rat) (11/20 : Rat)
#guard !certCheck certInput2 certReduced2 certTransform2 tamperedInverse2
  (3/4 : Rat) (11/20 : Rat)
#guard match LLLProvider.certifyFlat certInput2 (3/4 : Rat) goodFlat2 with
  | some _ => true
  | none => false
#guard match LLLProvider.certifyFlat certInput2 (3/4 : Rat) malformedFlat2 with
  | some _ => false
  | none => true
#guard !certCheck etaBoundary2 etaBoundary2 (Matrix.identity (R := Int) 2) (Matrix.identity (R := Int) 2) (3/4 : Rat) (11/20 : Rat)

private def stateOf (b : Matrix Int n m) : LLLState n m :=
  let gs := GramSchmidt.Int.data b
  { b := b
    ν := gs.ν
    d := gs.d }

private def identityState : LLLState 8 8 := stateOf identity8
private def zeroState : LLLState 8 8 := stateOf zero8
private def unreducedState : LLLState 8 8 := stateOf unreduced8
private def typicalState : LLLState 8 8 := stateOf typical8

#guard (identityState.d.get f0_9) = 1
#guard (identityState.d.get f1_9) = 1
#guard (identityState.d.get f2_9) = 1
#guard (identityState.d.get f3_9) = 1
#guard (identityState.d.get f4_9) = 1
#guard (identityState.d.get f5_9) = 1
#guard (identityState.d.get f6_9) = 1
#guard (identityState.d.get f7_9) = 1
#guard (identityState.d.get f8_9) = 1
#guard identityState.potential = 1

#guard (zeroState.d.get f0_9) = 1
#guard (zeroState.d.get f1_9) = 0
#guard (zeroState.d.get f2_9) = 0
#guard (zeroState.d.get f8_9) = 0
#guard zeroState.potential = 0

#guard (typicalState.d.get f0_9) = 1
#guard (typicalState.d.get f1_9) = 2
#guard (typicalState.d.get f2_9) = 3
#guard (typicalState.d.get f3_9) = 4
#guard (typicalState.d.get f4_9) = 4
#guard (typicalState.d.get f5_9) = 4
#guard (typicalState.d.get f6_9) = 4
#guard (typicalState.d.get f7_9) = 4
#guard (typicalState.d.get f8_9) = 4
#guard typicalState.potential = 6144

#guard independentCheck bzStyleBasis
#guard (Matrix.row bzStyleBasis f0_3).get f0_4 = 1
#guard (Matrix.row bzStyleBasis f1_3).get f1_4 = 1
#guard (Matrix.row bzStyleBasis f2_3).get f2_4 = 1
#guard (Matrix.row bzStyleBasis f0_3).get f3_4 = 1
#guard (Matrix.row bzStyleBasis f1_3).get f3_4 = -1
#guard (Matrix.row bzStyleBasis f2_3).get f3_4 = 2

example (hδ : (121 / 400 : Rat) < 3 / 4) (hδ' : (3 / 4 : Rat) ≤ 1) :
    lll.firstShortVector bzStyleBasis (3 / 4) hδ hδ' (by decide) =
      Matrix.row (lll bzStyleBasis (3 / 4) hδ hδ' (by decide)) f0_3 := by
  rfl

example (hδ : (121 / 400 : Rat) < 3 / 4) (hδ' : (3 / 4 : Rat) ≤ 1) :
    lll.shortVectors bzStyleBasis (3 / 4) hδ hδ' (by decide) =
      (lll bzStyleBasis (3 / 4) hδ hδ' (by decide)).rows.toArray := by
  rfl

-- The three proof arguments are `autoParam`s (`:= by grind`), so at a concrete
-- `δ`/`n` the public entry points take no proof arguments at all.
example : lll.firstShortVector bzStyleBasis (3 / 4) = Matrix.row (lll bzStyleBasis (3 / 4)) f0_3 := by
  rfl

example : lll.shortVectors bzStyleBasis (3 / 4) = (lll bzStyleBasis (3 / 4)).rows.toArray := by
  rfl

example :
    identityState.gramSchmidtCoeff 1 0 (by decide) (by decide) =
      (((identityState.ν.getRow f1_8).get f0_8 : Int) : Rat) / (identityState.d.get f1_9 : Rat) := by
  rfl

example :
    unreducedState.gramSchmidtCoeff 1 0 (by decide) (by decide) =
      (((unreducedState.ν.getRow f1_8).get f0_8 : Int) : Rat) /
        (unreducedState.d.get f1_9 : Rat) := by
  rfl

example :
    typicalState.gramSchmidtCoeff 2 1 (by decide) (by decide) =
      (((typicalState.ν.getRow f2_8).get f1_8 : Int) : Rat) / (typicalState.d.get f2_9 : Rat) := by
  rfl

#guard (((identityState.ν.getRow f1_8).get f0_8 : Int) : Rat) /
  (identityState.d.get f1_9 : Rat) = 0
#guard (((unreducedState.ν.getRow f1_8).get f0_8 : Int) : Rat) /
  (unreducedState.d.get f1_9 : Rat) = 3
#guard (((typicalState.ν.getRow f2_8).get f1_8 : Int) : Rat) /
  (typicalState.d.get f2_9 : Rat) = ((1 : Rat) / 3)

private def sizeReducedUnreduced : LLLState 8 8 :=
  unreducedState.sizeReduceColumn f0_8 f1_8 (by decide)

#guard Matrix.row sizeReducedUnreduced.b f0_8 = Matrix.row unreduced8 f0_8
#guard Matrix.row sizeReducedUnreduced.b f1_8 =
  (Vector.ofFn fun i => if i.val = 1 then 1 else 0)
#guard sizeReducedUnreduced.d = unreducedState.d
#guard (sizeReducedUnreduced.ν.getRow f1_8).get f0_8 = 0

private def unchangedIdentityColumn : LLLState 8 8 :=
  identityState.sizeReduceColumn f0_8 f1_8 (by decide)

#guard unchangedIdentityColumn.b = identityState.b
#guard unchangedIdentityColumn.ν = identityState.ν
#guard unchangedIdentityColumn.d = identityState.d

private def sizeReducedTypical : LLLState 8 8 :=
  typicalState.sizeReduce 2

#guard Matrix.row sizeReducedTypical.b f0_8 = Matrix.row typical8 f0_8
#guard Matrix.row sizeReducedTypical.b f1_8 = Matrix.row typical8 f1_8
#guard Matrix.row sizeReducedTypical.b f2_8 =
  (Vector.ofFn fun i =>
    match i.val with
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | _ => 0)
#guard sizeReducedTypical.d = typicalState.d

#guard (identityState.sizeReduce 2).b = identityState.b
#guard (identityState.sizeReduce 2).ν = identityState.ν
#guard (identityState.sizeReduce 2).d = identityState.d

private def sizeReducedTypicalHigh : LLLState 8 8 :=
  typicalState.sizeReduce 7

#guard sizeReducedTypicalHigh.b = typicalState.b
#guard sizeReducedTypicalHigh.ν = typicalState.ν
#guard sizeReducedTypicalHigh.d = typicalState.d

private def swappedFirstTypical : LLLState 8 8 :=
  typicalState.swapStep 1

#guard Matrix.row swappedFirstTypical.b f0_8 = Matrix.row typical8 f1_8
#guard Matrix.row swappedFirstTypical.b f1_8 = Matrix.row typical8 f0_8
#guard Matrix.row swappedFirstTypical.b f2_8 = Matrix.row typical8 f2_8
#guard (swappedFirstTypical.d.get f0_9) = 1
#guard (swappedFirstTypical.d.get f1_9) = 2
#guard (swappedFirstTypical.d.get f2_9) = 3
#guard (swappedFirstTypical.d.get f3_9) = 4
#guard (swappedFirstTypical.d.get f8_9) = 4
#guard (swappedFirstTypical.ν.getRow f1_8).get f0_8 = 1
#guard swappedFirstTypical.potential = 6144

private def swappedSecondTypical : LLLState 8 8 :=
  typicalState.swapStep 2

#guard Matrix.row swappedSecondTypical.b f0_8 = Matrix.row typical8 f0_8
#guard Matrix.row swappedSecondTypical.b f1_8 = Matrix.row typical8 f2_8
#guard Matrix.row swappedSecondTypical.b f2_8 = Matrix.row typical8 f1_8
#guard (swappedSecondTypical.d.get f0_9) = 1
#guard (swappedSecondTypical.d.get f1_9) = 2
#guard (swappedSecondTypical.d.get f2_9) = 3
#guard (swappedSecondTypical.d.get f3_9) = 4
#guard (swappedSecondTypical.d.get f8_9) = 4
#guard (swappedSecondTypical.ν.getRow f2_8).get f1_8 = 1
#guard swappedSecondTypical.potential = 6144

private def swappedHighTypical : LLLState 8 8 :=
  typicalState.swapStep 4

#guard Matrix.row swappedHighTypical.b f3_8 = Matrix.row typical8 f4_8
#guard Matrix.row swappedHighTypical.b f4_8 = Matrix.row typical8 f3_8
#guard Matrix.row swappedHighTypical.b f0_8 = Matrix.row typical8 f0_8
#guard Matrix.row swappedHighTypical.b f7_8 = Matrix.row typical8 f7_8
#guard swappedHighTypical.d = typicalState.d
#guard swappedHighTypical.potential = 6144

#guard (typicalState.swapStep 0).b = typicalState.b
#guard (typicalState.swapStep 8).b = typicalState.b
#guard (typicalState.swapStep 8).d = typicalState.d

end LLLConformance
end Hex
