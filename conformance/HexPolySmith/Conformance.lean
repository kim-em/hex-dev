/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyFp.PrimeField
import HexPolySmith

/-!
Executable conformance checks for polynomial Smith form.

**Oracle:** SymPy `smith_normal_form` over `QQ[x]` and `GF(p)[x]`.

**Mode:** `required` for release verification and `if_available` in ordinary
local runs; the Lean-only checks below are `always`.

**Covered operations:**

* `snf`, `snfRank`, `snfData`, `isSNFShape`, and `invariantFactors`;
* `moduleStructure`, `quotientOrder`, and `solve`;
* `snfDiagonal` and `snfDiagonalData`;
* `snfCert`, `evalMatrix`, and `mulEqCertAt`.

**Covered properties:**

* the returned diagonal, rank, monicity, and divisibility chain agree;
* left/right transformations and their explicit inverses multiply correctly;
* direct and evaluated product certificates accept valid products;
* structure projections and quotient order match independently known diagonal
  presentations;
* solving is sound on constructed right-hand sides and rejects an impossible
  divisibility constraint;
* a full-rank square result has the same total invariant-factor degree as the
  determinant.

**Covered edge cases:**

* zero matrices and zero right-hand sides;
* `1 × 1`, tall, wide, singular, and rank-deficient matrices;
* unit, nonmonic, zero, and out-of-order diagonal entries;
* a right basis change that is not the identity;
* a field too small to supply a degree-two evaluation certificate.

Each advertised operation is exercised on a typical presentation, the zero
edge case, and a unit/nonmonic adversarial presentation. Additional rectangular
and small-field guards exercise orientation and certificate-specific hazards.
-/

namespace Hex.PolySmithConformance

open Hex Hex.PolyMatrix

private instance boundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem primeTwo : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro k hk
    have hkle : k ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hk
    · exact Or.inl rfl
    · exact Or.inr rfl

private instance primeModTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime primeTwo

private def qp (coeffs : List Rat) : DensePoly Rat := DensePoly.ofList coeffs

private def x : DensePoly Rat := qp [0, 1]

private def points : Vector Rat 7 := #v[0, 1, 2, 3, 4, 5, 6]

private def typical : Matrix (DensePoly Rat) 2 2 :=
  #m[x, 0; 0, x * x]

private def zeroCase : Matrix (DensePoly Rat) 2 2 := 0

-- A unit and a nonmonic polynomial force normalization as well as ordering.
private def adversarial : Matrix (DensePoly Rat) 2 2 :=
  #m[2, 0; 0, DensePoly.scale (2 : Rat) x]

private def typicalExpected : Matrix (DensePoly Rat) 2 2 := typical
private def zeroExpected : Matrix (DensePoly Rat) 2 2 := 0
private def adversarialExpected : Matrix (DensePoly Rat) 2 2 :=
  #m[1, 0; 0, x]

-- A nondivisible pivot-row entry forces the Bézout branch.
private def bezoutCase : Matrix (DensePoly Rat) 2 2 :=
  #m[x, x + 1; x * x, x]

private def bezoutFactor : DensePoly Rat := x * x * x

-- The pivot row and column are clear, but the trailing block is not divisible
-- by the pivot, forcing the bad-block restart.
private def badBlockCase : Matrix (DensePoly Rat) 2 2 :=
  #m[x, 0; 0, x + 1]

private def badBlockFactor : DensePoly Rat := x * (x + 1)

private def evalReference (A : Matrix (DensePoly Rat) 2 2) (a : Rat) :
    Matrix Rat 2 2 :=
  Matrix.ofFn fun i j => DensePoly.eval A[(i, j)] a

private def publicSurface
    (A expected : Matrix (DensePoly Rat) 2 2)
    (expectedRank : Nat) (expectedFactors : List (DensePoly Rat))
    (expectedFree : Nat) (expectedTorsion : Array (DensePoly Rat))
    (expectedOrder : DensePoly Rat) : Bool :=
  let S := snfData A
  let T := S.left * A
  let witness : Vector (DensePoly Rat) 2 := #v[x + 1, qp [2]]
  let b := Matrix.vecMul witness A
  (snf A == expected)
    && (snfRank A == expectedRank)
    && (S.rank == expectedRank)
    && (S.diag.toList == expectedFactors)
    && ((invariantFactors A).toList == expectedFactors)
    && (moduleStructure A == (expectedFree, expectedTorsion))
    && (quotientOrder A == expectedOrder)
    && isSNFShape S
    && snfCert A S T
    && (S.left * S.leftInv == polyIdentity 2)
    && (S.right * S.rightInv == polyIdentity 2)
    && (T * S.right == expected)
    && (evalMatrix A 2 == evalReference A 2)
    && mulEqCertAt points S.left A T
    && match solve A b with
      | some answer => Matrix.vecMul answer A == b
      | none => false

-- Typical, edge, and adversarial coverage for every operation in
-- `publicSurface`.
#guard publicSurface typical typicalExpected 2 [x, x * x] 0 #[x, x * x]
  (x * x * x)
#guard publicSurface zeroCase zeroExpected 0 [] 2 #[] 0
#guard publicSurface adversarial adversarialExpected 2 [1, x] 0 #[x] x
#guard publicSurface bezoutCase (#m[1, 0; 0, bezoutFactor]) 2
  [1, bezoutFactor] 0 #[bezoutFactor] bezoutFactor
#guard publicSurface badBlockCase (#m[1, 0; 0, badBlockFactor]) 2
  [1, badBlockFactor] 0 #[badBlockFactor] badBlockFactor

private def diagonalSurface (d : Vector (DensePoly Rat) 3)
    (expected : Matrix (DensePoly Rat) 3 3)
    (expectedFactors : List (DensePoly Rat)) : Bool :=
  let S := snfDiagonalData d
  (snfDiagonal d == expected)
    && (S.diag.toList == expectedFactors)
    && snfCert (Matrix.diagMatrix d 3 3) S (S.left * Matrix.diagMatrix d 3 3)

private def typicalDiagonal : Vector (DensePoly Rat) 3 := #v[x, x * x, x * x * x]
private def zeroDiagonal : Vector (DensePoly Rat) 3 := #v[0, 0, 0]
private def adversarialDiagonal : Vector (DensePoly Rat) 3 :=
  #v[0, DensePoly.scale (2 : Rat) (x * x), DensePoly.scale (3 : Rat) x]

#guard diagonalSurface typicalDiagonal
  (#m[x, 0, 0; 0, x * x, 0; 0, 0, x * x * x]) [x, x * x, x * x * x]
#guard diagonalSurface zeroDiagonal (0 : Matrix (DensePoly Rat) 3 3) []
#guard diagonalSurface adversarialDiagonal
  (#m[x, 0, 0; 0, x * x, 0; 0, 0, 0]) [x, x * x]

-- The total invariant-factor degree agrees with the determinant degree.
#guard
  (invariantFactors typical).toList.foldl
      (fun degree p => degree + p.degree?.getD 0) 0 ==
    (Matrix.det typical).degree?.getD 0

-- Rectangular orientation and rank-deficient coverage.
private def wide : Matrix (DensePoly Rat) 2 3 :=
  #m[x, x + 1, 0; 0, 0, 0]
private def tall : Matrix (DensePoly Rat) 3 2 :=
  #m[x, 0; x + 1, 0; 0, 0]

#guard
  let S := snfData wide
  S.rank == 1 && snfCert wide S (S.left * wide)
#guard
  let S := snfData tall
  S.rank == 1 && snfCert tall S (S.left * tall)

-- This fixture genuinely exercises the transformed right-hand side in solve.
private def solveA : Matrix (DensePoly Rat) 2 2 :=
  #m[x, 1; 0, x + 1]
private def solveWitness : Vector (DensePoly Rat) 2 := #v[x + 1, qp [2]]
private def solveB : Vector (DensePoly Rat) 2 := Matrix.vecMul solveWitness solveA

#guard (snfData solveA).right != polyIdentity 2
#guard
  match solve solveA solveB with
  | some answer => Matrix.vecMul answer solveA == solveB
  | none => false
#guard solve (#m[x] : Matrix (DensePoly Rat) 1 1) (#v[1] : Vector _ 1) == none

-- The direct certificate works over a field too small for a degree-two
-- evaluation certificate to obtain enough distinct points.
#guard
  letI : OfNat (DensePoly (ZMod64 2)) 0 := ⟨Zero.zero⟩
  let x2 : DensePoly (ZMod64 2) :=
    DensePoly.ofList [0, ZMod64.ofNat 2 1]
  let A : Matrix (DensePoly (ZMod64 2)) 2 2 :=
    #m[x2 * x2 + 1, x2; 0, x2 * x2]
  let S := snfData A
  snfCert A S (Matrix.mul S.left A)

end Hex.PolySmithConformance
