/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModularMatrix.Fixtures
import HexMatrix.Notation

/-!
Oracle: `scripts/oracle/modmat_flint.py` (FLINT integer determinants).
Mode: always
Covered operations: determinant routes, decomposition, lifting, vector/matrix solves, witnesses,
modular rank certificates, exact fallback rank and rational kernel bases.
Covered properties: modular residues, strict-bound reconstruction, bound ordering,
modular success, recorded Bareiss fallback, reduced checked solutions, decomposition reuse,
cofactor image counts, nonunit skips, exact digit counts and FLINT agreement.
Covered edge cases: empty and singular matrices, row-swap signs, composite units,
nonzero nonunits, zero pivot columns, zero fuel, bad initial primes, large entries.
-/

namespace Hex.ModularMatrixConformance

local instance : ZMod64.Bounds 6 := ⟨by decide, by decide⟩
local instance : ZMod64.Bounds 1 := ⟨by decide, by decide⟩

private def modMatrix (a b c d : Nat) : Matrix (ZMod64 6) 2 2 :=
  Matrix.ofFn fun i j => ZMod64.ofNat 6
    (if i.val = 0 then (if j.val = 0 then a else b) else if j.val = 0 then c else d)

#guard (ZMod64.inv? (5 : ZMod64 6)).map ZMod64.toNat == some 5
#guard ZMod64.inv? (2 : ZMod64 6) == none
#guard ((modMatrix 1 2 3 5).detMod?).map ZMod64.toNat == some 5
#guard ((modMatrix 2 0 3 1).detMod?).isNone
-- Determinant one does not guarantee an individual unit in a composite-modulus column.
#guard ((modMatrix 2 3 3 2).detMod?).isNone
#guard ((modMatrix 0 1 0 2).detMod?).map ZMod64.toNat == some 0
-- A nonunit preceding a unit must not prevent a later unit pivot being used.
#guard ((modMatrix 2 1 1 0).detMod?).map ZMod64.toNat == some 5
#guard (Matrix.ofFn (fun _ _ => (0 : ZMod64 1)) : Matrix (ZMod64 1) 1 1).detMod? == some 0

private def checkCase (c : ModularMatrixFixtures.Case) : Bool :=
  let A := c.matrix
  let expected := A.bareiss
  let bound := A.rowNormBound
  let fuel := bound.log2 / 30 + 2
  let modular := ModularMatrix.detWith A fuel
  let fallback := ModularMatrix.detWith A 0
  A.detBounded? bound fuel == some expected &&
    A.detModular? fuel == some expected &&
    ModularMatrix.det A == expected &&
    modular == ⟨expected, .modular, []⟩ &&
    fallback == ⟨expected, .modular, [.bareiss]⟩ &&
    A.hadamardBound ≤ bound

#guard ModularMatrixFixtures.cases.all checkCase

-- Recover the consumed prefix length from the actual CRT modulus. The supply
-- consists of distinct primes, so a successful image contributes one factor.
private def imageCount (A : Matrix Int n n) (bound fuel : Nat) : Option Nat := do
  let state ← A.detCrt? bound fuel
  let (product, count) := (ZMod64.primesBelow (2 ^ 31 - 1) fuel).foldl
    (fun (product, count) p =>
      if product < state.modulus then (product * p.m, count + 1)
      else (product, count)) (1, 0)
  if product = state.modulus then some count else none

private def imageCounts (c : ModularMatrixFixtures.Case) : Option (Nat × Nat) := do
  let fuel := c.matrix.rowNormBound.log2 / 30 + 2
  let row ← imageCount c.matrix c.matrix.rowNormBound fuel
  let hadamard ← imageCount c.matrix c.matrix.hadamardBound fuel
  return (row, hadamard)

#guard ModularMatrixFixtures.cases.all fun c =>
  match imageCounts c with
  | some (row, hadamard) => hadamard ≤ row
  | none => false

/-- info: [("empty", some (1, 1)),
 ("singleton-negative", some (1, 1)),
 ("zero", some (1, 1)),
 ("singular", some (1, 1)),
 ("swap-sign", some (1, 1)),
 ("modulus", some (2, 2)),
 ("two-bad-primes", some (3, 3)),
 ("large-small-determinant", some (133, 133)),
 ("scaled-hadamard", some (3, 3)),
 ("structured-determinant/8", some (1, 1)),
 ("dense-random-determinant/8-bit", some (2, 1)),
 ("dense-random-determinant/64-bit", some (9, 9)),
 ("dense-random-determinant/1024-bit", some (100, 100)),
 ("unimodular-determinant/positive", some (13, 13)),
 ("unimodular-determinant/negative", some (13, 13))] -/
#guard_msgs in
#eval ModularMatrixFixtures.cases.map fun c => (c.name, imageCounts c)

#guard (ModularMatrixFixtures.unimodular 6 64).detModular? 16 == some 1
-- Two zero residues are insufficient at this bound: the third image is required.
#guard ((ZMod64.primesBelow (2 ^ 31 - 1) 2).map (·.m)) == #[2147483647, 2147483629]
private def badPrimes : Matrix Int 1 1 := Matrix.ofFn fun _ _ =>
  (2147483647 : Int) * 2147483629
#guard (badPrimes.detModular? 2).isNone
#guard badPrimes.detModular? 3 == some ((2147483647 : Int) * 2147483629)
-- A zero determinant with a zero bound still requires an image and positive fuel.
#guard ((0 : Matrix Int 2 2).detBounded? 0 0).isNone
#guard (0 : Matrix Int 2 2).detBounded? 0 1 == some 0

end Hex.ModularMatrixConformance

namespace Hex.ModularMatrixSolveConformance

open Hex Hex.Matrix

-- The solve/divisor normaliser must remove a constructed common factor.
#guard Dixon.normalise #v[6, 9] 6 == (#v[2, 3], 2)
#guard Dixon.normalise #v[0, 0] 6 == (#v[0, 0], 1)
#guard Dixon.check (Matrix.identity 2) #v[2, 3] #v[6, 9] 3 == some (#v[2, 3], 1)

local instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
local instance : ZMod64.Bounds 6 := ⟨by decide, by decide⟩

#guard (decompAt? (Matrix.identity 2) 2 (by decide)).isSome
#guard (decompAt? (Matrix.identity 0) 2 (by decide)).isSome
#guard (decompAt? (0 : Matrix Int 2 2) 2 (by decide)).isNone
#guard (decompAt? (Matrix.ofFn fun i j : Fin 2 =>
  if i = j then 5 else 0) 6 (by decide)).isSome

-- Over a composite ring, invertibility alone need not provide a unit entry
-- in the pivot column: det([[2,3],[3,2]]) = -5 is a unit modulo six.
#guard (decompAt? (Matrix.ofFn fun i j : Fin 2 =>
  if i = j then 2 else 3) 6 (by decide)).isNone

-- Assert that the optimised elimination routes themselves succeed.
private def wordA : Matrix (ZMod64 2) 2 2 :=
  Matrix.ofFn fun i j => if i.val = 1 && j.val = 1 then 0 else 1
#guard ((Dixon.fastReduce? wordA).map (·.echelon)) == some (Matrix.identity 2)
#guard Dixon.flatDet? wordA == some 1

private def A : Matrix Int 2 2 := Matrix.ofFn fun i j =>
  if i.val = 0 then (if j.val = 0 then 2 else 3) else if j.val = 0 then 0 else 1

#guard numeratorBound A #v[0, 1] == 4
#guard solve? A #v[0, 1] 1 == some (#v[-3, 2], 2)
#guard solve? A #v[0, 0] 1 == some (#v[0, 0], 1)
#guard solve? (Matrix.identity 0) #v[] 1 == some (#v[], 1)
#guard (solve? A #v[0, 1] 0).isNone
#guard solveMat? A (Matrix.identity 2) 1 ==
  some (Matrix.ofFn (fun i j : Fin 2 =>
    if i.val = 0 then (if j.val = 0 then 1 else -3) else if j.val = 0 then 0 else 2), 2)
#guard solveMat? A (0 : Matrix Int 2 0) 1 == some (0, 1)
#guard (A.detViaDivisorWith (Rand.ofSeed 1) 1).1 == some 2
#guard ModularMatrix.detWith A 1 1 true == ⟨2, .divisor, []⟩
#guard ModularMatrix.detViaDivisor A 1 == 2
#guard ModularMatrix.detWith A 0 1 true == ⟨2, .divisor, [.modular, .bareiss]⟩

-- Exercise the divisor route with a deliberately non-reduced solution 3/6.
-- Without reduction, 6 does not divide det([2]) and the reconstructed answer is wrong.
#guard ((decomp? (Matrix.ofFn fun _ _ : Fin 1 => (2 : Int)) 1).bind fun D =>
  Dixon.cofactorWith D #v[1] #v[3] 6 1) == some 2


private def checkSolve (c : ModularMatrixFixtures.Case) : Bool := Id.run do
  let A := c.matrix
  let b : Vector Int c.n := Vector.ofFn fun i => (i.val + 1 : Nat)
  let fuel := A.solveFuel + 2
  match A.decomp? fuel with
  | none => return A.bareiss == 0
  | some D =>
    for rhs in [b, A.mulVec b, Vector.replicate c.n 0] do
      match solveWith D rhs, solve? A rhs fuel, solveWitness? A rhs fuel with
      | some (y, d), some pair, some w =>
        if pair != (y, d) || w.num != y || w.den != d ||
            A.mulVec y != d • rhs || d ≤ 0 || Dixon.common y d != 1 then return false
      | _, _, _ => return false
    for cols in [0, 1, 3, c.n] do
      let C : Matrix Int c.n cols := Matrix.ofFn fun i j => (i.val + j.val + 1 : Nat)
      match solveMatWith D C, solveMat? A C fuel with
      | some (X, d), some pair =>
        if pair != (X, d) || A * X != d • C || d ≤ 0 ||
            Dixon.common (Dixon.flatten X) d != 1 then return false
      | _, _ => return false
    return true

private def checkDivisor (c : ModularMatrixFixtures.Case) : Bool :=
  let expected := c.matrix.bareiss
  [0, 42].all fun seed =>
    let result := ModularMatrix.detWith c.matrix (ModularMatrix.defaultFuel c.matrix) seed true
    result.value == expected && (expected == 0 || result.rest.isEmpty)

#guard ModularMatrixFixtures.cases.all checkDivisor

#guard ModularMatrixFixtures.cases.all checkSolve

-- The zero-fuel result is resource failure, including for invertible inputs.
#guard (solveWitness? A #v[0, 1] 0).isNone
#guard (solveMat? A (Matrix.identity 2) 0).isNone

private def checkPrecision : Bool :=
  match decompAt? A 2 (by decide) with
  | some _ => false -- det A is divisible by 2
  | none =>
    match decomp? A 1 with
    | none => false
    | some D =>
      let P := numeratorBound A #v[0, 1]
      let Q := hadamardBound A
      let k := Dixon.digits D P Q
      k > 0 && D.p ^ k > 2 * P * Q && D.p ^ (k - 1) ≤ 2 * P * Q &&
        (List.finRange 2).all (fun i =>
          ((A.mulVec (D.lift #v[0, 1] k))[i] - (#v[0, 1] : Vector Int 2)[i]) %
            ((D.p : Int) ^ k) == 0)
#guard checkPrecision

-- A denominator sharing a factor with the modulus must be skipped.
#guard ((decomp? A 1).map fun D => (Dixon.cofactorImage D 2 6).isNone) == some true
#guard ((decomp? A 1).map fun D => (Dixon.cofactorImage D 2 7).isSome) == some true
-- A generous budget still stops at the modulus allowed by the production bound.
#guard ((decomp? A 1).bind fun D =>
  (Dixon.cofactorState D #v[0, 1] #v[-3, 2] 2 8).map fun (d, s) =>
    (d, s.value[0], s.modulus == D.p)) == some (2, 1, true)

private def largeCofactor : Matrix Int 2 2 := Matrix.ofFn fun i j =>
  if i != j then 0 else if i.val = 0 then 2 else 2 ^ 32
#guard ((decomp? largeCofactor 1).bind fun D =>
  (Dixon.cofactorState D #v[1, 0] #v[1, 0] 2 8).map fun (d, s) =>
    let second := ((ZMod64.primesBelow (2 ^ 31 - 1) 8).map (·.m))[1]!
    (d, s.value[0], s.modulus == D.p * second)) == some (2, 2 ^ 32, true)
#guard ((decomp? A 1).map fun D => (Dixon.cofactorCrt? D 2 1 0).isNone) == some true

private def unlucky : Matrix Int 1 1 := Matrix.ofFn fun _ _ =>
  (2147483647 : Int) * 2147483629
#guard (unlucky.decomp? 2).isNone
#guard (unlucky.decomp? 3).map (·.p) == some 2147483587
#guard unlucky.solve? #v[1] 3 == some (#v[1], (2147483647 : Int) * 2147483629)

end Hex.ModularMatrixSolveConformance

namespace Hex.ModularMatrixRankTests

open scoped Hex

private def checkRankCase (c : ModularMatrixFixtures.RankCase) : Bool :=
  match c.matrix.rankCert? 3, c.matrix.kernel? 3 with
  | some cert, some K =>
    cert.rank == c.rank && c.matrix.checkRank cert &&
    c.matrix.rankModular == c.rank && c.matrix.checkRank K.cert &&
    K.cert.rank == c.rank &&
    K.freeCols.toList == Matrix.Kernel.complement K.cert.cols &&
    c.matrix * K.basis == Matrix.zero c.n (c.m - K.cert.rank) &&
    (List.finRange (c.m - K.cert.rank)).all (fun i =>
      (List.finRange (c.m - K.cert.rank)).all (fun j =>
        K.basis[(K.freeCols[i], j)] == if i = j then -K.cert.denom else 0))
  | _, _ => false

#guard ModularMatrixFixtures.rankCases.all checkRankCase
#guard ModularMatrixFixtures.rankCases.all fun c =>
  (c.matrix.rankCert? 0).isNone && (c.matrix.kernel? 0).isNone

private def bad := ModularMatrixFixtures.rankMatrix 4 6 2 256 true
#guard (bad.rankCert? 1).isNone
#guard (bad.rankCert? 2).isNone
#guard (bad.rankCert? 3).map (·.rank) == some 2

-- Exhaust the complete public budget, forcing the exact integer fallback.
private def obstructed : Matrix Int 1 1 :=
  let d := (ZMod64.primesBelow (2 ^ 31 - 1) Matrix.rankFuel).foldl
    (fun a q => a * (q.m : Int)) 1
  Matrix.ofFn fun _ _ => d
#guard (obstructed.rankCert? Matrix.rankFuel).isNone
#guard obstructed.rankModular == 1

-- Solving against identity gives denominator 2; the certificate must store det = 4.
private def twiceIdentity : Matrix Int 2 2 := #m[2, 0; 0, 2]
#guard (twiceIdentity.rankCert? 1).map (·.denom) == some 4
#guard (twiceIdentity.rankCert? 1).map (fun c => c.adj.rows.toList.map (·.toList)) ==
  some ([[2, 0], [0, 2]] : List (List Int))

-- The SPEC's noninitial selected column checks placement, signs, and scale.
private def exampleMatrix : Matrix Int 2 3 := #m[2, 4, 6; 4, 8, 12]
private def exampleCert : Matrix.RankCert Int 2 3 := ⟨1, #v[1], #v[1], 8, #m[1]⟩
private theorem exampleCheck : exampleMatrix.checkRank exampleCert = true := by decide +kernel
private def exampleKernel := Matrix.Kernel.ofCert exampleMatrix exampleCert exampleCheck
#guard exampleKernel.freeCols == #v[0, 2]
#guard exampleKernel.basis == #m[-8, 0; 4, 12; 0, -8]
#guard exampleMatrix * exampleKernel.basis == 0

-- Permuted pivot selections and noncanonical common scale remain valid inputs.
private def permutedMatrix : Matrix Int 2 3 := #m[1, 0, 3; 0, 1, 5]
private def permutedCert : Matrix.RankCert Int 2 3 := ⟨2, #v[1, 0], #v[1, 0], -2, #m[-2, 0; 0, -2]⟩
private theorem permutedCheck : permutedMatrix.checkRank permutedCert = true := by decide +kernel
private def permutedKernel := Matrix.Kernel.ofCert permutedMatrix permutedCert permutedCheck
#guard permutedKernel.freeCols == #v[2]
#guard permutedKernel.basis == #m[-6; -10; 2]
#guard permutedMatrix * permutedKernel.basis == 0

local instance : ZMod64.Bounds 7 := ⟨by decide, by decide⟩
local instance : ZMod64.PrimeModulus 7 := ⟨by decide +kernel⟩
#guard (exampleMatrix.mapEntries (ZMod64.intCast 7)).rankModP == 1

end Hex.ModularMatrixRankTests
