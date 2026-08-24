/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMinPoly
import HexMinPoly.Fixtures
import HexPolyFp.PrimeField

/-!
# HexMinPoly conformance contract

- **Oracle:** python-flint `fmpz_mat.minpoly` and `fmpq_mat.minpoly`.
- **Mode:** required in CI through `scripts/ci/run_oracles.sh`.
- **Covered operations:** `evalVec`, `krylovVec`, `krylovMat`, `krylovDeg`,
  `krylovCoeffs?`, `dependencyPoly`, `vecMinPoly`, `minPoly`,
  `checkRightInverse`, `minPolyCert`, and `MinPolyCert.check`.
- **Covered properties:** Krylov iteration and shared-row agreement, first
  dependency reconstruction, annihilation, monicity/minimality, certificate
  acceptance, and rejection of corrupted certificate components.
- **Covered edge cases:** empty and scalar matrices, zero vectors, zero and
  identity matrices, nilpotent Jordan chains, repeated eigenvalues, small
  prime fields, larger nonminimal annihilators, and malformed witnesses.
-/

namespace Hex.MinPolyConformance

open Hex Matrix

private def p (xs : List Rat) : DensePoly Rat := DensePoly.ofList xs

private def scalar (a : Rat) : Matrix Rat 1 1 :=
  Matrix.ofFn fun _ _ => a

private def zero3 : Matrix Rat 3 3 := 0

private def identity3 : Matrix Rat 3 3 := Matrix.identity 3

private def nilpotent2 : Matrix Rat 2 2 :=
  Matrix.ofFn fun i j => if i.val = 0 && j.val = 1 then 1 else 0

private def nilpotent4 : Matrix Rat 4 4 :=
  Matrix.ofFn fun i j => if i.val + 1 = j.val then 1 else 0

private def diagonal112 : Matrix Rat 3 3 :=
  Matrix.ofFn fun i j =>
    if i = j then (if i.val < 2 then 1 else 2) else 0

private def zero2 : Matrix Rat 2 2 := 0

private def annihilatesBasis2 (q : DensePoly Rat) (A : Matrix Rat 2 2) : Bool :=
  (List.finRange 2).all fun i =>
    decide (Matrix.evalVec q A (Matrix.basisVec 2 i) = 0)

private def divides (q r : DensePoly Rat) : Bool :=
  decide ((DensePoly.divMod r q).2 = 0)

private def e0 : Vector Rat 2 := #v[1, 0]
private def e1 : Vector Rat 2 := #v[0, 1]

-- Direct polynomial-vector evaluation: typical, edge, and cancellation cases.
#guard Matrix.evalVec (p [1, 1]) nilpotent2 e1 == #v[1, 1]
#guard Matrix.evalVec (p []) zero2 e0 == #v[0, 0]
#guard Matrix.evalVec (p [0, 0, 1]) nilpotent2 e1 == #v[0, 0]

-- Krylov iteration and the shared row materialization agree on three shapes.
#guard Matrix.krylovVec nilpotent2 e1 1 == e0
#guard Matrix.krylovVec nilpotent2 e1 2 == #v[0, 0]
#guard Matrix.krylovVec (scalar 7) #v[2] 2 == #v[98]
#guard (Matrix.krylovMat nilpotent2 e1 3).rows == #v[e1, e0, #v[0, 0]]
#guard (Matrix.krylovMat zero2 e0 2).rows == #v[e0, #v[0, 0]]
#guard (Matrix.krylovMat (0 : Matrix Rat 0 0) #v[] 0).rows == #v[]

-- Dependency coefficients: cyclic, eigenvector, and zero-vector cases.
#guard (Matrix.krylovCoeffs? nilpotent2 e1).map Vector.toList == some [0, 0]
#guard (Matrix.krylovCoeffs? identity3 (Matrix.basisVec 3 ⟨0, by decide⟩)).map
  Vector.toList == some [1]
#guard (Matrix.krylovCoeffs? identity3 (0 : Vector Rat 3)).map Vector.toList == some []
#guard Matrix.dependencyPoly (#v[2, 3] : Vector Rat 2) == p [-2, -3, 1]
#guard Matrix.dependencyPoly (#v[] : Vector Rat 0) == p [1]
#guard Matrix.dependencyPoly (#v[-4] : Vector Rat 1) == p [4, 1]

#guard Matrix.minPoly (0 : Matrix Rat 0 0) == p [1]
#guard Matrix.minPoly (scalar 0) == p [0, 1]
#guard Matrix.minPoly (scalar 7) == p [-7, 1]
#guard Matrix.minPoly zero3 == p [0, 1]
#guard Matrix.minPoly identity3 == p [-1, 1]
#guard Matrix.minPoly nilpotent2 == p [0, 0, 1]
#guard Matrix.minPoly nilpotent4 == p [0, 0, 0, 0, 1]
#guard Matrix.minPoly diagonal112 == p [2, -3, 1]

-- Annihilation plus divisibility into the characteristic polynomial does not
-- certify minimality: x^2 passes both tests on the 2-by-2 zero matrix, while
-- the executable minimal polynomial is x.
#guard annihilatesBasis2 (p [0, 0, 1]) zero2
#guard divides (p [0, 0, 1]) (p [0, 0, 1])
#guard Matrix.minPoly zero2 != p [0, 0, 1]

-- A single basis vector misses the second step of the Jordan chain.
#guard Matrix.vecMinPoly nilpotent2 (Matrix.basisVec 2 ⟨0, by decide⟩) == p [0, 1]
#guard Matrix.minPoly nilpotent2 != p [0, 1]

-- The public vector operation handles the zero vector independently of `minPoly`.
#guard Matrix.krylovDeg identity3 (0 : Vector Rat 3) == 0
#guard Matrix.vecMinPoly identity3 (0 : Vector Rat 3) == p [1]

-- The public vector order has typical, edge, and adversarial chain coverage.
#guard Matrix.vecMinPoly nilpotent2 e1 == p [0, 0, 1]
#guard Matrix.vecMinPoly identity3 (Matrix.basisVec 3 ⟨2, by decide⟩) == p [-1, 1]

private def certifies {n : Nat} (A : Matrix Rat n n) : Bool :=
  (Matrix.minPolyCert A).check A

private def intToRat {n m : Nat} (M : Matrix Int n m) : Matrix Rat n m :=
  Matrix.ofRows (M.rows.map (fun row => row.map (fun x => ((x : Int) : Rat))))

private def certifiesCase (c : Hex.MinPolyFixtures.Case) : Bool :=
  certifies (intToRat c.matrix)

#guard certifies (0 : Matrix Rat 0 0)
#guard certifies (scalar 0)
#guard certifies (scalar 7)
#guard certifies zero3
#guard certifies identity3
#guard certifies nilpotent2
#guard certifies nilpotent4
#guard certifies diagonal112

-- Every oracle fixture exercises the division-free producer/checker path,
-- including the block, companion, transpose, similarity, and large-integer
-- stress cases that are not duplicated as local named matrices above.
#guard Hex.MinPolyFixtures.all.all certifiesCase

private def scalarSevenCert := Matrix.minPolyCert (scalar 7)

private def badInverseCert : Matrix.MinPolyCert Rat 1 :=
  let c := scalarSevenCert
  { c with order := Vector.ofFn fun i => { c.order.get i with inv := 0 } }

private def badOrderCert : Matrix.MinPolyCert Rat 1 :=
  let c := scalarSevenCert
  { c with order := Vector.ofFn fun i => { c.order.get i with poly := p [1] } }

private def badBezoutCert : Matrix.MinPolyCert Rat 1 :=
  let c := scalarSevenCert
  { c with steps := Vector.ofFn fun i => { c.steps.get i with bezoutLeft := 0 } }

private def nonmonicClaimCert : Matrix.MinPolyCert Rat 1 :=
  { scalarSevenCert with poly := p [1, 2] }

-- The checker accepts valid right inverses, including the empty one, and
-- rejects a rank-deficient candidate.
#guard Matrix.checkRightInverse (Matrix.identity (R := Rat) 2)
  (Matrix.identity (R := Rat) 2)
#guard Matrix.checkRightInverse (0 : Matrix Rat 0 0) (0 : Matrix Rat 0 0)
#guard !Matrix.checkRightInverse (Matrix.identity (R := Rat) 2) (0 : Matrix Rat 2 2)

-- Hostile certificate mutations must all be rejected.
#guard !badInverseCert.check (scalar 7)
#guard !badOrderCert.check (scalar 7)
#guard !badBezoutCert.check (scalar 7)
#guard !nonmonicClaimCert.check (scalar 7)

private instance primeModulusTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime (by decide)

private def nilpotent2Mod : Matrix (ZMod64 2) 2 2 :=
  Matrix.ofFn fun i j => if i.val = 0 && j.val = 1 then 1 else 0

-- The repeated factor x^2 is retained over the small field, and its produced
-- certificate follows the same checker path as characteristic-zero inputs.
#guard DensePoly.beqCoeffs (Matrix.minPoly nilpotent2Mod)
  (#p[0, 0, 1] : DensePoly (ZMod64 2))
#guard (Matrix.minPolyCert nilpotent2Mod).check nilpotent2Mod

end Hex.MinPolyConformance
