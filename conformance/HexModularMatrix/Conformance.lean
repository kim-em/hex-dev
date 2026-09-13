/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModularMatrix.Fixtures

/-!
Oracle: `scripts/oracle/modmat_flint.py` (FLINT integer determinants).
Mode: always
Covered operations: `detMod?`, `detBounded?`, `detModular?`, `detWith`, `det`.
Covered properties: modular residues, strict-bound reconstruction, bound ordering,
modular success, recorded Bareiss fallback, agreement with the integer oracle.
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
