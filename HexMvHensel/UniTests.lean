/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexMvHensel.Uni
import all HexPoly.Dense
import all HexPoly.Operations
import all HexPoly.Euclid.DivGcd
import all HexPoly.Euclid.MulRing
import all HexPolyFp.Field
import all HexModArith.Residue
import all HexModArith.Ring
import all HexModArith.Prime
import all HexArith.ExtGcd
import all HexModular.SymMod

section

/-!
Executable route checks, plus small kernel-reduction checks, for the
univariate Hensel layer.  They cover both the arbitrary-prime-power solver and
production of a lifted partial-fraction tuple; no certificate theorem is
trusted by the tests.
-/

namespace Hex.MvHensel.UniTests

open Hex
open scoped Hex

def x : ZPoly := DensePoly.ofCoeffs #[0, 1]
def xPlusOne : ZPoly := DensePoly.ofCoeffs #[1, 1]

/- The tuple `(1,-1)` solves `1*(x+1) + (-1)*x = 1`.  For right-hand side
`x`, the two degree-bounded residues are `(0,1)`. -/
#guard solveUni 5 [x, xPlusOne] [1, -1] x ==
  [0, DensePoly.C 1]

/- Unit-leading division is genuinely over the composite prime power rather
than a `ZMod64`: `3` is the symmetric inverse of `2` modulo `5`. -/
#guard remUnit? 5 (DensePoly.ofCoeffs #[0, 1])
  (DensePoly.ofCoeffs #[1, 2]) == some (DensePoly.C 2)

def prime5 : ZMod64.Prime where
  m := 5
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

def point0 : Fin 0 → Int := fun j => nomatch j

example : invMod? 2 5 = some (-2) := by
  unfold invMod? Hex.pureIntExtGcd
  decide +kernel

example :
    ({ main := 0, point := point0, prime := prime5, exponent := 3 } :
      Setup 0).modulus = 125 := by
  rfl

def liftWorks : Bool :=
  witnessOf?
    ({ main := 0, point := point0, prime := prime5, exponent := 3 } : Setup 0)
    [x, xPlusOne] == some [DensePoly.C 1, DensePoly.C 124]

/- The mod-5 tuple `(1,4)` lifts to `(1,124)` modulo `5^3`, maintaining
`1*(x+1) + 124*x = 1 (mod 125)` without reducing witnesses by their images. -/
#guard liftWorks

def rejectsRepeated : Bool :=
  (witnessOf?
    ({ main := 0, point := point0, prime := prime5, exponent := 2 } : Setup 0)
    [x, x]).isNone

/- Repeated images have no partial-fraction tuple over the residue field. -/
#guard rejectsRepeated

def rejectsDegreeDrop : Bool :=
  (witnessOf?
    ({ main := 0, point := point0, prime := prime5, exponent := 2 } : Setup 0)
    [DensePoly.ofCoeffs #[1, 5], xPlusOne]).isNone

/- A leading coefficient killed by the residue prime is rejected before the
extended-gcd route can silently change degrees. -/
#guard rejectsDegreeDrop

end Hex.MvHensel.UniTests
