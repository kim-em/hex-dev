/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyZGcd

/-!
Core conformance checks for checked integer-polynomial gcd.

Oracle: SymPy `Poly.gcd`, exact division, cofactors, and square-free parts
Mode: always
Covered operations:
- `divExact?`, `checkCoprime`, and `checkGcd`
- `coprimeCert?`, `heuCandidateAt?`, `brownOffer`, and `prsCert?`
- `structuralReduction?`, `restoreStructural?`, and `gcdCert`
- `gcd`, `cofactors`, `isCoprime`, `gcdList`, `lcm`, and `ratGcd`
- `sqfDecomp`
Covered properties:
- every accepted producer result passes the independent certificate checker
- the structural factor is restored after gcd search on the reduced inputs
- public gcds divide both inputs and the returned cofactors reassemble them
- rational gcds are monic and square-free parts reassemble the primitive input
Covered edge cases:
- two zero inputs, one zero input, units, and nonzero constants
- common scalar content and a pure power of `x`
- bad and unlucky Brown primes, including a smaller-degree restart
- false heuristic candidates rejected by exact trial division
- rational inputs with large pairwise-coprime denominators
- zero, square-free, and repeated-factor square-free decompositions
-/

namespace Hex.ZPoly.Conformance

open Hex
open Hex.DensePoly
open Hex.ZPoly

private def z (coeffs : List Int) : ZPoly := DensePoly.ofList coeffs

private def gcdContract (f h expected : ZPoly) : Bool :=
  let cert := gcdCert f h
  checkGcd f h cert && cert.gcd == expected &&
    expected * cert.cofL == f && expected * cert.cofR == h &&
    gcd f h == expected && cofactors f h == (cert.cofL, cert.cofR)

/-! Exact division and certificate replay. -/

#guard divExact? (z [2, 3, 1]) (z [1, 1]) = some (z [2, 1])
#guard (divExact? (z [1, 0, 1]) (z [1, 1])).isNone
#guard (divExact? (z [1, 2]) 0).isNone

#guard checkGcd (0 : ZPoly) 0 zeroGcdCert
#guard
  let f := z [2, 4, 2]
  checkGcd f 0 (rationalGcdCert f 0)
#guard
  let common := z [1, 1]
  let f := common * z [2, 1]
  let h := common * z [3, 1]
  checkGcd f h (gcdCert f h)

/-! Coprime and heuristic routes: success, genuine non-coprimality, and a
false evaluated factor which the checker must reject. -/

#guard (coprimeCert? (z [1, 1]) (z [2, 1])).isSome
#guard (coprimeCert? (z [1, 0, 1]) (z [1, 1, 1])).isSome
#guard
  let common := z [1, 1]
  (coprimeCert? (common * z [2, 1]) (common * z [3, 1])).isNone

#guard
  let common := z [1, 1]
  let f := common * z [2, 1]
  let h := common * z [3, 1]
  match heuCandidateAt? f h 101 with
  | some candidate => (checkedCandidate? f h candidate).isSome
  | none => false
#guard
  match heuCandidateAt? (z [0, 1]) (z [5, 1]) 5 with
  | some candidate => (checkedCandidate? (z [0, 1]) (z [5, 1]) candidate).isNone
  | none => false
#guard (heuCandidateAt? (1 : ZPoly) 1 0).isNone &&
  (heuCandidateAt? (1 : ZPoly) 1 1).isNone

/-! Brown route traps.  The prime constructors come from the independently
proved bundled supply, so no handwritten primality witness enters the test. -/

private def primeAt? (p : Nat) : Option ZMod64.Prime :=
  (ZMod64.primesBelow p 1)[0]?

#guard
  match primeAt? 2 with
  | some p => (brownImage? (z [1, 2]) (z [3, 2]) p).isNone
  | none => false

#guard
  match primeAt? 2, primeAt? 3 with
  | some p2, some p3 =>
      match brownOffer (z [0, 1]) (z [2, 1]) none p2 with
      | .accumulated state =>
          match brownOffer (z [0, 1]) (z [2, 1]) (some state) p3 with
          | .restarted _ => true
          | _ => false
      | _ => false
  | _, _ => false

#guard
  let common := z [1, 2]
  let f := common * z [1, 1]
  let h := common * z [2, 1]
  match primeAt? 5 with
  | some p =>
      match brownImage? f h p with
      | some image => image.coeffs == #[1, 2]
      | none => false
  | none => false

/-! The deterministic PRS route, including its genuinely empty raw chain at
`(0, 0)`. -/

#guard
  let common := z [2, 1]
  let f := common * z [1, 2]
  let h := common * z [1, 3]
  match prsCert? f h with
  | some cert => cert.gcd == common && checkGcd f h cert
  | none => false
#guard
  match prsCert? (0 : ZPoly) 0 with
  | some cert => checkGcd 0 0 cert
  | none => false
#guard (prsTerminal? (0 : ZPoly) 0).isNone

/-! Structural reduction and public gcd/cofactor contracts. -/

#guard gcdContract 0 0 0
#guard
  let f := z [6, -3]
  gcdContract f 0 (z [-6, 3])
#guard
  let common := z [2, 1]
  gcdContract (common * z [1, 2]) (common * z [1, 3]) common
#guard gcdContract (z [0, 12]) (z [0, 18]) (z [0, 6])

#guard
  let f := z [0, 0, 0, 12, 12]
  let h := z [0, 0, 36, 18]
  match structuralReduction? f h with
  | none => false
  | some reduced =>
      reduced.factor == z [0, 0, 6] &&
        match prsCert? reduced.left reduced.right with
        | none => false
        | some cert =>
            match restoreStructural? f h reduced cert with
            | some restored => restored.gcd == z [0, 0, 6] && checkGcd f h restored
            | none => false

#guard isCoprime (z [1, 1]) (z [2, 1])
#guard !isCoprime (z [2, 3, 1]) (z [3, 4, 1])
#guard isCoprime 1 (z [0, 2, 4])

#guard gcdList ([] : List ZPoly) == 0
#guard gcdList [z [0, 2], z [0, 4]] == z [0, 2]
#guard gcdList [z [0, 6], z [0, 9], z [0, 15]] == z [0, 3]

#guard lcm (0 : ZPoly) (z [1, 1]) == 0
#guard lcm (z [0, 2]) (z [0, 4]) == z [0, 4]
#guard lcm (z [1, 1]) (z [2, 1]) == z [2, 3, 1]

/-! Rational clearing and monic normalization. -/

#guard
  ratGcd (DensePoly.ofList [1, 2]) (DensePoly.ofList [2, 4]) ==
    DensePoly.ofList [1 / 2, 1]
#guard
  let common : DensePoly Rat := DensePoly.ofList [(1 : Rat) / 1000003, 1]
  let f := common * DensePoly.ofList [(1 : Rat) / 1000033, 1]
  let h := common * DensePoly.ofList [(1 : Rat) / 1000037, 1]
  ratGcd f h == common
#guard ratGcd (0 : DensePoly Rat) 0 == 0

/-! Fast primitive square-free normalization. -/

#guard
  let x1 := z [1, 1]
  let x2 := z [2, 1]
  let d := sqfDecomp (x1 * x1 * x2)
  d.repeatedPart == x1 && d.squareFreeCore == x1 * x2
#guard
  let f := z [1, 0, 1]
  let d := sqfDecomp f
  d.repeatedPart == 1 && d.squareFreeCore == f
#guard
  let d := sqfDecomp (0 : ZPoly)
  d.primitive == 0 && d.squareFreeCore == 0 && d.repeatedPart == 0

end Hex.ZPoly.Conformance
