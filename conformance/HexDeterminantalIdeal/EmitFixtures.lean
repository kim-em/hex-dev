/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexDeterminantalIdealFixtures

/-!
JSONL emit driver for the `hex-determinantal-ideal` SymPy oracle.

One `mvpolymatrix` record per committed matrix and minor size, followed by
the enumerated minors, the determinantal-ideal generators, and — for the
cases that carry points — the rank of the specialisation and the decision of
the rank-drop locus at each point.
-/

namespace Hex.DeterminantalIdealEmit

open Hex
open Hex.Conformance.Emit
open Hex.MvPoly
open Hex.DeterminantalIdealFixtures

private def lib : String := "HexDeterminantalIdeal"

private def wireTerms {k : Nat} (p : P k) : List (List Nat × Int) :=
  p.termsList.map fun term => (term.1.toList, term.2)

private def wireMatrix {k n m : Nat} (A : Matrix (P k) n m) :
    List (List (List (List Nat × Int))) :=
  A.rows.toList.map fun row => row.toList.map wireTerms

private def emitCase (c : Case) : IO Unit := do
  emitMvPolyMatrixFixture lib c.id c.arity "grlex" c.rows c.cols
    (wireMatrix c.matrix) c.r
  emitResult lib c.id "minors"
    (mvPolyListValue ((Matrix.minors c.r c.matrix).map wireTerms))
  emitResult lib c.id "detIdealGens"
    (mvPolyListValue ((Matrix.detIdealGens c.r c.matrix).map wireTerms))
  let lifted := toRat c.matrix
  for v in c.points do
    let p := pointOf v
    emitResult lib c.id ("rankAt/" ++ pointName v)
      (intListValue [Int.ofNat (Matrix.rankAt lifted p)])
    emitResult lib c.id ("inLocus/" ++ pointName v)
      (boolValue (decide (Matrix.InLocus c.r lifted p)))

private def emitAll : IO Unit :=
  cases.forM emitCase

end Hex.DeterminantalIdealEmit

def main : IO Unit :=
  Hex.DeterminantalIdealEmit.emitAll
