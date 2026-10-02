/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDet
import HexBareiss.Conformance

/-!
Oracle: `scripts/oracle/matrix_carriers.py` (`poly_det`, SymPy Berkowitz).
Mode: always
The retained transform and singular witness pass the compiled list checker;
their values agree with Leibniz on these finite fixtures. This is a runtime
conformance check, not a general producer correctness theorem.
-/

namespace Hex.PolyDetFixtures
open Hex.BareissCarriers

def extraCases (k : Nat) (h : 2 ≤ k) (C : Type) [Zero C] [One C] [Add C]
    [DecidableEq C] : List (String × (n : Nat) × Matrix (Mv k C) n n) :=
  let x : Mv k C := MvPoly.X ⟨0, by omega⟩
  let y : Mv k C := MvPoly.X ⟨1, by omega⟩
  [("dense", ⟨3, Matrix.ofFn fun i j =>
      if i.val = j.val then x else if (i.val + 1) % 3 = j.val then y else 1⟩),
   ("valuation_x_zero", ⟨3, Matrix.ofFn fun i j =>
      if i.val = j.val then (if i.val = 0 then x else y + 1) else 0⟩)]

def intCases (k : Nat) (h : 2 ≤ k) := mvIntCases k h ++ extraCases k h Int
def ratCases (k : Nat) (h : 2 ≤ k) := mvRatCases k h ++ extraCases k h Rat

def modCases (k : Nat) (h : 2 ≤ k) : List (String × (n : Nat) × Matrix (Mv k Mod) n n) :=
  let x : Mv k Mod := MvPoly.X ⟨0, by omega⟩
  let y : Mv k Mod := MvPoly.X ⟨1, by omega⟩
  let z := if hk : 2 < k then MvPoly.X ⟨2, hk⟩ else 1
  BareissCarriers.cases (MvPoly.C (2 : Mod) * x * y + y * z + 1) ++ extraCases k h Mod

def checkCases {k : Nat} {C : Type} [Lean.Grind.CommRing C]
    [DecidableEq C] [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (cs : List (String × (n : Nat) × Matrix (Mv k C) n n)) : Bool :=
  cs.all fun (_, ⟨n, A⟩) =>
    match PolyDet.polyDetWitness A with
    | .error _ => false
    | .ok w => PolyDet.check n (A.rows.toList.map (·.toList)) w &&
        decide (w.value = Matrix.det A) && decide (PolyDet.polyDet A = w.value)

#guard checkCases (intCases 2 (by decide))
#guard checkCases (intCases 3 (by decide))
#guard checkCases (ratCases 2 (by decide))
#guard checkCases (ratCases 3 (by decide))
#guard checkCases (modCases 2 (by decide))
#guard checkCases (modCases 3 (by decide))

end Hex.PolyDetFixtures
