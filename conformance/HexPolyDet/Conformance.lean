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

def modCases (k : Nat) (h : 2 ≤ k) :=
  let x : Mv k Mod := MvPoly.X ⟨0, by omega⟩
  let y : Mv k Mod := MvPoly.X ⟨1, by omega⟩
  let z := if hk : 2 < k then MvPoly.X ⟨2, hk⟩ else 1
  BareissCarriers.cases (MvPoly.C (2 : Mod) * x * y + y * z + 1)

def checkCases {k : Nat} {C : Type} [Lean.Grind.CommRing C]
    [DecidableEq C] [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [LawfulGcdOps C]
    (cs : List (String × (n : Nat) × Matrix (Mv k C) n n)) : Bool :=
  cs.all fun (_, ⟨n, A⟩) =>
    match PolyDet.polyDetWitness A with
    | .error _ => false
    | .ok w => PolyDet.check n (A.rows.toList.map (·.toList)) w &&
        decide (w.value = Matrix.det A) && decide (PolyDet.polyDet A = w.value)

#guard checkCases (mvIntCases 2 (by decide))
#guard checkCases (mvIntCases 3 (by decide))
#guard checkCases (mvRatCases 2 (by decide))
#guard checkCases (mvRatCases 3 (by decide))
#guard checkCases (modCases 2 (by decide))
#guard checkCases (modCases 3 (by decide))

end Hex.PolyDetFixtures
