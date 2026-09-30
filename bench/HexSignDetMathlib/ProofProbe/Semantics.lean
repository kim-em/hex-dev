/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootModel
public import HexRealRootsMathlib.RealClosed
public import HexSignDetMathlib.ProofProbe.Inputs

public section

namespace Hex.SignDetMathlib.ProofProbe.Semantics
open Hex Hex.SignDet Hex.SignDet.Conformance HexPolyMathlib.Interpret HexRealRootsMathlib

theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

/-- The actual finite root set specified by the literal descriptor, independent of
its proposed sign counts. -/
@[expose] noncomputable def roots : Finset ℝ :=
  Tarski.rootsIn (interpret (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) singletonRaw.head)
    (singletonRaw.lower.map fun r : Rat => (r : ℝ))
    (singletonRaw.upper.map fun r : Rat => (r : ℝ))

/-- Ordered query sign condition at a mathematical root. -/
@[expose] noncomputable def signCondition (depth : Nat) (x : ℝ) : List Int :=
  signsAt (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (List.replicate (2 ^ depth) (DensePoly.C (2 : Rat))) x

end Hex.SignDetMathlib.ProofProbe.Semantics
