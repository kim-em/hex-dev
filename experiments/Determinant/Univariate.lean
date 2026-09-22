/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Fixture

namespace Determinant.Univariate

open Hex

def dense : Matrix (DensePoly Int) 4 4 := Matrix.ofFn fun i j =>
  let c := (coefficients.getD i.val []).getD j.val (0, 0, 0)
  DensePoly.ofList [c.1, c.2.1, c.2.2]

abbrev Sparse := MvPoly 1 Int Mono.grevlex

def sparse : Matrix Sparse 4 4 := Matrix.ofFn fun i j =>
  let c := (coefficients.getD i.val []).getD j.val (0, 0, 0)
  MvPoly.C c.1 + MvPoly.C c.2.1 * MvPoly.X 0 + MvPoly.C c.2.2 * (MvPoly.X 0)^2

/-- Return the same normalized dense coefficient representation as the other
arms. Sparse-to-dense output conversion is part of this computation. -/
def sparseCoeffs (A : Matrix Sparse 4 4) : Array Int :=
  let terms := PolyDet.toList (PolyDet.polyDet A)
  let size := terms.foldl (fun d t => max d (t.1.headD 0 + 1)) 0
  DensePoly.ofCoeffs (Array.ofFn fun i : Fin size =>
    terms.foldl (fun c t => if t.1.headD 0 == i.val then t.2 else c) 0) |>.coeffs

/-- Direct Lagrange interpolation at nine distinct integer points. The degree
bound eight comes from this fixed 4x4 quadratic fixture. Matrix evaluation,
nine integer determinants, interpolation and integer output normalization are
all inside the call. This is not a general interpolation implementation. -/
def interpolate (A : Matrix (DensePoly Int) 4 4) : Option (Array Int) := Id.run do
  let mut result : DensePoly Rat := 0
  for i in [:9] do
    let value := (A.mapEntries (fun p => p.eval (i : Int))).bareiss
    let mut term : DensePoly Rat := DensePoly.C (value : Rat)
    for j in [:9] do
      if j != i then
        term := term * ((DensePoly.monomial 1 1) - DensePoly.C (j : Rat)) *
          DensePoly.C ((1 : Rat) / ((i : Rat) - (j : Rat)))
    result := result + term
  if result.coeffs.all (fun q => q.den == 1) then
    return some (DensePoly.ofCoeffs (result.coeffs.map (·.num))).coeffs
  return none

end Determinant.Univariate
