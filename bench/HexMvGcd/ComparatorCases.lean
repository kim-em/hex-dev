/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd.Matrix
import HexMvGcdFlint
import HexMvGcdSingular

/-!
Matched Hex/FLINT/Singular cases for every `hex-mv-gcd` Phase-4 family.

Each triple returns the same semantic result: canonical sparse GCD or quotient
terms, or the sorted squarefree multiplicity signature. Singular checks its
answer against the canonical expected polynomial inside the timed request;
FLINT returns its polynomial answer for direct comparison. Inputs are cached
outside the measured repetitions by each fixed benchmark's discarded warmup.
-/

namespace Hex.MvGcdBench.ComparatorCases

open Hex.MvPoly
open Hex.MvGcdBench.Families

def leanInt {n : Nat} (input : P n Int × P n Int) : IO Flint.IntTerms :=
  Flint.leanIntGcd input

def flintInt {n : Nat} (input : P n Int × P n Int) : IO Flint.IntTerms :=
  Flint.intGcd input

def singularInt {n : Nat} (input : P n Int × P n Int)
    (expected : P n Int) : IO Flint.IntTerms :=
  Singular.intGcd input expected

def leanRat {n : Nat} (input : P n Rat × P n Rat) : IO Flint.RatTerms :=
  Flint.leanRatGcd input

def flintRat {n : Nat} (input : P n Rat × P n Rat) : IO Flint.RatTerms :=
  Flint.ratGcd input

def singularRat {n : Nat} (input : P n Rat × P n Rat)
    (expected : P n Rat) : IO Flint.RatTerms :=
  Singular.ratGcd input expected

/-! Coprime pairs: one dense low-arity and one sparse high-arity endpoint. -/

def runLeanCoprimeDense2 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← Matrix.denseCoprime2.get)

def runFlintCoprimeDense2 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← Matrix.denseCoprime2.get)

def runSingularCoprimeDense2 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← Matrix.denseCoprime2.get) 1

def runLeanCoprimeSparse8 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← Matrix.sparseCoprime8.get)

def runFlintCoprimeSparse8 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← Matrix.sparseCoprime8.get)

def runSingularCoprimeSparse8 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← Matrix.sparseCoprime8.get) 1

/-! Dense Brown interpolation: canonical `3d5` and `4d5` inputs. -/

def dense4 : IO (P 4 Int × P 4 Int) :=
  Matrix.getCached Matrix.denseGcd4d5 fun _ => denseGcd 4 5

def runLeanDense3d5 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← Matrix.denseGcd3d5.get)

def runFlintDense3d5 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← Matrix.denseGcd3d5.get)

def runSingularDense3d5 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← Matrix.denseGcd3d5.get) (commonFactor 3)

def runLeanDense4d5 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← dense4)

def runFlintDense4d5 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← dense4)

def runSingularDense4d5 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← dense4) (commonFactor 4)

/-! Sparse-gap endpoints. The separate degree-4096 matrix cases measure one
bounded Brown image; these smaller cases keep the complete public-GCD call
finite for all three comparator implementations. -/

initialize sparse5d4 : IO.Ref (P 5 Int × P 5 Int) ←
  IO.mkRef (sparseGapGcd 5 4)
initialize sparse5d16 : IO.Ref (P 5 Int × P 5 Int) ←
  IO.mkRef (sparseGapGcd 5 16)

def runLeanSparse5d4 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← sparse5d4.get)

def runFlintSparse5d4 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← sparse5d4.get)

def runSingularSparse5d4 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← sparse5d4.get) (commonFactor 5)

def runLeanSparse5d16 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← sparse5d16.get)

def runFlintSparse5d16 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← sparse5d16.get)

def runSingularSparse5d16 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← sparse5d16.get) (commonFactor 5)

/-! Extended-PRS coefficient swell. -/

initialize swell3 : IO.Ref (P 2 Int × P 2 Int) ← IO.mkRef (swellGcd 3)
initialize swell5 : IO.Ref (P 2 Int × P 2 Int) ← IO.mkRef (swellGcd 5)

def swellCommon : P 2 Int := C 2 * X 0 + X 1 + 1

def runLeanSwell3 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← swell3.get)

def runFlintSwell3 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← swell3.get)

def runSingularSwell3 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← swell3.get) (polyNormalize swellCommon)

def runLeanSwell5 (_ : Unit) : IO Flint.IntTerms := do
  leanInt (← swell5.get)

def runFlintSwell5 (_ : Unit) : IO Flint.IntTerms := do
  flintInt (← swell5.get)

def runSingularSwell5 (_ : Unit) : IO Flint.IntTerms := do
  singularInt (← swell5.get) (polyNormalize swellCommon)

/-! Rational denominator-clearing endpoints. -/

def rational4 : IO (P 4 Rat × P 4 Rat) :=
  Matrix.getCached Matrix.rationalGcd4d5 fun _ => rationalGcd 4 5

def runLeanRational3d5 (_ : Unit) : IO Flint.RatTerms := do
  leanRat (← Matrix.rationalGcd3d5.get)

def runFlintRational3d5 (_ : Unit) : IO Flint.RatTerms := do
  flintRat (← Matrix.rationalGcd3d5.get)

def runSingularRational3d5 (_ : Unit) : IO Flint.RatTerms := do
  singularRat (← Matrix.rationalGcd3d5.get)
    (polyNormalize (rationalCommon 3))

def runLeanRational4d5 (_ : Unit) : IO Flint.RatTerms := do
  leanRat (← rational4)

def runFlintRational4d5 (_ : Unit) : IO Flint.RatTerms := do
  flintRat (← rational4)

def runSingularRational4d5 (_ : Unit) : IO Flint.RatTerms := do
  singularRat (← rational4) (polyNormalize (rationalCommon 4))

/-! Squarefree decomposition compares sorted multiplicity signatures. -/

def leanSquarefree {n : Nat} (polynomial : P n Int) : IO (List Nat) :=
  return (sqfDecomp polynomial).factors.map (·.multiplicity)

def runLeanSquarefree2m1 (_ : Unit) : IO (List Nat) := do
  leanSquarefree (← Matrix.squarefree2m1.get)

def runFlintSquarefree2m1 (_ : Unit) : IO (List Nat) := do
  Flint.intSquarefree (← Matrix.squarefree2m1.get)

def runSingularSquarefree2m1 (_ : Unit) : IO (List Nat) := do
  Singular.intSquarefree (← Matrix.squarefree2m1.get)

def runLeanSquarefree4m7 (_ : Unit) : IO (List Nat) := do
  leanSquarefree (← Matrix.squarefree4m7.get)

def runFlintSquarefree4m7 (_ : Unit) : IO (List Nat) := do
  Flint.intSquarefree (← Matrix.squarefree4m7.get)

def runSingularSquarefree4m7 (_ : Unit) : IO (List Nat) := do
  Singular.intSquarefree (← Matrix.squarefree4m7.get)

/-! Cofactor-heavy exact division. -/

initialize cofactor16 : IO.Ref (P 2 Int × P 2 Int × P 2 Int) ←
  IO.mkRef (cofactorHeavy 16)
initialize cofactor64 : IO.Ref (P 2 Int × P 2 Int × P 2 Int) ←
  IO.mkRef (cofactorHeavy 64)

def leanDiv (input : P 2 Int × P 2 Int × P 2 Int) : IO Flint.IntTerms :=
  match divExact? input.1 input.2.1 with
  | none => throw <| IO.userError "Hex exact division declined a divisible input"
  | some quotient => return Flint.intTerms quotient

def flintDiv (input : P 2 Int × P 2 Int × P 2 Int) : IO Flint.IntTerms :=
  Flint.intDiv input.1 input.2.1

def singularDiv (input : P 2 Int × P 2 Int × P 2 Int) : IO Flint.IntTerms :=
  Singular.intDiv input.1 input.2.1 input.2.2

def runLeanCofactor16 (_ : Unit) : IO Flint.IntTerms := do
  leanDiv (← cofactor16.get)

def runFlintCofactor16 (_ : Unit) : IO Flint.IntTerms := do
  flintDiv (← cofactor16.get)

def runSingularCofactor16 (_ : Unit) : IO Flint.IntTerms := do
  singularDiv (← cofactor16.get)

def runLeanCofactor64 (_ : Unit) : IO Flint.IntTerms := do
  leanDiv (← cofactor64.get)

def runFlintCofactor64 (_ : Unit) : IO Flint.IntTerms := do
  flintDiv (← cofactor64.get)

def runSingularCofactor64 (_ : Unit) : IO Flint.IntTerms := do
  singularDiv (← cofactor64.get)

end Hex.MvGcdBench.ComparatorCases
