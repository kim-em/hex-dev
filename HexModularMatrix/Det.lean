/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Reconstruction
public import HexModularMatrix.Divisor
public import HexBareiss.Bareiss

public section

namespace Hex.ModularMatrix

/-- Determinant methods recorded by the dispatcher. -/
inductive Method where
  | modular | divisor | bareiss
  deriving Repr, BEq, DecidableEq

/-- A determinant value and the methods attempted in order. The final method
in `first :: rest` supplies the value. -/
structure DetData where
  value : Int
  first : Method
  rest : List Method
  deriving Repr, BEq, DecidableEq

/-- Try bounded modular reconstruction, then use Bareiss on exhaustion. -/
def ordinaryWith (A : Matrix Int n n) (fuel : Nat) : DetData :=
  match A.detModular? fuel with
  | some d => ⟨d, .modular, []⟩
  | none => ⟨A.bareiss, .modular, [.bareiss]⟩

/-- Default reproducible random seed for the divisor route. -/
def defaultSeed : Nat := 0

/-- Try the optional seeded divisor route, ordinary CRT, then Bareiss.
The route records every attempted method and its final supplier. -/
def detWith (A : Matrix Int n n) (fuel : Nat) (seed : Nat := defaultSeed)
    (useDivisor : Bool := false) : DetData :=
  if useDivisor then
    match (A.detViaDivisorWith (Rand.ofSeed seed) fuel).1 with
    | some d => ⟨d, .divisor, []⟩
    | none =>
      let result := ordinaryWith A fuel
      ⟨result.value, .divisor, result.first :: result.rest⟩
  else ordinaryWith A fuel

/-- The default budget allows roughly one 30-bit image per bound word, with
two spare images and a cap of 16384. Exhaustion always dispatches to Bareiss. -/
def defaultFuel (A : Matrix Int n n) : Nat :=
  min 16384 (A.hadamardBound.log2 / 30 + 2)

/-- The total integer determinant, with Bareiss as the finite-supply fallback. -/
@[expose]
def det (A : Matrix Int n n) : Int := (detWith A (defaultFuel A)).value

/-- First measured structured rung where the divisor route beats Bareiss. -/
@[expose] def divisorCrossover : Nat := 192

/-- Use Bareiss below the measured crossover, and a seeded Dixon divisor above it.
`detWith ... true` remains the explicit way to force a divisor attempt at any size. -/
@[expose] def detViaDivisor (A : Matrix Int n n) (seed : Nat) : Int :=
  if n < divisorCrossover then A.bareiss
  else (detWith A (defaultFuel A) seed true).value

/-- A successful modular reconstruction records only the modular method. -/
theorem detWith_modular {A : Matrix Int n n} {fuel : Nat} {d : Int}
    (h : A.detModular? fuel = some d) : detWith A fuel = ⟨d, .modular, []⟩ := by
  simp [detWith, ordinaryWith, h]

/-- Exhaustion records the Bareiss fallback after the modular attempt. -/
theorem detWith_bareiss {A : Matrix Int n n} {fuel : Nat}
    (h : A.detModular? fuel = none) :
    detWith A fuel = ⟨A.bareiss, .modular, [.bareiss]⟩ := by
  simp [detWith, ordinaryWith, h]

theorem detWith_divisor {A : Matrix Int n n} {fuel seed : Nat} {d : Int}
    (h : (A.detViaDivisorWith (Rand.ofSeed seed) fuel).1 = some d) :
    detWith A fuel seed true = ⟨d, .divisor, []⟩ := by simp [detWith, h]

theorem detWith_divisor_modular {A : Matrix Int n n} {fuel seed : Nat} {d : Int}
    (h : (A.detViaDivisorWith (Rand.ofSeed seed) fuel).1 = none)
    (hm : A.detModular? fuel = some d) :
    detWith A fuel seed true = ⟨d, .divisor, [.modular]⟩ := by
  simp [detWith, ordinaryWith, h, hm]

theorem detWith_divisor_bareiss {A : Matrix Int n n} {fuel seed : Nat}
    (h : (A.detViaDivisorWith (Rand.ofSeed seed) fuel).1 = none)
    (hm : A.detModular? fuel = none) :
    detWith A fuel seed true = ⟨A.bareiss, .divisor, [.modular, .bareiss]⟩ := by
  simp [detWith, ordinaryWith, h, hm]

theorem detWith_divisor_eq [Matrix.LawfulDetBound] {A : Matrix Int n n}
    {fuel seed : Nat} {d : Int}
    (h : (A.detViaDivisorWith (Rand.ofSeed seed) fuel).1 = some d) :
    (detWith A fuel seed true).value = A.det := by
  rw [detWith_divisor h]
  exact Matrix.detViaDivisorWith_eq h

/-- Correctness of the successful modular route in the Mathlib-free layer. -/
theorem detWith_modular_eq [Matrix.LawfulDetBound] {A : Matrix Int n n}
    {fuel : Nat} {d : Int} (h : A.detModular? fuel = some d) :
    (detWith A fuel).value = A.det := by
  rw [detWith_modular h]
  exact Matrix.detModular?_eq h

end Hex.ModularMatrix
