/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Lift
public import HexModularMatrix.Normalise
public import HexModularMatrix.Numerator
public import HexModularMatrix.Algebra
public import HexModular.Recon

public section

namespace Hex.Matrix
namespace Dixon

/-- Count multiplications until the modulus strictly exceeds the bound. -/
def digitsFrom (p : Nat) (hp : 1 < p) (bound power : Nat) (hpower : 0 < power) : Nat :=
  if bound < power then 0
  else 1 + digitsFrom p hp bound (power * p) (Nat.mul_pos hpower (by omega))
termination_by bound + 1 - power
decreasing_by
  have h : power < power * p := by
    calc power = power * 1 := by omega
         _ < power * p := Nat.mul_lt_mul_of_pos_left hp hpower
  omega

theorem digitsFrom_spec (p : Nat) (hp : 1 < p) (bound power : Nat) (hpower : 0 < power) :
    bound < power * p ^ digitsFrom p hp bound power hpower := by
  fun_induction digitsFrom p hp bound power hpower with
  | case1 power hpower h => simpa using h
  | case2 power hpower h ih =>
    simpa only [Nat.pow_add, Nat.pow_one, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using ih

/-- The digit count is determined by the numerator and denominator bounds. -/
def digits (D : Decomp n) (P Q : Nat) : Nat :=
  digitsFrom D.p D.one_lt (2 * P * Q) 1 (by decide)

theorem digits_spec (D : Decomp n) (P Q : Nat) :
    2 * P * Q < D.p ^ digits D P Q := by
  simpa only [digits, Nat.one_mul] using digitsFrom_spec D.p D.one_lt (2 * P * Q) 1 (by decide)

/-- Normalise a candidate and check its integer equation. Shared by the solve
and determinant-divisor route so reduction is tested independently of reconstruction. -/
def check (A : Matrix Int n n) (b y : Vector Int n) (d : Int) :
    Option (Vector Int n × Int) :=
  if 0 < d then
    let (y, d) := normalise y d
    if A * y = d • b then some (y, d) else none
  else none

theorem check_spec {A : Matrix Int n n} {b y z : Vector Int n} {d e : Int}
    (h : check A b y d = some (z, e)) : A * z = e • b ∧ 0 < e := by
  unfold check at h
  split at h <;> try contradiction
  rename_i hd
  dsimp only at h
  split at h <;> try contradiction
  rename_i heq
  cases h
  exact ⟨heq, normalise_pos y d hd⟩

theorem check_reduced {A : Matrix Int n n} {b y z : Vector Int n} {d e : Int}
    (h : check A b y d = some (z, e)) :
    ∀ g : Int, (∀ i : Fin n, g ∣ z[i]) → g ∣ e → g ∣ 1 := by
  unfold check at h
  split at h <;> try contradiction
  rename_i hd
  dsimp only at h
  split at h <;> try contradiction
  cases h
  exact normalise_reduced y d hd

end Dixon

/-- Lift and reconstruct a candidate; consumers must normalise and check it. -/
def Dixon.reconstruct (D : Decomp n) (b : Vector Int n) : Option (Vector Int n × Int) :=
  let P := numeratorBound D.A b
  let Q := hadamardBound D.A
  let k := Dixon.digits D P Q
  Modular.ratReconVec? (D.lift b k) (D.p ^ k) P Q

/-- Lift through a reusable decomposition, reconstruct, normalise and check. -/
def solveWith (D : Decomp n) (b : Vector Int n) : Option (Vector Int n × Int) := do
  let (y, d) ← Dixon.reconstruct D b
  Dixon.check D.A b y d

/-- Solve an integer system over the rationals within a prime-search budget. -/
def solve? (A : Matrix Int n n) (b : Vector Int n) (fuel : Nat) :
    Option (Vector Int n × Int) := (decomp? A fuel).bind (solveWith · b)

theorem solveWith_spec {D : Decomp n} {b y : Vector Int n} {d : Int}
    (h : solveWith D b = some (y, d)) : D.A.mulVec y = d • b ∧ 0 < d := by
  obtain ⟨⟨z, e⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact Dixon.check_spec h

theorem solveWith_reduced {D : Decomp n} {b y : Vector Int n} {d : Int}
    (h : solveWith D b = some (y, d)) :
    ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1 := by
  obtain ⟨⟨z, e⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact Dixon.check_reduced h

theorem solve?_spec {A : Matrix Int n n} {b y : Vector Int n} {fuel : Nat} {d : Int}
    (h : solve? A b fuel = some (y, d)) : A.mulVec y = d • b ∧ 0 < d := by
  obtain ⟨D, hD, hs⟩ := Option.bind_eq_some_iff.mp h
  have h := solveWith_spec hs
  rwa [decomp?_A hD] at h

theorem solve?_reduced {A : Matrix Int n n} {b y : Vector Int n} {fuel : Nat} {d : Int}
    (h : solve? A b fuel = some (y, d)) :
    ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1 := by
  obtain ⟨D, _, hs⟩ := Option.bind_eq_some_iff.mp h
  exact solveWith_reduced hs

theorem solve?_unique {A : Matrix Int n n} {b y z : Vector Int n}
    {fuel : Nat} {d e : Int} (h : solve? A b fuel = some (y, d))
    (hA : det A ≠ 0) (hz : A.mulVec z = e • b) (_he : 0 < e) :
    e • y = d • z := Dixon.solution_unique hA (solve?_spec h).1 hz

/-- A rational solution and a nonzero modular determinant witness. -/
structure SolveWitness (n : Nat) where
  num : Vector Int n
  den : Int
  modulus : Nat
  detImage : Int
  nonzero : detImage ≠ 0

def solveWitness? (A : Matrix Int n n) (b : Vector Int n) (fuel : Nat) :
    Option (SolveWitness n) := do
  let D ← decomp? A fuel
  let (y, d) ← solveWith D b
  return ⟨y, d, D.p, D.detImage, D.detImage_ne_zero⟩

theorem solveWitness?_det_ne_zero {A : Matrix Int n n} {b : Vector Int n}
    {fuel : Nat} {w : SolveWitness n} (h : solveWitness? A b fuel = some w) :
    det A ≠ 0 := by
  obtain ⟨D, hD, _⟩ := Option.bind_eq_some_iff.mp h
  have h := D.det_ne_zero
  rwa [decomp?_A hD] at h

/-- A returned witness contains exactly a checked, reduced solution. -/
theorem solveWitness?_solve {A : Matrix Int n n} {b : Vector Int n}
    {fuel : Nat} {w : SolveWitness n} (h : solveWitness? A b fuel = some w) :
    solve? A b fuel = some (w.num, w.den) := by
  obtain ⟨D, hD, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, d⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  unfold solve?
  simp only [hD, Option.bind_some, hs]

/-- Every successful vector solve also certifies nonsingularity. -/
theorem solve?_det_ne_zero {A : Matrix Int n n} {b y : Vector Int n}
    {fuel : Nat} {d : Int} (h : solve? A b fuel = some (y, d)) : det A ≠ 0 := by
  obtain ⟨D, hD, _⟩ := Option.bind_eq_some_iff.mp h
  have hd := D.det_ne_zero
  rwa [decomp?_A hD] at hd

end Hex.Matrix
