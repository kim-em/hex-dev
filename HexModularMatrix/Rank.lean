/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexModularMatrix.Det
import all HexModularMatrix.Reconstruction

public import HexRank.Int
public import HexModArith.Field
public import HexModularMatrix.Det
public import HexModularMatrix.SolveMat

public section

/-! Integer rank certificates found modulo primes and completed by Dixon solves. -/

namespace Hex.Matrix

variable {n m p : Nat}

/-- Rank over a prime field, using the same profile pass as the certificate search. -/
def rankModP [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (A : Matrix (ZMod64 p) n m) : Nat :=
  (rankProfileWith Hex.exactDiv A).rank

namespace ModularRank

/-- The ordinary determinant route with a shared modulus supply. The budget
and Bareiss fallback are the same as `ordinaryWith`. -/
def determinant (B : Matrix Int r r) (fuel : Nat) (qs : Array ZMod64.Prime) :
    Hex.ModularMatrix.DetData :=
  match B.detCrtWith? B.hadamardBound fuel (qs.map (·.m)) with
  | some state => ⟨state.value[0], .modular, []⟩
  | none => ⟨B.bareiss, .modular, [.bareiss]⟩

/-- Sharing the generated supply preserves the ordinary determinant route. -/
theorem determinant_eq (B : Matrix Int r r) (fuel : Nat) :
    determinant B fuel (ZMod64.primesBelow (2 ^ 31 - 1) fuel) =
      Hex.ModularMatrix.ordinaryWith B fuel := by
  unfold determinant Hex.ModularMatrix.ordinaryWith detModular? detBounded? detCrt?
  cases B.detCrtWith? B.hadamardBound fuel
    ((ZMod64.primesBelow (2 ^ 31 - 1) fuel).map (·.m)) <;> rfl

/-- Complete a modular profile using one decomposition of its square block.
The determinant fixes the normalization; the matrix solve shares its inverse
across all right-hand sides. Every division is checked before using exactDiv. -/
def candidate (A : Matrix Int n m) (fuel : Nat) (qs : Array ZMod64.Prime) (q : ZMod64.Prime) :
    Option (RankCert Int n m) := do
  let _ : ZMod64.Bounds q.m := q.bounds
  let profile := rankProfileWith Hex.exactDiv (A.mapEntries (ZMod64.intCast q.m))
  let B := selectedSubmatrix A profile.rows profile.cols
  let d := (determinant B fuel qs).value
  let D ← decompAt? B q.m q.prime.one_lt
  let (Y, e) ← solveMatWith D (scale d (Matrix.identity profile.rank))
  if e ≠ 0 ∧ ∀ (i j : Fin profile.rank), Y[(i, j)] % e = 0 then
    let X := Y.mapEntries (fun x => HexArith.Int.exactDiv x e)
    return ⟨profile.rank, profile.rows, profile.cols, d, X⟩
  else none

/-- Search a finite prime list, retaining only certificates accepted by hex-rank. -/
def search (A : Matrix Int n m) (fuel : Nat) (supply : Array ZMod64.Prime) : List ZMod64.Prime →
    Option (RankCert Int n m)
  | [] => none
  | q :: qs =>
    match candidate A fuel supply q with
    | some c => if checkRank A c then some c else search A fuel supply qs
    | none => search A fuel supply qs

theorem search_check {A : Matrix Int n m} {fuel : Nat} {supply : Array ZMod64.Prime} {qs : List ZMod64.Prime}
    {c : RankCert Int n m} (h : search A fuel supply qs = some c) : checkRank A c = true := by
  induction qs with
  | nil => simp [search] at h
  | cons q qs ih =>
    simp only [search] at h
    split at h
    · split at h
      · cases h
        assumption
      · exact ih h
    · exact ih h

end ModularRank

/-- Try at most `fuel` descending word primes, also allowing `fuel` determinant
images per attempt. Dixon lifting uses its bound-derived digit count. Exhaustion
or rejected attempts return `none`, asserting no rank or singularity fact. -/
def rankCert? (A : Matrix Int n m) (fuel : Nat) : Option (RankCert Int n m) :=
  if fuel = 0 then none
  else
    let qs := ZMod64.primesBelow (2 ^ 31 - 1) fuel
    ModularRank.search A fuel qs qs.toList

theorem rankCert?_check {A : Matrix Int n m} {fuel : Nat} {c : RankCert Int n m}
    (h : rankCert? A fuel = some c) : checkRank A c = true := by
  unfold rankCert? at h
  split at h
  · contradiction
  · exact ModularRank.search_check h

@[simp] theorem rankCert?_zero (A : Matrix Int n m) : rankCert? A 0 = none := by
  simp [rankCert?]

/-- A fixed prime-search budget; exhaustion uses the total integer rank algorithm. -/
def rankFuel : Nat := 8

/-- Exact integer rank, with only the natural number exposed. On modular-search
failure this computes hex-rank's total fraction-free integer rank. -/
def rankModular (A : Matrix Int n m) : Nat :=
  match rankCert? A rankFuel with
  | some c => c.rank
  | none => rank A

end Hex.Matrix
