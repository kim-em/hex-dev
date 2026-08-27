/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Ntt.Catalogue

public section

/-!
# Auxiliary-prime NTT residue batches

This module selects enough fixed catalogue primes for a strict symmetric CRT
bound and runs the same integer convolution at each selected modulus.  It does
not depend on the CRT implementation: coefficient-owner libraries pass the
resulting moduli and residue vectors to `Hex.Modular.CrtPlan`.
-/

namespace Hex

namespace ZMod64

namespace Ntt

/-- Take supported catalogue primes through the first prefix whose product
exceeds `target`.  The public checked wrapper below validates exhaustion. -/
private def takeUntil (target product : Nat) : List NttPrime → List NttPrime
  | [] => []
  | prime :: primes =>
      prime ::
        if target < product * prime.modulus then []
        else takeUntil target (product * prime.modulus) primes

/-- Candidate catalogue prefix for a transform length and coefficient bound. -/
private def choose (n bound : Nat) : List NttPrime :=
  takeUntil (2 * bound) 1
    (nttPrimes.filter fun prime => decide (n ≤ prime.maxLength))

/-- A checked catalogue selection with enough pairwise-coprime modulus product
for strict symmetric reconstruction. -/
structure CrtSelection (n bound : Nat) where
  /-- Selected catalogue entries, in catalogue order. -/
  primes : List NttPrime
  /-- At least one transform is run, including at bound zero. -/
  hasPrime : primes ≠ []
  /-- Every selected prime supports the requested transform length. -/
  fits : ∀ prime ∈ primes, n ≤ prime.maxLength
  /-- The selected product is strictly larger than twice the supplied bound. -/
  enough : 2 * bound < (primes.map NttPrime.modulus).prod

namespace CrtSelection

/-- Select and validate a sufficient supported catalogue prefix. -/
def build? (n bound : Nat) : Option (CrtSelection n bound) :=
  let primes := choose n bound
  if hnonempty : primes ≠ [] then
    if hsupported : ∀ prime ∈ primes, n ≤ prime.maxLength then
      if henough : 2 * bound < (primes.map NttPrime.modulus).prod then
        some (CrtSelection.mk primes hnonempty hsupported henough)
      else
        none
    else
      none
  else
    none

/-- Selected moduli in the same order expected by batch CRT. -/
def moduli (selection : CrtSelection n bound) : Array Nat :=
  (selection.primes.map NttPrime.modulus).toArray

@[simp] theorem moduli_toList (selection : CrtSelection n bound) :
    selection.moduli.toList = selection.primes.map NttPrime.modulus := by
  simp [moduli]

@[simp] theorem moduli_size (selection : CrtSelection n bound) :
    selection.moduli.size = selection.primes.length := by
  simp [moduli]

theorem enough_moduli (selection : CrtSelection n bound) :
    2 * bound < selection.moduli.toList.prod := by
  simpa using selection.enough

end CrtSelection

/-- Coefficientwise congruence between a prime list and its erased residue
vectors. -/
inductive CrtMatches (reference : List Int) :
    List NttPrime → List (Vector Int n) → Prop where
  | nil : CrtMatches reference [] []
  | cons {prime : NttPrime} {primes : List NttPrime}
      {residue : Vector Int n} {residues : List (Vector Int n)} :
      (∀ j : Fin n,
        reference.getD j.val 0 % (prime.modulus : Int) =
          residue[j] % (prime.modulus : Int)) →
      CrtMatches reference primes residues →
      CrtMatches reference (prime :: primes) (residue :: residues)

/-- Erased NTT residues paired with their coefficientwise congruence proof. -/
structure CrtImages (selection : CrtSelection n bound)
    (left right : Array Int) where
  residues : List (Vector Int n)
  sound : CrtMatches
    (intPadTo n (intLinearConvolution left.toList right.toList))
    selection.primes residues
  referenceSize :
    (intPadTo n
      (intLinearConvolution left.toList right.toList)).length = n

namespace CrtMatches

theorem length_eq {reference : List Int} {primes : List NttPrime}
    {residues : List (Vector Int n)}
    (h : CrtMatches reference primes residues) :
    residues.length = primes.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem getElem {reference : List Int} {primes : List NttPrime}
    {residues : List (Vector Int n)}
    (h : CrtMatches reference primes residues)
    (i : Nat) (hi : i < primes.length) (j : Fin n) :
    reference.getD j.val 0 % ((primes[i]'hi).modulus : Int) =
      (residues[i]'(by simpa [h.length_eq] using hi))[j] %
        ((primes[i]'hi).modulus : Int) := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons prime primes residue residues hhead htail ih =>
      cases i with
      | zero => simpa using hhead j
      | succ i =>
          have hi' : i < primes.length := by simpa using hi
          simpa using ih i hi'

end CrtMatches

private def runPrimes? (n : Nat) (left right : Array Int) :
    (primes : List NttPrime) →
      Option { residues : List (Vector Int n) //
        CrtMatches (intPadTo n
          (intLinearConvolution left.toList right.toList)) primes residues ∧
        (primes ≠ [] →
          (intPadTo n
            (intLinearConvolution left.toList right.toList)).length = n) }
  | [] => some ⟨[], .nil, by simp⟩
  | prime :: primes =>
      match hcoefficients : prime.convolution? n left right with
      | none => none
      | some coefficients =>
          if hsize : coefficients.size = n then
            match runPrimes? n left right primes with
            | none => none
            | some tail => by
                have hreference := prime.convolution?_eq_of_some n left right
                  coefficients hcoefficients
                let residue : Vector Int n := ⟨coefficients, hsize⟩
                let reference := intPadTo n
                  (intLinearConvolution left.toList right.toList)
                have hreferenceSize : reference.length = n := by
                  have hsizes := congrArg Array.size hreference
                  simpa [reference, hsize] using hsizes.symm
                have hhead : ∀ j : Fin n,
                    reference.getD j.val 0 % (prime.modulus : Int) =
                      residue[j] % (prime.modulus : Int) := by
                  intro j
                  have hjcoeff : j.val < coefficients.size := by
                    simpa [hsize] using j.isLt
                  have hjreference : j.val < reference.length := by
                    rw [hreferenceSize]
                    exact j.isLt
                  rw [show residue[j] = coefficients.getD j.val 0 by
                    simp [residue, Array.getD_eq_getD_getElem?, hjcoeff]]
                  have hcoeff := congrArg
                    (fun values : Array Int => values.getD j.val 0) hreference
                  rw [hcoeff]
                  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map,
                    List.getElem?_toArray]
                  rw [List.getElem?_eq_getElem (by
                    simpa [reference] using hjreference)]
                  simp only [Option.map_some, Option.getD_some]
                  rw [← List.getElem_eq_getD (h := hjreference) 0]
                  simpa [reference] using
                    (prime.residue_emod (reference[j.val]'hjreference)).symm
                exact some ⟨residue :: tail.val,
                  .cons hhead tail.property.1, fun _ => hreferenceSize⟩
          else
            none

/-- Run an integer convolution at every prime in a checked selection. -/
def CrtSelection.images? (selection : CrtSelection n bound)
    (left right : Array Int) : Option (CrtImages selection left right) := do
  let images ← runPrimes? n left right selection.primes
  pure (CrtImages.mk images.val images.property.1
    (images.property.2 selection.hasPrime))

namespace CrtImages

@[simp] theorem residues_length {n bound : Nat}
    {selection : CrtSelection n bound} {left right : Array Int}
    (images : CrtImages selection left right) :
    images.residues.length = selection.primes.length :=
  images.sound.length_eq

/-- Residue vectors in batch-CRT input form. -/
def residueArray {n bound : Nat} {selection : CrtSelection n bound}
    {left right : Array Int} (images : CrtImages selection left right) :
    Array (Vector Int n) :=
  images.residues.toArray

@[simp] theorem residueArray_size {n bound : Nat}
    {selection : CrtSelection n bound} {left right : Array Int}
    (images : CrtImages selection left right) :
    images.residueArray.size = selection.moduli.size := by
  simp [residueArray, images.residues_length]

/-- Each erased residue lane is congruent to the reference integer
convolution at the corresponding selected modulus. -/
theorem congr {n bound : Nat} {selection : CrtSelection n bound}
    {left right : Array Int} (images : CrtImages selection left right)
    (i : Fin selection.moduli.size) (j : Fin n) :
    (intPadTo n
        (intLinearConvolution left.toList right.toList)).getD j.val 0 %
          (selection.moduli[i] : Int) =
      (images.residueArray.getD i.val (Vector.replicate n 0))[j] %
        (selection.moduli[i] : Int) := by
  have hi : i.val < selection.primes.length := by
    simpa using i.isLt
  have hmod : selection.moduli[i] =
      (selection.primes[i.val]'hi).modulus := by
    change (selection.primes.map NttPrime.modulus)[i.val] = _
    rw [List.getElem_map]
  rw [hmod]
  simpa [residueArray, Array.getD, hi] using
    images.sound.getElem i.val hi j

end CrtImages

end Ntt

end ZMod64

end Hex
