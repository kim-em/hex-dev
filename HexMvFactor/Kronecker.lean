/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvFactor.IrredData
public import HexBerlekampZassenhaus.FactorProduct
public import HexPolyZ.ExactDivision
public import Batteries.Data.Vector.Basic

@[expose] public section
set_option backward.proofsInPublic true

/-!
Mixed-radix Kronecker substitution and the unconditional divisor sweep.

This is variable packing, not the coefficient-packing multiplication in
`HexPolyZ.Kronecker`.  Every inverse result is checked by applying `kron`
again, and every reducible verdict retains a split accepted by the cheap split
checker core.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp]

/-- Coordinate degrees tabulated once from the sparse representation. -/
def kronDegrees (p : MvPoly n Int cmp) : Vector Nat n :=
  Hex.Vector.ofFn' fun i => MvPoly.degreeOf i p

/-- All mixed-radix weights, computed in one left-to-right pass. -/
def radixWeights (degrees : Fin n → Nat) : Vector Nat n :=
  let bases := Hex.Vector.ofFn' fun i => degrees i + 1
  (bases.scanl (fun weight base => weight * base) 1).pop.cast (by omega)

/-- Product of the earlier mixed-radix bases. -/
def radixWeight (degrees : Fin n → Nat) (j : Fin n) : Nat :=
  (radixWeights degrees)[j]

/-- Number of exponent vectors in the degree box. -/
def radixSize (degrees : Fin n → Nat) : Nat :=
  (List.finRange n).foldl (fun size i => size * (degrees i + 1)) 1

/-- Mixed-radix encoding using already tabulated weights. -/
def kronExponentWith (weights : Vector Nat n) (m : Mono n) : Nat :=
  (List.finRange n).foldl
    (fun exponent i => exponent + Mono.degreeOf i m * weights[i]) 0

/-- Mixed-radix encoding of one exponent vector. -/
def kronExponent (degrees : Fin n → Nat) (m : Mono n) : Nat :=
  kronExponentWith (radixWeights degrees) m

/-- Substitute with already tabulated mixed-radix weights. -/
def kronWith (weights : Vector Nat n) (p : MvPoly n Int cmp) : ZPoly :=
  p.foldTerms
    (fun image monomial coefficient =>
      image + DensePoly.monomial (kronExponentWith weights monomial) coefficient)
    0

/-- Substitute `x_j = z^(radixWeight degrees j)`. -/
def kron (degrees : Fin n → Nat) (p : MvPoly n Int cmp) : ZPoly :=
  kronWith (radixWeights degrees) p

/-- Maximum encoded exponent, read directly from the sparse support without
constructing a dense univariate image. -/
def kronDegreeWith (weights : Vector Nat n)
    (p : MvPoly n Int cmp) : Option Nat :=
  p.foldTerms
    (fun degree monomial _ =>
      let encoded := kronExponentWith weights monomial
      some <| match degree with
        | none => encoded
        | some current => max current encoded)
    none

/-- Sparse encoded degree with weights prepared from the degree box. -/
def kronDegree? (degrees : Fin n → Nat)
    (p : MvPoly n Int cmp) : Option Nat :=
  kronDegreeWith (radixWeights degrees) p

/-! # Budget-saturated sparse degree -/

/-- Add natural numbers, returning `cap + 1` as soon as the result exceeds
the producer cap. -/
def kronCapAdd (cap a b : Nat) : Nat :=
  if cap < a || cap - a < b then cap + 1 else a + b

/-- Multiply natural numbers, returning `cap + 1` as soon as the result
exceeds the producer cap.  The comparison happens before multiplication. -/
def kronCapMul (cap a b : Nat) : Nat :=
  if a = 0 || b = 0 then 0
  else if cap / a < b then cap + 1 else a * b

/-- Encoded exponent saturated at `cap + 1`.  The current weight is carried
through one fold, so rejection neither recomputes nor stores exact powers. -/
def kronExponentUpTo (cap : Nat) (degrees : Fin n → Nat)
    (monomial : Mono n) : Nat :=
  ((List.finRange n).foldl
    (fun state i =>
      (kronCapAdd cap state.1
          (kronCapMul cap (Mono.degreeOf i monomial) state.2),
        kronCapMul cap state.2 (degrees i + 1)))
    (0, 1)).1

/-- Sparse encoded degree saturated at `cap + 1`.  In particular, a tiny
budget never constructs the exact exponentially growing weight table. -/
def kronDegreeUpTo? (cap : Nat) (degrees : Fin n → Nat)
    (p : MvPoly n Int cmp) : Option Nat :=
  p.foldTerms
    (fun degree monomial _ =>
      let encoded := kronExponentUpTo cap degrees monomial
      some <| match degree with
        | none => encoded
        | some current => max current encoded)
    none

/-- Decode an exponent using already tabulated weights and box size. -/
def decodeExponentWith? (degrees : Fin n → Nat) (weights : Vector Nat n)
    (size exponent : Nat) : Option (Mono n) :=
  if exponent < size then
    some <| Hex.Vector.ofFn' fun i =>
      exponent / weights[i] % (degrees i + 1)
  else
    none

/-- Decode an exponent inside the mixed-radix box. -/
def decodeExponent? (degrees : Fin n → Nat) (exponent : Nat) : Option (Mono n) :=
  decodeExponentWith? degrees (radixWeights degrees) (radixSize degrees) exponent

/-- Decode the dense coefficients, rejecting any supported exponent outside
the mixed-radix box. -/
def unKronAux (degrees : Fin n → Nat) (weights : Vector Nat n) (size : Nat) :
    Nat → List Int → List (Mono n × Int) → Option (MvPoly n Int cmp)
  | _, [], terms => some (MvPoly.ofTerms terms.reverse)
  | exponent, coefficient :: coefficients, terms =>
      if coefficient = 0 then
        unKronAux degrees weights size (exponent + 1) coefficients terms
      else
        match decodeExponentWith? degrees weights size exponent with
        | none => none
        | some monomial =>
            unKronAux degrees weights size (exponent + 1) coefficients
              ((monomial, coefficient) :: terms)

/-- Partial inverse with mixed-radix prework supplied by the caller. -/
def unKronWith? (degrees : Fin n → Nat) (weights : Vector Nat n)
    (size : Nat) (P : ZPoly) : Option (MvPoly n Int cmp) :=
  match unKronAux (cmp := cmp) degrees weights size 0 P.toArray.toList [] with
  | none => none
  | some p => if kronWith weights p == P then some p else none

/-- Partial inverse to `kron`, with an exact re-encoding check before any
decoded polynomial is exposed. -/
def unKron? (degrees : Fin n → Nat) (P : ZPoly) : Option (MvPoly n Int cmp) :=
  let weights := radixWeights degrees
  unKronWith? degrees weights (radixSize degrees) P

/-- Structural polynomial power used by certificate replay. -/
def zPow (P : ZPoly) : Nat → ZPoly
  | 0 => 1
  | exponent + 1 => zPow P exponent * P

private theorem zPow_factorPower (P : ZPoly) : ∀ exponent,
    zPow P exponent = Factorization.factorPower P exponent
  | 0 => rfl
  | exponent + 1 => by
      rw [zPow, Factorization.factorPower_succ,
        zPow_factorPower P exponent]

/-- Product represented by the univariate part of a Kronecker certificate. -/
def uniProduct (scalar : Int) (uni : List (ZPoly × Nat)) : ZPoly :=
  uni.foldl (fun product entry => product * zPow entry.1 entry.2)
    (DensePoly.C scalar)

private theorem uniProduct_factorization (factorization : Factorization) :
    uniProduct factorization.scalar factorization.factors.toList =
      factorization.product := by
  unfold uniProduct Factorization.product
  rw [← Array.foldl_toList]
  apply List.foldl_congr
  intro acc entry _
  rw [zPow_factorPower]
  rfl

/-- Product selected by one exponent vector.  Length mismatch is rejected. -/
def candidateProduct? : List (ZPoly × Nat) → List Nat → Option ZPoly
  | [], [] => some 1
  | entry :: entries, exponent :: exponents =>
      (candidateProduct? entries exponents).map fun product =>
        zPow entry.1 exponent * product
  | _, _ => none

/-- All exponent vectors bounded componentwise by the stored multiplicities. -/
def exponentVectors : List (ZPoly × Nat) → List (List Nat)
  | [] => [[]]
  | entry :: entries =>
      (List.range (entry.2 + 1)).flatMap fun exponent =>
        (exponentVectors entries).map fun exponents => exponent :: exponents

/-- Remove the two exponent vectors representing the trivial unit and whole
products. -/
def properExponentVectors (uni : List (ZPoly × Nat)) : List (List Nat) :=
  let full := uni.map Prod.snd
  (exponentVectors uni).filter fun exponents =>
    decide (exponents ≠ List.replicate uni.length 0) && decide (exponents ≠ full)

/-- Positive multiplicity and primitive positive degree for one stored
univariate factor. -/
def checkUniFactor (entry : ZPoly × Nat) : Bool :=
  decide (0 < entry.2) &&
    decide (ZPoly.content entry.1 = 1) &&
    match entry.1.degree? with
    | none => false
    | some degree => decide (0 < degree)

/-- Pairwise exact distinctness of the stored univariate factors. -/
def distinctUni : List (ZPoly × Nat) → Bool
  | [] => true
  | entry :: entries =>
      entries.all (fun other => decide (entry.1 ≠ other.1)) && distinctUni entries

/-- Pairwise-distinct factor keys pass the structural replay. -/
private theorem distinctUni_of_pairwise : ∀ {uni : List (ZPoly × Nat)},
    uni.Pairwise (fun a b => a.1 ≠ b.1) → distinctUni uni = true
  | [], _ => rfl
  | _ :: _, .cons head tail => by
      simp only [distinctUni, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq]
      exact ⟨head, distinctUni_of_pairwise tail⟩

/-- Cheap replay core shared by `checkSplit` and the producer. -/
def checkSplitCore (g : MvPoly n Int cmp) (split : Split n cmp) : Bool :=
  (split.left * split.right == g) &&
    !polyIsUnit split.left && !polyIsUnit split.right

/-- One candidate is refuted when it does not decode, decodes to a constant,
or fails to give a checked nontrivial split. Mixed-radix prework is shared by
the whole candidate sweep. -/
def candidateRejected (degrees : Fin n → Nat) (weights : Vector Nat n)
    (size : Nat) (g : MvPoly n Int cmp) (uni : List (ZPoly × Nat))
    (exponents : List Nat) : Bool :=
  match candidateProduct? uni exponents with
  | none => true
  | some candidate =>
      match unKronWith? (cmp := cmp) degrees weights size candidate with
      | none => true
      | some divisor =>
          if divisor.vars.isEmpty then true
          else
            match MvPoly.divExact? g divisor with
            | none => true
            | some quotient => !checkSplitCore g ⟨divisor, quotient⟩

/-- Replay against a prepared degree box and its exact Kronecker image. -/
def checkKroneckerWith (degrees : Fin n → Nat) (weights : Vector Nat n)
    (size : Nat) (g : MvPoly n Int cmp) (image : ZPoly) (scalar : Int)
    (uni : List (ZPoly × Nat)) : Bool :=
  decide (MvPoly.content g = 1) &&
    decide (g.vars ≠ []) &&
    (uniProduct scalar uni == image) &&
    uni.all checkUniFactor &&
    distinctUni uni &&
    (properExponentVectors uni).all
      (candidateRejected degrees weights size g uni)

/-- Replay the complete Kronecker certificate without refactoring its
univariate image. -/
def checkKronecker (g : MvPoly n Int cmp) (scalar : Int)
    (uni : List (ZPoly × Nat)) : Bool :=
  let degreeData := kronDegrees g
  let degrees : Fin n → Nat := fun i => degreeData[i]
  let weights := radixWeights degrees
  checkKroneckerWith degrees weights (radixSize degrees) g
    (kronWith weights g) scalar uni

/-- Inspect candidates in order and retain the first accepted nontrivial
divisor and its exact quotient. -/
def findSplitAux (degrees : Fin n → Nat) (weights : Vector Nat n)
    (size : Nat) (g : MvPoly n Int cmp) (uni : List (ZPoly × Nat)) :
    List (List Nat) → Option (Split n cmp)
  | [] => none
  | exponents :: rest =>
      match candidateProduct? uni exponents with
      | none => findSplitAux degrees weights size g uni rest
      | some candidate =>
          match unKronWith? (cmp := cmp) degrees weights size candidate with
          | none => findSplitAux degrees weights size g uni rest
          | some divisor =>
              if divisor.vars.isEmpty then
                findSplitAux degrees weights size g uni rest
              else
                match MvPoly.divExact? g divisor with
                | none => findSplitAux degrees weights size g uni rest
                | some quotient =>
                    let split : Split n cmp := ⟨divisor, quotient⟩
                    if checkSplitCore g split then some split
                    else findSplitAux degrees weights size g uni rest

/-- Every split returned by the candidate sweep has passed cheap replay. -/
private theorem findSplitAux_checks (degrees : Fin n → Nat)
    (weights : Vector Nat n) (size : Nat) (g : MvPoly n Int cmp)
    (uni : List (ZPoly × Nat)) : ∀ {candidates split},
      findSplitAux degrees weights size g uni candidates = some split →
        checkSplitCore g split = true
  | [], _, h => by contradiction
  | _ :: rest, _, h => by
      unfold findSplitAux at h
      split at h
      · exact findSplitAux_checks degrees weights size g uni h
      · split at h
        · exact findSplitAux_checks degrees weights size g uni h
        · split at h
          · exact findSplitAux_checks degrees weights size g uni h
          · split at h
            · exact findSplitAux_checks degrees weights size g uni h
            · dsimp only at h
              split at h
              · cases h
                assumption
              · exact findSplitAux_checks degrees weights size g uni h

/-- Exhausting the split search refutes every candidate by the replay
predicate used in a Kronecker certificate. -/
private theorem findSplitAux_none (degrees : Fin n → Nat)
    (weights : Vector Nat n) (size : Nat) (g : MvPoly n Int cmp)
    (uni : List (ZPoly × Nat)) : ∀ {candidates},
      findSplitAux degrees weights size g uni candidates = none →
        candidates.all
          (candidateRejected degrees weights size g uni) = true
  | [], _ => rfl
  | _ :: rest, h => by
      unfold findSplitAux at h
      simp only [List.all_cons, Bool.and_eq_true]
      unfold candidateRejected
      split at *
      · exact ⟨by simp_all, findSplitAux_none degrees weights size g uni h⟩
      · split at *
        · exact ⟨by simp_all, findSplitAux_none degrees weights size g uni h⟩
        · split at *
          · exact ⟨by simp_all, findSplitAux_none degrees weights size g uni h⟩
          · split at *
            · exact ⟨by simp_all, findSplitAux_none degrees weights size g uni h⟩
            · dsimp only at h ⊢
              split at *
              · contradiction
              · exact ⟨by simp_all,
                  findSplitAux_none degrees weights size g uni h⟩

/-- Search with mixed-radix prework supplied by the caller. -/
def findSplitWith (degrees : Fin n → Nat) (weights : Vector Nat n)
    (size : Nat) (g : MvPoly n Int cmp)
    (uni : List (ZPoly × Nat)) : Option (Split n cmp) :=
  findSplitAux degrees weights size g uni (properExponentVectors uni)

/-- Search all proper exponent vectors for a genuine multivariate divisor. -/
def findSplit (degrees : Fin n → Nat) (g : MvPoly n Int cmp)
    (uni : List (ZPoly × Nat)) : Option (Split n cmp) :=
  let weights := radixWeights degrees
  findSplitWith degrees weights (radixSize degrees) g uni

/-- Kronecker decision with a prepared degree box and its exact image. -/
def kronDecideWith (degrees : Fin n → Nat) (weights : Vector Nat n)
    (size : Nat) (g : MvPoly n Int cmp) (image : ZPoly) : Verdict n cmp :=
  let factorization := ZPoly.factorize image
  let uni := factorization.factors.toList
  match findSplitWith degrees weights size g uni with
  | some split => .reducible split
  | none => .irreducible (.kronecker factorization.scalar uni)

/-- Produce a Kronecker certificate only when the sparse encoded degree fits
`maxDegree`.  Rejection uses saturated arithmetic; acceptance constructs the
dense image once and shares it between factorization and producer replay. -/
def kronProduce? (maxDegree : Nat) (g : MvPoly n Int cmp) :
    Option (IrredCert n cmp) :=
  let degreeData := kronDegrees g
  let degrees : Fin n → Nat := fun i => degreeData[i]
  match kronDegreeUpTo? maxDegree degrees g with
  | none => none
  | some degree =>
      if maxDegree < degree then none
      else
        let weights := radixWeights degrees
        let size := radixSize degrees
        let image := kronWith weights g
        match kronDecideWith degrees weights size g image with
        | .reducible _ => none
        | .irreducible cert@(.kronecker scalar uni) =>
            if checkKroneckerWith degrees weights size g image scalar uni then
              some cert
            else none
        | .irreducible _ => none

/-- Total Kronecker decision procedure on the intended primitive,
nonconstant domain.  Outside that domain it still terminates, while the
soundness theorem below deliberately requires the missing hypotheses. -/
def kronDecide (g : MvPoly n Int cmp) : Verdict n cmp :=
  let degreeData := kronDegrees g
  let degrees : Fin n → Nat := fun i => degreeData[i]
  let weights := radixWeights degrees
  kronDecideWith degrees weights (radixSize degrees) g (kronWith weights g)

set_option maxHeartbeats 800000

/-- The producer's irreducible branch replays on its intended domain. -/
theorem kronDecide_checks {g : MvPoly n Int cmp} {cert : IrredCert n cmp}
    (hprim : MvPoly.content g = 1) (hnonconst : ¬ MvPoly.IsConst g)
    (h : kronDecide g = .irreducible cert) :
    ∃ scalar uni,
      cert = .kronecker scalar uni ∧ checkKronecker g scalar uni = true := by
  simp only [kronDecide, kronDecideWith] at h
  split at h
  next => contradiction
  next hfind =>
    cases h
    let degrees : Fin n → Nat := fun i => (kronDegrees g)[i]
    let weights := radixWeights degrees
    let size := radixSize degrees
    let image := kronWith weights g
    let factorization := ZPoly.factorize image
    change findSplitWith degrees weights size g
      factorization.factors.toList = none at hfind
    refine ⟨factorization.scalar, factorization.factors.toList, rfl, ?_⟩
    change checkKroneckerWith degrees weights size g image
      factorization.scalar factorization.factors.toList = true
    unfold checkKroneckerWith
    have hvars : g.vars ≠ [] := hnonconst
    have hprimB : decide (MvPoly.content g = 1) = true := by
      simp [hprim]
    have hvarsB : decide (g.vars ≠ []) = true := by
      simp [hvars]
    rw [hprimB, hvarsB]
    simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq]
    constructor
    · constructor
      · constructor
        · exact (uniProduct_factorization factorization).trans
            (factorize_product image)
        · rw [List.all_eq_true]
          intro entry hentry
          have harray : entry ∈ factorization.factors :=
            Array.mem_toList_iff.mp hentry
          by_cases himage : image = 0
          · change entry ∈ (ZPoly.factorize image).factors at harray
            rw [himage, factorize_zero_factors] at harray
            simp at harray
          · have hmult := factorize_entry_multiplicity_pos image entry hentry
            have hprimEntry := factorize_entries_primitive_of_ne_zero
              image himage entry harray
            change ZPoly.content entry.1 = 1 at hprimEntry
            have hdegree := factorize_entries_degree_pos
              image himage entry harray
            unfold checkUniFactor
            simp only [hmult, decide_true, hprimEntry, Bool.true_and]
            cases hdegreeOpt : entry.1.degree? with
            | none => simp [hdegreeOpt] at hdegree
            | some degree => simpa [hdegreeOpt] using hdegree
      · exact distinctUni_of_pairwise (factorize_pairwise_first image)
    · unfold findSplitWith at hfind
      exact findSplitAux_none _ _ _ _ _ hfind

set_option maxHeartbeats 200000

/-- Every reducible outcome has already passed cheap split replay. -/
theorem kronDecide_split {g : MvPoly n Int cmp} {split : Split n cmp}
    (h : kronDecide g = .reducible split) : checkSplitCore g split = true := by
  simp only [kronDecide, kronDecideWith] at h
  split at h
  next found hfind =>
    cases h
    unfold findSplitWith at hfind
    exact findSplitAux_checks _ _ _ _ _ hfind
  next hfind => contradiction

end Hex.MvFactor
