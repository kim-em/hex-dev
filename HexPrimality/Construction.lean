/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Search

public section

namespace Hex.Nat

/-- Finite, opt-in certificate construction resources. ECM is disabled on this
Mathlib-free core route (zero curves and no ECM bounds). -/
structure ConstructionBudget where
  maxBits : Nat := 512
  maxDepth : Nat := 32
  factor : FactorSearchBudget := {
    primeBudget := ⟨2, 32768⟩
    primeFuel := 32
    factorFuel := 1024
    smoothBounds := [64, 512, 4096, 32768, 262144, 524288]
    smoothBases := [2, 3] }
  witnessBases : List Nat := [2, 3, 5, 7, 11, 13, 17]
  randomWitnesses : Nat := 32
  maxFactors : Nat := 12
  maxSubsets : Nat := 4096
deriving Repr, DecidableEq

/-- The reproducible construction profile used by `primality?`. -/
def constructionBudget : ConstructionBudget := {}

namespace Construction

private def insert (q e : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(q, e)]
  | (p, k) :: rest =>
      if p = q then (p, k + e) :: rest else (p, k) :: insert q e rest

private def trial (n : Nat) : PartialFactors := Id.run do
  let mut m := n
  let mut factors := []
  for q in primeTable do
    if m % q = 0 then
      let (e, rest) := Internal.trialExtractTrace q m
      factors := (q, e) :: factors
      m := rest
  return ⟨factors, m⟩

private def splitSmooth (allocation : FactorSearchBudget) (n : Nat) (r : Hex.Rand) :
    Option Nat × Nat := Id.run do
  let mut attempts := 0
  for bound in allocation.smoothBounds do
    for base in allocation.smoothBases do
      let result := pMinusOneStage1Counted n base bound r
      attempts := attempts + result.attempts
      if let .factor d := result.result then
        return (some d, attempts)
  return (none, attempts)

private def factorGo (allocation : FactorSearchBudget) :
    Nat → List Nat → List (Nat × Nat) → Nat → Hex.Rand → Nat → FactorSearchResult
  | 0, stack, acc, residual, r, attempts =>
      ⟨⟨acc, stack.foldl (· * ·) residual⟩, r, attempts⟩
  | _ + 1, [], acc, residual, r, attempts => ⟨⟨acc, residual⟩, r, attempts⟩
  | fuel + 1, m :: stack, acc, residual, r, attempts =>
      if m ≤ 1 then factorGo allocation fuel stack acc residual r attempts
      else if isProbablePrime m then
        factorGo allocation fuel stack (insert m 1 acc) residual r attempts
      else
        let (d, work) := splitSmooth allocation m r
        match d with
        | some d => factorGo allocation fuel (d :: m / d :: stack) acc residual r
            (attempts + work)
        | none =>
            match Internal.rhoFactorCountedWith? m r allocation.primeBudget.rhoRestarts
                allocation.primeBudget.rhoSteps with
            | .ok success =>
                factorGo allocation fuel (success.factor :: m / success.factor :: stack)
                  acc residual success.rand (attempts + work + success.attempts)
            | .error f => factorGo allocation fuel stack acc (residual * m) f.rand
                (attempts + work + f.attempts)

/-- Table division followed by the explicitly budgeted smooth/rho worklist.
Every unresolved component is retained in the residual. -/
def factorSearch : FactorSearch := fun allocation n r =>
  if n = 0 then ⟨⟨[], 0⟩, r, 0⟩ else
    let initial := trial n
    factorGo allocation allocation.factorFuel [initial.residual] initial.factors 1 r 0

private def product (n : Nat) (factors : List (Nat × Nat)) : Option Nat := do
  let mut acc := 1
  for (q, e) in factors do
    if q < 2 || e == 0 || n ≤ q then failure
    acc ← boundedPowMul (n - 1) q acc e
  if (n - 1) % acc != 0 then failure
  return acc

private def cubeData (n F : Nat) : Nat × Nat × Nat :=
  let R := (n - 1) / F
  let r := R % (2 * F)
  let s := R / (2 * F)
  (r, s, (r * r - 8 * s).sqrt)

/-- Cheap size and discriminant screening before any recursive certification.
The public checker validates these computations again on the final literal. -/
private def sufficient (n F : Nat) : Bool :=
  if n < F * F then true else
    let (r, s, w) := cubeData n F
    F % 2 == 0 && (n - 1) / F % 2 == 1 && 1 ≤ r &&
      n < (F + 1) * (2 * F * F + (r - 1) * F + 1) &&
      (s == 0 || r * r < 8 * s ||
        (w * w < r * r - 8 * s && r * r - 8 * s < (w + 1) * (w + 1)))

/-- Estimate recursive replay work using the table-factored predecessor.
Table leaves cost no construction nodes; a child already covered by its table
factors costs one. More expensive children receive a bit-size penalty. -/
private def childCost (q : Nat) : Nat :=
  if isTablePrime q then 0 else
    let factors := trial (q - 1)
    let F := (q - 1) / factors.residual
    if sufficient q F then 1 else 2 + q.log2 / 32

private def subsets (budget : ConstructionBudget) (n : Nat)
    (factors : List (Nat × Nat)) : List (List (Nat × Nat)) := Id.run do
  if factors.length > budget.maxFactors then return []
  let factors := factors.mergeSort (fun x y => x.1 ≤ y.1)
  if !decide ((factors.map Prod.fst).Pairwise (· < ·)) then return []
  if (product n factors).isNone then return []
  let costs := factors.map fun (q, _) => childCost q
  let mut choices : List (Nat × List (Nat × Nat)) := []
  for mask in [:min budget.maxSubsets (2 ^ factors.length)] do
    let selected := factors.zipIdx |>.filterMap fun (entry, i) =>
      if mask.testBit i then some entry else none
    if let some F := product n selected then
      if sufficient n F then
        let cost := (costs.zipIdx).foldl (fun acc (cost, i) =>
          if mask.testBit i then acc + 16 * cost + 1 else acc) 0
        choices := (cost, selected) :: choices
  return (choices.mergeSort fun x y => x.1 ≤ y.1).map Prod.snd

private def witness (budget : ConstructionBudget) (n q : Nat) (r : Hex.Rand) :
    Except PrimeCertFailure (Nat × Nat × Hex.Rand) := Id.run do
  let mut attempts := 0
  for a in budget.witnessBases do
    attempts := attempts + 1
    if checkWitness n q a then return .ok (a, attempts, r)
  match Internal.witnessSearchTrace n q r budget.randomWitnesses with
  | .ok (a, work, r') => return .ok (a, attempts + work, r')
  | .error f => return .error { f with attempts := attempts + f.attempts }

private def node (n F : Nat) (entries : List (Nat × Nat × PrimeCert)) : PrimeCert :=
  if n < F * F then .pock n entries else
    let (r, s, w) := cubeData n F
    .pock3 n r s w entries

mutual

private def generate (budget : ConstructionBudget) (factor : FactorSearch)
    (fuel n : Nat) (r : Hex.Rand) :
    Except PrimeCertFailure (PrimeCert × Nat × Hex.Rand) :=
  if n.log2 + 1 > budget.maxBits then .error ⟨.exhausted, 0, r⟩
  else if isTablePrime n then .ok (.small n, 0, r)
  else if !isProbablePrime n then .error ⟨.composite, 0, r⟩
  else match fuel with
  | 0 => .error ⟨.exhausted, 0, r⟩
  | fuel + 1 =>
      let allocation := { budget.factor with primeFuel := fuel }
      let result := factor allocation (n - 1) r
      if result.raw.factors.length > budget.maxFactors then
        .error ⟨.exhausted, result.attempts, result.rand⟩
      else match product n result.raw.factors with
      | none => .error ⟨.exhausted, result.attempts, result.rand⟩
      | some F =>
          if result.raw.residual == 0 || result.raw.residual > n - 1 ||
              F * result.raw.residual != n - 1 then
            .error ⟨.exhausted, result.attempts, result.rand⟩
          else choose budget factor fuel n (subsets budget n result.raw.factors)
            result.attempts result.rand
termination_by (fuel, 0, 0)

private def choose (budget : ConstructionBudget) (factor : FactorSearch)
    (fuel n : Nat) : List (List (Nat × Nat)) → Nat → Hex.Rand →
      Except PrimeCertFailure (PrimeCert × Nat × Hex.Rand)
  | [], work, r => .error ⟨.exhausted, work, r⟩
  | selected :: rest, work, r =>
      match assemble budget factor fuel n selected [] work r with
      | .error f => choose budget factor fuel n rest f.attempts f.rand
      | .ok (entries, work, r) =>
          match certProduct (n - 1) entries with
          | none => choose budget factor fuel n rest work r
          | some F =>
              let cert := node n F entries
              if checkPrime cert then .ok (cert, work, r)
              else choose budget factor fuel n rest work r
termination_by choices => (fuel, choices.length + 1, 0)

private def assemble (budget : ConstructionBudget) (factor : FactorSearch)
    (fuel n : Nat) : List (Nat × Nat) → List (Nat × Nat × PrimeCert) → Nat →
      Hex.Rand → Except PrimeCertFailure (List (Nat × Nat × PrimeCert) × Nat × Hex.Rand)
  | [], acc, work, r => .ok (acc.reverse, work, r)
  | (q, e) :: rest, acc, work, r =>
      match generate budget factor fuel q r with
      | .error f => .error ⟨.exhausted, work + f.attempts, f.rand⟩
      | .ok (child, childWork, r) =>
          match witness budget n q r with
          | .error f => .error ⟨.exhausted, work + childWork + f.attempts, f.rand⟩
          | .ok (a, witnessWork, r) =>
              assemble budget factor fuel n rest ((a, e - 1, child) :: acc)
                (work + childWork + witnessWork) r
termination_by entries => (fuel, 0, entries.length + 1)

end

/-- Construct and self-check the exact certificate to be reified. Factor data,
subset estimates and witnesses are untrusted; every success passes `checkPrime`.
A malformed producer can only prevent certificate construction. -/
def run (n : Nat) (r : Hex.Rand) (budget : ConstructionBudget := constructionBudget)
    (factor : FactorSearch := factorSearch) :
    Except PrimeCertFailure (Internal.PrimeCertSuccess n) :=
  match generate budget factor budget.maxDepth n r with
  | .error f => .error f
  | .ok (cert, attempts, rand) =>
      if hs : cert.subject = n then
        if hc : checkPrime cert = true then .ok ⟨⟨cert, hs, hc⟩, attempts, rand⟩
        else .error ⟨.exhausted, attempts, rand⟩
      else .error ⟨.exhausted, attempts, rand⟩

end Construction
end Hex.Nat
