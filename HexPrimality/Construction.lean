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
  maxBits : Nat := 521
  maxDepth : Nat := 32
  maxAttempts : Nat := 1024
  factor : FactorSearchBudget := {
    primeBudget := ⟨2, 32768⟩
    primeFuel := 32
    factorFuel := 1024
    smoothBounds := [64, 512, 4096, 32768, 262144, 524288]
    smoothBases := [2, 3] }
  witnessBases : List Nat := [2, 3, 5, 7, 11, 13, 17]
  randomWitnesses : Nat := 32
  maxFactors : Nat := 32
  maxSubsets : Nat := 4096
  maxSieveBound : Nat := 64
deriving Repr, DecidableEq

/-- The reproducible construction profile used by `primality?`. -/
def constructionBudget : ConstructionBudget := {}

namespace Construction

/-- The least positive sieve bound satisfying the cube-root size inequality, or zero.
This runs only during construction; the checker validates the chosen literal directly. -/
private def sieveBound (twoF r s : Nat) : Nat :=
  let b := twoF + r
  if b * b + 8 ≤ 8 * s then 0
  else Id.run do
    let sq := Nat.sqrt (b * b + 8 - 8 * s)
    let cand := (b - sq) / 2
    for m in [max 1 (cand - 3) : cand + 4] do
      if 2 * s + m * m < b * m + 2 then return m
    return 0

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

private def splitSmooth (allocation : FactorSearchBudget) (n limit : Nat) (r : Hex.Rand) :
    Option Nat × Nat := Id.run do
  let mut attempts := 0
  for bound in allocation.smoothBounds do
    for base in allocation.smoothBases do
      if attempts ≥ limit then return (none, attempts)
      let result := pMinusOneStage1Counted n base bound r
      attempts := attempts + result.attempts
      if let .factor d := result.result then
        return (some d, attempts)
  return (none, attempts)

private def factorGo (allocation : FactorSearchBudget) (limit : Nat) :
    Nat → List Nat → List (Nat × Nat) → Nat → Hex.Rand → Nat → FactorSearchResult
  | 0, stack, acc, residual, r, attempts =>
      ⟨⟨acc, stack.foldl (· * ·) residual⟩, r, attempts⟩
  | _ + 1, [], acc, residual, r, attempts => ⟨⟨acc, residual⟩, r, attempts⟩
  | fuel + 1, m :: stack, acc, residual, r, attempts =>
      if attempts ≥ limit then ⟨⟨acc, (m :: stack).foldl (· * ·) residual⟩, r, attempts⟩
      else if m ≤ 1 then factorGo allocation limit fuel stack acc residual r attempts
      else if isProbablePrime m then
        factorGo allocation limit fuel stack (insert m 1 acc) residual r attempts
      else
        let (d, work) := splitSmooth allocation m (limit - attempts) r
        match d with
        | some d => factorGo allocation limit fuel (d :: m / d :: stack) acc residual r
            (attempts + work)
        | none =>
            match Internal.rhoFactorCountedWith? m r
                (min allocation.primeBudget.rhoRestarts (limit - attempts - work))
                allocation.primeBudget.rhoSteps with
            | .ok success =>
                factorGo allocation limit fuel (success.factor :: m / success.factor :: stack)
                  acc residual success.rand (attempts + work + success.attempts)
            | .error f => factorGo allocation limit fuel stack acc (residual * m) f.rand
                (attempts + work + f.attempts)

/-- Table division followed by the explicitly budgeted smooth/rho worklist.
Every unresolved component is retained in the residual. -/
def factorSearch : FactorSearch := fun allocation n r =>
  if n = 0 then ⟨⟨[], 0⟩, r, 0⟩ else
    let initial := trial n
    let limit := allocation.attemptLimit.getD
      (allocation.factorFuel * (allocation.smoothBounds.length *
        allocation.smoothBases.length + allocation.primeBudget.rhoRestarts))
    factorGo allocation limit allocation.factorFuel [initial.residual] initial.factors 1 r 0

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
private def sufficient (budget : ConstructionBudget) (n F : Nat) : Bool :=
  if n < F * F then true else
    let (r, s, w) := cubeData n F
    let m := sieveBound (2 * F) r s
    F % 2 == 0 && (n - 1) / F % 2 == 1 && 1 ≤ r &&
      1 ≤ m && m ≤ min budget.maxSieveBound pocklingtonSieveCap && checkDivisors n F (m - 1) &&
      (s == 0 || r * r < 8 * s ||
        (w * w < r * r - 8 * s && r * r - 8 * s < (w + 1) * (w + 1)))

/-- Estimate recursive replay work using the table-factored predecessor.
Table leaves cost no construction nodes; a child already covered by its table
factors costs one. More expensive children receive a bit-size penalty. -/
private def childCost (budget : ConstructionBudget) (q : Nat) : Nat :=
  if isTablePrime q then 0 else
    let factors := trial (q - 1)
    let F := (q - 1) / factors.residual
    if sufficient budget q F then 1 else 2 + q.log2 / 32

private def subsets (budget : ConstructionBudget) (n : Nat)
    (factors : List (Nat × Nat)) : List (List (Nat × Nat)) := Id.run do
  if factors.length > budget.maxFactors then return []
  let factors := factors.mergeSort (fun x y => x.1 ≤ y.1)
  if !decide ((factors.map Prod.fst).Pairwise (· < ·)) then return []
  if (product n factors).isNone then return []
  let costs := factors.map fun (q, _) => childCost budget q
  let mut choices : List (Nat × List (Nat × Nat)) := []
  let count := 2 ^ factors.length
  for i in [:min budget.maxSubsets count] do
    let mask := if count ≤ budget.maxSubsets then i
      else if i == 0 then count - 1 else i - 1
    let selected := factors.zipIdx |>.filterMap fun (entry, i) =>
      if mask.testBit i then some entry else none
    if let some F := product n selected then
      if sufficient budget n F then
        let (r, s, _) := cubeData n F
        let divisions := if n < F * F then 0 else sieveBound (2 * F) r s - 1
        let cost := (costs.zipIdx).foldl (fun acc (cost, i) =>
          if mask.testBit i then acc + (16 * cost + 1) * (n.log2 + 1) else acc) divisions
        choices := (cost, selected) :: choices
  return (choices.mergeSort fun x y => x.1 ≤ y.1).map Prod.snd

private def witness (budget : ConstructionBudget) (n q : Nat) (r : Hex.Rand) :
    Except PrimeCertFailure (Nat × Nat × Hex.Rand) := Id.run do
  let mut attempts := 0
  for a in budget.witnessBases do
    if attempts ≥ budget.maxAttempts then return .error ⟨.exhausted, attempts, r⟩
    attempts := attempts + 1
    if checkWitness n q a then return .ok (a, attempts, r)
  match Internal.witnessSearchTrace n q r
      (min budget.randomWitnesses (budget.maxAttempts - attempts)) with
  | .ok (a, work, r') => return .ok (a, attempts + work, r')
  | .error f => return .error { f with attempts := attempts + f.attempts }

private def node (n F : Nat) (entries : List (Nat × Nat × PrimeCert)) : PrimeCert :=
  if n < F * F then .pock n entries else
    let (r, s, w) := cubeData n F
    let m := sieveBound (2 * F) r s
    if m == 1 then .pock3 n r s w entries else .pock3Sieve n r s w m entries

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
      let cheap := subsets budget n (trial (n - 1)).factors
      match choose budget factor fuel n cheap [] 0 r with
      | .ok result => .ok result
      | .error first =>
        let remaining := { budget with maxAttempts := budget.maxAttempts - first.attempts }
        let r := first.rand
        let result : Except PrimeCertFailure (PrimeCert × Nat × Hex.Rand) := Id.run do
          let allocation := { budget.factor with
            primeFuel := fuel
            attemptLimit := some remaining.maxAttempts }
          let result := factor allocation (n - 1) r
          return if result.attempts > remaining.maxAttempts ||
              result.raw.factors.length > budget.maxFactors then
            .error ⟨.exhausted, result.attempts, result.rand⟩
          else match product n result.raw.factors with
          | none => .error ⟨.exhausted, result.attempts, result.rand⟩
          | some F =>
              if result.raw.residual == 0 || result.raw.residual > n - 1 ||
                  F * result.raw.residual != n - 1 then
                .error ⟨.exhausted, result.attempts, result.rand⟩
              else
                let choices := (subsets remaining n result.raw.factors).filter
                  (fun fs => !cheap.contains fs)
                choose remaining factor fuel n choices [] result.attempts result.rand
        match result with
        | .ok (cert, work, rand) => .ok (cert, first.attempts + work, rand)
        | .error failure => .error { failure with attempts := first.attempts + failure.attempts }

termination_by (fuel, 0, 0)

private def choose (budget : ConstructionBudget) (factor : FactorSearch)
    (fuel n : Nat) : List (List (Nat × Nat)) → List PrimeCert → Nat → Hex.Rand →
      Except PrimeCertFailure (PrimeCert × Nat × Hex.Rand)
  | [], _, work, r => .error ⟨.exhausted, work, r⟩
  | selected :: rest, cache, work, r =>
      if work ≥ budget.maxAttempts then .error ⟨.exhausted, work, r⟩ else
      let (result, cache) := assemble budget factor fuel n selected [] cache work r
      match result with
      | .error f => choose budget factor fuel n rest cache f.attempts f.rand
      | .ok (entries, work, r) =>
          match certProduct (n - 1) entries with
          | none => choose budget factor fuel n rest cache work r
          | some F =>
              let cert := node n F entries
              if checkPrime cert then .ok (cert, work, r)
              else choose budget factor fuel n rest cache work r
termination_by choices => (fuel, choices.length + 1, 0)

private def assemble (budget : ConstructionBudget) (factor : FactorSearch)
    (fuel n : Nat) : List (Nat × Nat) → List (Nat × Nat × PrimeCert) →
      List PrimeCert → Nat → Hex.Rand →
      (Except PrimeCertFailure (List (Nat × Nat × PrimeCert) × Nat × Hex.Rand)) ×
        List PrimeCert
  | [], acc, cache, work, r => (.ok (acc.reverse, work, r), cache)
  | (q, e) :: rest, acc, cache, work, r =>
      if work ≥ budget.maxAttempts then (.error ⟨.exhausted, work, r⟩, cache) else
      let child : Except PrimeCertFailure (PrimeCert × Nat × Hex.Rand) :=
        match cache.find? (fun c => c.subject == q) with
        | some c => .ok (c, 0, r)
        | none => generate { budget with maxAttempts := budget.maxAttempts - work }
            factor fuel q r
      match child with
      | .error f => (.error ⟨.exhausted, work + f.attempts, f.rand⟩, cache)
      | .ok (child, childWork, r) =>
          let cache := if cache.any (fun c => c.subject == q) then cache else child :: cache
          match witness { budget with maxAttempts := budget.maxAttempts - work - childWork }
              n q r with
          | .error f => (.error ⟨.exhausted, work + childWork + f.attempts, f.rand⟩, cache)
          | .ok (a, witnessWork, r) =>
              assemble budget factor fuel n rest ((a, e - 1, child) :: acc) cache
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
