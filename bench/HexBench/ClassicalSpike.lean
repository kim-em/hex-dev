/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus.Basic

/-!
Feasibility spike (UNPROVEN): a minimal end-to-end classical Berlekamp-Zassenhaus
that reuses the library's good-prime selection (`choosePrimeData?`) and Hensel
lift (`henselLiftData`), but replaces the materialized-powerset recombination
with a smart, size-ordered, factor-removing search. Int variant only here;
machine-word variant and benchmarking added alongside.

Restricted to monic squarefree primitive inputs (our test corpus:
`(x-1)...(x-n)` and `Phi_15`), which keeps the recombination candidates monic so
no leading-coefficient scaling / primitive-part step is needed.

Proves nothing. This is a measurement artifact to decide the C architecture.
-/

open Hex

local instance : Inhabited ZPoly := ⟨0⟩

/-- `(x-1)(x-2)...(x-n)`, monic, fully split over `ℤ`. -/
def linearProduct (n : Nat) : ZPoly :=
  (List.range n).foldl
    (fun acc i => acc * DensePoly.ofCoeffs #[-(Int.ofNat (i + 1)), 1]) (1 : ZPoly)

/-- 15th cyclotomic polynomial: irreducible over `ℤ`, splits mod p. -/
def phi15 : ZPoly := DensePoly.ofCoeffs #[1, -1, 0, 1, -1, 1, 0, -1, 1]

/-- All size-`k` sub-lists of `xs`, each paired with its complement. Structural;
worst-case `2^|xs|`, but the caller tries small `k` first and stops early. -/
def chooseWithComplement {α : Type} : List α → Nat → List (List α × List α)
  | xs, 0 => [([], xs)]
  | [], _ + 1 => []
  | x :: xs, k + 1 =>
      (chooseWithComplement xs k).map (fun sc => (x :: sc.1, sc.2)) ++
      (chooseWithComplement xs (k + 1)).map (fun sc => (sc.1, x :: sc.2))

def firstSomeList {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, f => match f x with | some y => some y | none => firstSomeList xs f

/-- Reduce every coefficient of `g` into `[0, m)`. -/
def reduceModInt (g : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs (g.toArray.map (fun c => Int.emod c (Int.ofNat m)))

/-- Product of a subset of lifted factors, reduced mod `m` after each multiply. -/
def productModInt (s : List ZPoly) (m : Nat) : ZPoly :=
  s.foldl (fun acc g => reduceModInt (acc * g) m) (1 : ZPoly)

/-- First subset of `remaining` (sizes `lo..hi`) whose centered product exactly
divides `target`; returns the integer factor, the quotient, and the unused
factors. Smallest size first, so fully-split inputs peel singletons in O(r). -/
partial def findDivisorInt
    (target : ZPoly) (remaining : List ZPoly) (modulus : Nat) (size hi : Nat) :
    Option (ZPoly × ZPoly × List ZPoly) :=
  if size > hi then none
  else
    let scan := firstSomeList (chooseWithComplement remaining size) fun sc =>
      let cand := centeredLiftPoly (productModInt sc.1 modulus) modulus
      match exactQuotient? target cand with
      | some q => some (cand, q, sc.2)
      | none => none
    match scan with
    | some res => some res
    | none => findDivisorInt target remaining modulus (size + 1) hi

/-- Peel irreducible integer factors off `target` one at a time. When no proper
subset (size `1..r/2`) divides, the remaining lifted factors collectively equal
`target`, which is therefore irreducible. -/
partial def recombInt
    (target : ZPoly) (remaining : List ZPoly) (modulus : Nat) (acc : Array ZPoly) :
    Array ZPoly :=
  let r := remaining.length
  if r == 0 then acc
  else
    match findDivisorInt target remaining modulus 1 (r / 2) with
    | some (cand, quotient, rest) => recombInt quotient rest modulus (acc.push cand)
    | none => acc.push target

/-- Classical BZ, Int arithmetic. Assumes `f` monic squarefree primitive. -/
def classicalFactorInt (f : ZPoly) : Option (Array ZPoly) :=
  match choosePrimeData? f with
  | none => none
  | some pd =>
      let bound := ZPoly.exhaustiveLiftBound f (ZPoly.defaultFactorCoeffBound f)
      let k := precisionForCoeffBound bound pd.p
      let ld := henselLiftData f k pd
      let modulus := pd.p ^ k
      some (recombInt f ld.liftedFactors.toList modulus #[])

/-- Balanced product-tree Hensel lift: split the mod-p factors in half, lift the
two-way split `target ≡ g·h` once via `henselLiftQuadratic`, recurse into each
half. O(log r) depth and O(n log r) total split-degree, vs the library's
sequential O(n·r) `multifactorLiftQuadraticList`. -/
partial def balancedLift (p k : Nat) [ZMod64.Bounds p]
    (target : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  if factors.size <= 1 then #[ZPoly.reduceModPow target p k]
  else
    let half := factors.size / 2
    let L := factors.extract 0 half
    let R := factors.extract half factors.size
    let g := Array.polyProduct L
    let h := Array.polyProduct R
    let xgcd := ZPoly.normalizedXGCD p g h
    let lifted := ZPoly.henselLiftQuadratic p k target g h
      (FpPoly.liftToZ xgcd.left) (FpPoly.liftToZ xgcd.right)
    balancedLift p k lifted.g L ++ balancedLift p k lifted.h R

/-- Mignotte lift precision for `f` under prime data `pd`. -/
def mignotteK (f : ZPoly) (pd : PrimeChoiceData) : Nat :=
  precisionForCoeffBound (ZPoly.exhaustiveLiftBound f (ZPoly.defaultFactorCoeffBound f)) pd.p

/-- Classical BZ, Int, balanced-tree lift, explicit precision `k`. -/
def classicalFactorBalancedK (f : ZPoly) (k : Nat) : Option (Array ZPoly) :=
  match choosePrimeData? f with
  | none => none
  | some pd =>
      letI := pd.bounds
      let factors := pd.factorsModP.map FpPoly.liftToZ
      some (recombInt f (balancedLift pd.p k f factors).toList (pd.p ^ k) #[])

/-- Classical BZ, Int, balanced-tree lift, conservative Mignotte precision. -/
def classicalFactorBalanced (f : ZPoly) : Option (Array ZPoly) :=
  match choosePrimeData? f with
  | none => none
  | some pd =>
      letI := pd.bounds
      let k := mignotteK f pd
      let factors := pd.factorsModP.map FpPoly.liftToZ
      some (recombInt f (balancedLift pd.p k f factors).toList (pd.p ^ k) #[])

/-- Classical BZ, Int, but lift to an EXPLICIT precision `k` (not the worst-case
Mignotte bound). Sound: recombination's `exactQuotient?` only accepts real ℤ
divisors, so too-small `k` can only under-factor, never mis-factor. -/
def classicalFactorIntK (f : ZPoly) (k : Nat) : Option (Array ZPoly) :=
  match choosePrimeData? f with
  | none => none
  | some pd =>
      let ld := henselLiftData f k pd
      some (recombInt f ld.liftedFactors.toList (pd.p ^ k) #[])

/-- Sorted multiset of factor degrees, for a quick correctness signature. -/
def degreeSignature (fs : Array ZPoly) : List Nat :=
  (fs.toList.map (fun g => g.degree?.getD 0)).mergeSort (· ≤ ·)

#eval degreeSignature ((classicalFactorInt (linearProduct 6)).getD #[])   -- expect [1,1,1,1,1,1]
#eval degreeSignature ((classicalFactorInt phi15).getD #[])               -- expect [8]
#eval degreeSignature ((classicalFactorInt (linearProduct 12)).getD #[])  -- expect twelve 1s

/-- `(x-1-s)(x-2-s)...(x-n-s)`: a shifted fully-split family, used to defeat
loop-invariant hoisting (each `s` is a distinct input). -/
def linearProductShift (n s : Nat) : ZPoly :=
  (List.range n).foldl
    (fun acc i => acc * DensePoly.ofCoeffs #[-(Int.ofNat (i + 1 + s)), 1]) (1 : ZPoly)

/-- Checksum the actual factor coefficients so the optimizer cannot drop the
factorization (defeats CSE/dead-code elimination). -/
def factorChecksum (fs : Array ZPoly) : UInt64 :=
  fs.foldl (fun acc g =>
    g.toArray.foldl (fun a c => a * 1000003 + UInt64.ofNat c.natAbs) acc) 7

/-- Time `reps` factorizations, cycling through `inputs` (distinct each call) and
checksumming real factor coefficients. Marginal µs per call. Flushes on return. -/
def timeFamily (label : String) (reps : Nat) (inputs : Array ZPoly)
    (act : ZPoly → Array ZPoly) : IO Unit := do
  let m := inputs.size
  let mut w : UInt64 := 0
  for i in [0:Nat.min m 8] do w := w + factorChecksum (act inputs[i]!)
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := w
  for i in [0:reps] do
    acc := acc + factorChecksum (act (inputs[i % m]!))
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/call   (reps={reps}, sink={acc})"
  (← IO.getStdout).flush

/-- Generic phase timer over a distinct-input family; `sink` forces evaluation. -/
def timePhase (label : String) (reps : Nat) (inputs : Array ZPoly)
    (act : ZPoly → UInt64) : IO Unit := do
  let out ← IO.getStdout
  let m := inputs.size
  let mut w : UInt64 := 0
  for i in [0:Nat.min m 8] do w := w + act inputs[i]!
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := w
  for i in [0:reps] do acc := acc + act (inputs[i % m]!)
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/call (sink={acc})"
  out.flush

/-- Cheap checksum of a ZPoly's coefficients. -/
def zsum (g : ZPoly) : UInt64 := g.toArray.foldl (fun a c => a * 1000003 + UInt64.ofNat c.natAbs) 7

def main : IO Unit := do
  let out ← IO.getStdout
  IO.println "=== classical BZ spike: per-phase breakdown (Int) ==="
  IO.println "    16 distinct shifted (x-a)..(x-a-(n-1)) inputs per degree"
  out.flush
  for n in [8, 12, 16, 20, 24] do
    let inputs := (Array.range 16).map (fun s => linearProductShift n s)
    -- correctness: balanced lift must agree (recover all n linear factors)
    let sB := degreeSignature ((classicalFactorBalancedK inputs[0]! 4).getD #[])
    let sBm := degreeSignature ((classicalFactorBalanced inputs[0]!).getD #[])
    IO.println s!"--- degree {n} ---  (balanced k=4 size={sB.length}, balanced Mignotte size={sBm.length}, want {n})"; out.flush
    timePhase "seq      Mignotte" 100 inputs (fun f => factorChecksum ((classicalFactorInt f).getD #[]))
    timePhase "balanced Mignotte" 100 inputs (fun f => factorChecksum ((classicalFactorBalanced f).getD #[]))
    timePhase "seq      k=4     " 100 inputs (fun f => factorChecksum ((classicalFactorIntK f 4).getD #[]))
    timePhase "balanced k=4     " 100 inputs (fun f => factorChecksum ((classicalFactorBalancedK f 4).getD #[]))
