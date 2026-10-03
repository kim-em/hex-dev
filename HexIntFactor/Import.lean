/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Replay
public import HexIntFactor.Construction

public section

/-! Pure bounded import of untrusted factor proposals. Discovery supplies only
integer hints. Acceptance always replays the existing factorization checkers. -/

namespace Hex.Nat

/-- Signed, untrusted discovery data, optionally with existing Hex evidence. -/
structure FactorProposal where
  subject : Int
  entries : List (Int × Int × Option PrimeCert)
deriving Repr

/-- Independent structural and per-base certificate-construction allocations. -/
structure ImportBudget where
  maxBits : Nat := 256
  maxEntries : Nat := 64
  maxExponent : Nat := 256
  maxCertNodes : Nat := 4096
  maxCertDepth : Nat := 64
  completion : ConstructionBudget := {
    maxBits := 256
    maxDepth := 8
    maxAttempts := 128
    factor := {
      primeBudget := ⟨2, 65536, .off⟩
      primeFuel := 8
      factorFuel := 16
      smoothBounds := [64, 512, 4096]
      smoothBases := [2, 3] }
    randomWitnesses := 8
    maxFactors := 32
    maxSubsets := 256
    maxSieveBound := 64 }
deriving Repr

/-- Import rejection is distinct from unfinished certificate construction. -/
inductive ImportError where
  | zero | subjectMismatch | bounds | invalidBase | invalidExponent
  | invalidArithmetic | invalidCertificate | certificateBounds | rejected
deriving Repr, BEq

/-- No primality claim accompanies an unfinished residual piece. -/
inductive CompletionStop where
  | composite | unfinished | certificateBounds
deriving Repr, BEq

/-- Validated arithmetic hints; their bases are not certified prime powers. -/
structure ResidualPiece where
  base : Nat
  exponent : Nat
  stop : CompletionStop
  attempts : Nat := 0
  obligation : Option Nat := none
  events : List FactorEvent := []
deriving Repr

/-- Both branches carry ordinary checker acceptance for the requested subject. -/
inductive CheckedFactors (n : Nat) where
  | complete (value : CheckedFactorization n)
  | partialResult (value : CheckedPartialFactorization n)

/-- View accepted data uniformly as a partial certificate. -/
def CheckedFactors.raw {n : Nat} : CheckedFactors n → PartialFactorization
  | .complete F => ⟨n, F.raw.factors, 1⟩
  | .partialResult F => F.raw

/-- Import progress and untrusted residual hints, retaining random state. -/
structure ImportResult (n : Nat) where
  value : CheckedFactors n
  rand : Hex.Rand
  unlisted : Nat
  unresolved : List ResidualPiece
  attempts : Nat := 0
  events : List FactorEvent := []

namespace FactorImport

private inductive Item where
  | cert (depth : Nat) (value : PrimeCert)
  | factors (depth : Nat) (values : List (Nat × Nat × PrimeCert))

private def smallInts (b : ImportBudget) (ns : List Nat) : Bool :=
  ns.all (fun n => HexArith.bitLength n ≤ b.maxBits)

private def inspect (b : ImportBudget) : Nat → List Item → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, .cert depth c :: rest =>
      if depth > b.maxCertDepth then false else
      match c with
      | .small n => smallInts b [n] && inspect b fuel rest
      | .pock n fs => smallInts b [n] && inspect b fuel (.factors depth fs :: rest)
      | .pock3 n r s w fs =>
          smallInts b [n, r, s, w] && inspect b fuel (.factors depth fs :: rest)
      | .pock3Sieve n r s w m fs =>
          smallInts b [n, r, s, w, m] && m ≤ pocklingtonSieveCap &&
            inspect b fuel (.factors depth fs :: rest)
  | fuel + 1, .factors depth fs :: rest =>
      match fs with
      | [] => inspect b fuel rest
      | (a, e, c) :: tail =>
          smallInts b [a, e] && e ≤ b.maxExponent &&
            inspect b fuel (.cert (depth + 1) c :: .factors depth tail :: rest)

/-- Bound syntax traversal before invoking the recursive primality checker.
The node allocation counts constructors and factor-list cells together. -/
def certificateFits (b : ImportBudget) (c : PrimeCert) : Bool :=
  inspect b b.maxCertNodes [.cert 1 c]

private structure Entry where
  base : Nat
  exponent : Nat
  cert : Option PrimeCert

private def validate (b : ImportBudget) :
    Nat → Nat → List (Int × Int × Option PrimeCert) →
      Except ImportError (List Entry × Nat)
  | _, quotient, [] => .ok ([], quotient)
  | 0, _, _ :: _ => .error .bounds
  | fuel + 1, quotient, (base, exponent, cert) :: rest => do
      if base < 2 then throw .invalidBase
      if exponent ≤ 0 || exponent > b.maxExponent then throw .invalidExponent
      let p := base.toNat
      let e := exponent.toNat
      unless HexArith.bitLength p ≤ b.maxBits do throw .bounds
      let some power := boundedPowMul quotient p 1 e | throw .invalidArithmetic
      unless quotient % power == 0 do throw .invalidArithmetic
      if let some c := cert then
        unless certificateFits b c do throw .certificateBounds
        unless c.subject == p && checkPrime c do throw .invalidCertificate
      let (tail, unlisted) ← validate b fuel (quotient / power) rest
      return (⟨p, e, cert⟩ :: tail, unlisted)

private def merge (b : ImportBudget) : List Entry → Except ImportError (List Entry)
  | [] => .ok []
  | a :: rest => do
      let tail ← merge b rest
      match tail with
      | c :: cs =>
          if a.base == c.base then
            if a.exponent + c.exponent > b.maxExponent then throw .invalidExponent
            return { a with
              exponent := a.exponent + c.exponent
              cert := a.cert.or c.cert } :: cs
          else return a :: tail
      | [] => return [a]

/-- Replay both the final partial and, when applicable, complete checker. -/
def accept (n : Nat) (raw : PartialFactorization) : Except ImportError (CheckedFactors n) :=
  if hs : raw.subject = n then
    if hv : checkPartial raw = true then
      if raw.residual = 1 then
        let F : Factorization := ⟨n, raw.factors⟩
        if hf : checkFactorization F = true then .ok (.complete ⟨F, rfl, hf⟩)
        else .error .rejected
      else .ok (.partialResult ⟨raw, hs, hv⟩)
    else .error .rejected
  else .error .subjectMismatch

/-- Candidate construction for cost attribution; this is untrusted raw data,
not an alternative acceptance boundary. Use `importFactors` for checked output. -/
structure Candidate where
  raw : PartialFactorization
  rand : Hex.Rand
  unlisted : Nat
  unresolved : List ResidualPiece
  attempts : Nat
  events : List FactorEvent

/-- Validate all arithmetic and supplied evidence before any completion work. -/
def prepare (b : ImportBudget) (n : Nat) (proposal : FactorProposal) (r : Hex.Rand) :
    Except ImportError Candidate := do
  if n == 0 then throw .zero
  if HexArith.bitLength n > b.maxBits then throw .bounds
  unless proposal.subject == (n : Int) do throw .subjectMismatch
  let (entries, unlisted) ← validate b b.maxEntries n proposal.entries
  -- Stable sorting preserves the first supplied certificate in proposal order.
  let entries ← merge b (entries.mergeSort (fun a c => a.base ≤ c.base))
  let mut factors := []
  let mut residual := unlisted
  let mut rand := r
  let mut unresolved := []
  let mut attempts := 0
  let mut events := []
  for entry in entries do
    let mut cert := entry.cert
    let mut stop := CompletionStop.unfinished
    let mut used := 0
    let mut obligation := none
    let mut trace := []
    if cert.isNone && b.completion.maxAttempts > 0 then
      let initial := Construction.runTraced entry.base rand b.completion
      let found : Except Construction.Failure (Internal.PrimeCertSuccess entry.base) :=
        match initial with
        | .ok success => .ok success
        | .error failure => Construction.retry entry.base b.completion failure
            (ecmFactorSearch 128 1024 2)
      match found with
      | .ok success =>
          rand := success.rand
          used := success.attempts
          trace := success.events
          if certificateFits b success.cert.raw then cert := some success.cert.raw
          else stop := .certificateBounds
      | .error failure =>
          rand := failure.rand
          used := failure.attempts
          trace := failure.events
          obligation := failure.obligation
          stop := if failure.stop == PrimeCertStop.composite then .composite else .unfinished
    attempts := attempts + used
    events := events ++ trace
    if let some c := cert then
      factors := ⟨entry.exponent, c⟩ :: factors
    else
      let some next := boundedPowMul n entry.base residual entry.exponent
        | throw .invalidArithmetic
      residual := next
      unresolved := {
        base := entry.base
        exponent := entry.exponent
        stop
        attempts := used
        obligation
        events := trace } :: unresolved
  unresolved := unresolved.reverse
  -- Residual hints are checked separately from the accepted partial data.
  let mut reconstructed := unlisted
  for piece in unresolved do
    let some next := boundedPowMul n piece.base reconstructed piece.exponent
      | throw .invalidArithmetic
    reconstructed := next
  unless reconstructed == residual do throw .invalidArithmetic
  return ⟨⟨n, factors.reverse, residual⟩, rand, unlisted, unresolved, attempts, events⟩

end FactorImport

/-- Pure subject-bound import, independent of optional external process IO. -/
def importFactors (b : ImportBudget) (n : Nat) (proposal : FactorProposal) (r : Hex.Rand) :
    Except ImportError (ImportResult n) := do
  let c ← FactorImport.prepare b n proposal r
  let value ← FactorImport.accept n c.raw
  return ⟨value, c.rand, c.unlisted, c.unresolved, c.attempts, c.events⟩

end Hex.Nat
