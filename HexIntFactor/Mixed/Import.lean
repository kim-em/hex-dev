/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Mixed.Replay
public import HexIntFactor.Import
public import HexECPP.Search

public section

/-! Pure bounded mixed proposal import. Discovery, legacy completion, ECPP
completion and replay have independent allocations and diagnostics. -/

namespace Hex.Nat.Mixed

/-- Signed arithmetic proposals with optional subject-bound mixed evidence. -/
structure FactorProposal where
  subject : Int
  entries : List (Int × Int × Option Evidence)
deriving Repr

/-- Independent structural, legacy, native ECPP and replay allocations. -/
structure ImportBudget where
  maxSubjectBits : Nat := 4096
  maxBaseBits : Nat := 512
  maxEntries : Nat := 64
  maxExponent : Nat := 4096
  maxCertNodes : Nat := 4096
  maxCertDepth : Nat := 64
  maxEcppRows : Nat := 20
  maxEcppNodes : Nat := 32
  maxInverseWitnesses : Nat := 1024
  completion : ConstructionBudget := { ({} : Hex.Nat.ImportBudget).completion with maxBits := 512 }
  maxLegacyAttempts : Nat := 8192
  ecppBits : Option Nat := none
  maxEcppCalls : Nat := 2
  ecppSeed : Nat := 0
deriving Repr

/-- Completion failures never certify a residual or assert completeness. -/
inductive CompletionStop where
  | supplied | certified | composite | legacySkipped | legacyStarved | legacyExhausted
  | ecppDisabled | ecppSkipped | ecppStarved | ecppExhausted (resource : Hex.ECPP.Resource)
  | certificateBounds
deriving Repr, BEq

/-- Uncertified arithmetic hints reconstruct the checked residual. -/
structure ResidualPiece where
  base : Nat
  exponent : Nat
  stop : CompletionStop
  legacyStop : CompletionStop
  attempts : Nat
  obligation : Option Nat
  events : List FactorEvent
deriving Repr

/-- Retain completion history even when ECPP subsequently certifies a base. -/
structure Completion where
  base : Nat
  legacyStop : CompletionStop
  legacyAttempts : Nat
  ecppStop : CompletionStop
  ecpp : Option Hex.ECPP.SearchResult
deriving Repr

/-- Both branches are computationally checked at the requested subject. -/
inductive CheckedFactors (n : Nat) where
  | complete (value : CheckedFactorization n)
  | partialResult (value : CheckedPartialFactorization n)

/-- Uniform checked-result view; residual one identifies complete data. -/
def CheckedFactors.raw {n : Nat} : CheckedFactors n → PartialFactorization
  | .complete F => ⟨n, F.raw.factors, 1⟩
  | .partialResult F => F.raw

/-- Checked progress, legacy randomness and independent ECPP search histories. -/
structure ImportResult (n : Nat) where
  value : CheckedFactors n
  rand : Hex.Rand
  unlisted : Nat
  unresolved : List ResidualPiece
  attempts : Nat
  events : List FactorEvent
  ecppCalls : Nat
  completions : List Completion

namespace FactorImport

/-- Legacy syntax admission uses base limits independently of the whole subject. -/
def legacyBudget (b : ImportBudget) : Hex.Nat.ImportBudget := {
  maxBits := min b.maxBaseBits 512, maxEntries := min b.maxEntries 64
  maxExponent := min b.maxExponent 4096, maxCertNodes := min b.maxCertNodes 4096
  maxCertDepth := min b.maxCertDepth 64, completion := b.completion }

/-- Count constructors, including embedded terminal certificates, with fuel.
List cells do not count toward the ECPP constructor-node allocation. -/
private def primeNodes : Nat → List PrimeCert → Option Nat
  | fuel, [] => some fuel
  | 0, _ :: _ => none
  | fuel + 1, c :: rest =>
      match c with
      | .small _ => primeNodes fuel rest
      | .pock _ fs | .pock3 _ _ _ _ fs | .pock3Sieve _ _ _ _ _ fs =>
          if (fs.take (fuel + 1)).length > fuel then none else
          primeNodes fuel (fs.map (fun (_, _, child) => child) ++ rest)

private def ecppFits (b : ImportBudget) : Nat → Nat → Hex.ECPP.Cert → Bool
  | _, 0, _ => false
  | _, nodes + 1, .base c =>
      (primeNodes nodes [c]).isSome && Hex.Nat.FactorImport.certificateFits (legacyBudget b) c
  | rows, nodes + 1, .step n a c x y d ws child =>
      if rows >= min b.maxEcppRows 20 then false else
      if (ws.take (min b.maxInverseWitnesses 1024 + 1)).length > min b.maxInverseWitnesses 1024
      then false else
      [n, a, c, x, y, d].all (fun z => HexArith.bitLength z ≤ min b.maxBaseBits 512) &&
        ws.all (fun z => HexArith.bitLength z ≤ min b.maxBaseBits 512) &&
        ecppFits b (rows + 1) nodes child

/-- Preflight all evidence fields and bounded transcripts before replay. -/
def certificateFits (b : ImportBudget) : Evidence → Bool
  | .legacy c => Hex.Nat.FactorImport.certificateFits (legacyBudget b) c
  | .ecpp c => ecppFits b 0 (min b.maxEcppNodes 32) c

private structure Entry where
  base : Nat
  exponent : Nat
  cert : Option Evidence

private def validate (b : ImportBudget) :
    Nat → Nat → List (Int × Int × Option Evidence) →
      Except ImportError (List Entry × Nat)
  | _, quotient, [] => .ok ([], quotient)
  | 0, _, _ :: _ => .error .bounds
  | fuel + 1, quotient, (base, exponent, cert) :: rest => do
      if base < 2 then throw .invalidBase
      if exponent ≤ 0 || exponent > min b.maxExponent 4096 then throw .invalidExponent
      let p := base.toNat
      let e := exponent.toNat
      unless HexArith.bitLength p ≤ min b.maxBaseBits 512 do throw .bounds
      let some power := boundedPowMul quotient p 1 e | throw .invalidArithmetic
      unless quotient % power == 0 do throw .invalidArithmetic
      if let some c := cert then
        unless certificateFits b c do throw .certificateBounds
        unless checkEvidence p c do throw .invalidCertificate
      let (tail, unlisted) ← validate b fuel (quotient / power) rest
      return (⟨p, e, cert⟩ :: tail, unlisted)

private def merge (b : ImportBudget) : List Entry → Except ImportError (List Entry)
  | [] => .ok []
  | a :: rest => do
      let tail ← merge b rest
      match tail with
      | c :: cs =>
          if a.base == c.base then
            if a.exponent + c.exponent > min b.maxExponent 4096 then throw .invalidExponent
            return { a with
              exponent := a.exponent + c.exponent
              cert := a.cert.or c.cert } :: cs
          else return a :: tail
      | [] => return [a]

/-- Replay partial data once; residual one supplies complete acceptance. -/
def accept (n : Nat) (raw : PartialFactorization) : Except ImportError (CheckedFactors n) :=
  if hs : raw.subject = n then
    if hv : checkPartial raw = true then
      if hr : raw.residual = 1 then
        let F : Factorization := ⟨n, raw.factors⟩
        let hf := checkFactorization_of_checkPartial hv hr
        .ok (.complete ⟨F, rfl, by simpa only [hs] using hf⟩)
      else .ok (.partialResult ⟨raw, hs, hv⟩)
    else .error .rejected
  else .error .subjectMismatch

/-- Candidate preparation is untrusted and never substitutes for final replay. -/
structure Candidate where
  raw : PartialFactorization
  rand : Hex.Rand
  unlisted : Nat
  unresolved : List ResidualPiece
  attempts : Nat
  events : List FactorEvent
  ecppCalls : Nat
  completions : List Completion

/-- Validate all arithmetic and supplied evidence before any production.
Per-base legacy attempts are clamped to the shared remaining allocation. -/
def prepare (b : ImportBudget) (n : Nat) (proposal : FactorProposal) (r : Hex.Rand) :
    Except ImportError Candidate := do
  if n == 0 then throw .zero
  if HexArith.bitLength n > min b.maxSubjectBits 4096 then throw .bounds
  if let some bits := b.ecppBits then
    unless bits == 256 || bits == 512 do throw .bounds
  unless proposal.subject == (n : Int) do throw .subjectMismatch
  let (entries, unlisted) ← validate b (min b.maxEntries 64) n proposal.entries
  let entries ← merge b (entries.mergeSort (fun a c => a.base ≤ c.base))
  let mut factors := []
  let mut residual := unlisted
  let mut rand := r
  let mut unresolved := []
  let mut attempts := 0
  let mut events := []
  let mut ecppCalls := 0
  let mut completions := []
  for entry in entries do
    let mut cert := entry.cert
    let allowance := min 128 (min b.completion.maxAttempts (b.maxLegacyAttempts - attempts))
    let mut legacyStop := if cert.isSome then CompletionStop.supplied
      else if b.completion.maxAttempts == 0 then .legacySkipped
      else if allowance == 0 then .legacyStarved else .legacyExhausted
    let mut used := 0
    let mut obligation := none
    let mut trace := []
    if cert.isNone && allowance > 0 then
      let budget := { b.completion with maxAttempts := allowance, maxBits := min b.maxBaseBits 512 }
      let first := Construction.runTraced entry.base rand budget
      let result : Except Construction.Failure (Hex.Nat.Internal.PrimeCertSuccess entry.base) := match first with
        | .ok success => .ok success
        | .error failure => Construction.retry entry.base budget failure (ecmFactorSearch 128 1024 2)
      match result with
      | .ok success =>
          rand := success.rand
          used := success.attempts
          trace := success.events
          if certificateFits b (.legacy success.cert.raw) then
            cert := some (.legacy success.cert.raw)
            legacyStop := .certified
          else legacyStop := .certificateBounds
      | .error failure =>
          rand := failure.rand
          used := failure.attempts
          trace := failure.events
          obligation := failure.obligation
          legacyStop := if failure.stop == PrimeCertStop.composite then .composite else .legacyExhausted
    attempts := attempts + used
    events := events ++ trace
    let mut stop := legacyStop
    let mut ecppStop := if b.ecppBits.isSome then CompletionStop.ecppSkipped else .ecppDisabled
    let mut ecpp := none
    if cert.isNone && legacyStop != .composite then
      if let some bits := b.ecppBits then
        if b.maxEcppCalls == 0 then
          stop := .ecppSkipped
        else if ecppCalls >= min b.maxEcppCalls 2 then
          stop := .ecppStarved
          ecppStop := .ecppStarved
        else
          let seed := b.ecppSeed + ecppCalls
          -- Reserve a full independent allocation, including failed calls.
          ecppCalls := ecppCalls + 1
          let policy := if bits == 512 then Hex.ECPP.public512Budget else Hex.ECPP.public256Budget
          let policy := { policy with
            maxRows := some (min b.maxEcppRows 20), maxNodes := some (min b.maxEcppNodes 32) }
          let result := Hex.ECPP.produce entry.base seed policy
          ecpp := some result
          match result.result with
          | .error failure =>
              stop := .ecppExhausted failure.resource
              ecppStop := stop
          | .ok c =>
              if certificateFits b (.ecpp c) then
                cert := some (.ecpp c)
                stop := .certified
              else stop := .certificateBounds
              ecppStop := stop
    completions := ⟨entry.base, legacyStop, used, ecppStop, ecpp⟩ :: completions
    if let some c := cert then
      factors := ⟨entry.base, entry.exponent, c⟩ :: factors
    else
      let some next := boundedPowMul n entry.base residual entry.exponent | throw .invalidArithmetic
      residual := next
      unresolved := ⟨entry.base, entry.exponent, stop, legacyStop, used, obligation, trace⟩ :: unresolved
  let mut reconstructed := unlisted
  for piece in unresolved do
    let some next := boundedPowMul n piece.base reconstructed piece.exponent | throw .invalidArithmetic
    reconstructed := next
  unless reconstructed == residual do throw .invalidArithmetic
  let mut certified := 1
  for entry in factors do
    let some next := boundedPowMul n entry.prime certified entry.exponent | throw .invalidArithmetic
    certified := next
  unless n % certified == 0 && n / certified == reconstructed do throw .invalidArithmetic
  return ⟨⟨n, factors.reverse, residual⟩, rand, unlisted, unresolved.reverse,
    attempts, events, ecppCalls, completions.reverse⟩

end FactorImport

/-- Import mixed hints at the requested subject, with ECPP disabled unless selected. -/
def importFactors (b : ImportBudget) (n : Nat) (proposal : FactorProposal) (r : Hex.Rand) :
    Except ImportError (ImportResult n) := do
  let c ← FactorImport.prepare b n proposal r
  let value ← FactorImport.accept n c.raw
  return ⟨value, c.rand, c.unlisted, c.unresolved, c.attempts, c.events, c.ecppCalls, c.completions⟩

end Hex.Nat.Mixed
