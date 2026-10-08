/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Mixed.Import
public import HexIntFactor.Mixed.Frozen.Small
public meta import HexIntFactor.Import
public meta import HexIntFactor.Mixed.Cert
public meta import HexIntFactor.Mixed.Frozen.Small
public meta import HexIntFactor.Mixed.Import
public meta import HexPrimality.Cert

public section

/-!
Mixed importer conformance.
Oracle: exact arithmetic and checker acceptance; prime evidence is independently replayed.
Mode: internal
Covered operations: mixed admission, canonicalization, completion allocations and residuals.
Edge cases: signed fields, substitution, malformed transcripts, shared starvation and conversions.
-/

open Hex.Nat.Mixed

private def seed := Hex.Rand.ofSeed 1729
private def noSearch : ImportBudget := { completion := { maxAttempts := 0 } }
private def rejected (err : Hex.Nat.ImportError) (n : Nat) (p : FactorProposal)
    (b : ImportBudget := noSearch) : Bool :=
  match importFactors b n p seed with
  | .error e => e == err
  | _ => false

#guard rejected .zero 0 ⟨0, []⟩
#guard rejected .subjectMismatch 34 ⟨35, []⟩
#guard rejected .subjectMismatch 34 ⟨-34, []⟩
#guard rejected .invalidBase 34 ⟨34, [(0, 1, none)]⟩
#guard rejected .invalidBase 34 ⟨34, [(1, 1, none)]⟩
#guard rejected .invalidBase 34 ⟨34, [(-2, 1, none)]⟩
#guard rejected .invalidExponent 34 ⟨34, [(2, 0, none)]⟩
#guard rejected .invalidExponent 34 ⟨34, [(2, -1, none)]⟩
#guard rejected .invalidExponent 34 ⟨34, [(2, 2^1000, none)]⟩
#guard rejected .invalidArithmetic 34 ⟨34, [(2, 2, none)]⟩
#guard rejected .invalidCertificate 34 ⟨34, [(2, 1, some (.legacy (.small 3)))]⟩
#guard rejected .invalidCertificate 26 ⟨26, [(13, 1, some (.ecpp Frozen.ecpp17))]⟩
#guard rejected .invalidCertificate 4 ⟨4, [(4, 1, some (.ecpp (.base (.small 4))))]⟩
#guard rejected .invalidCertificate 17
  ⟨17, [(17, 1, some (.ecpp (.step 17 2 3 3 6 6 [] (.base (.small 11)))))]⟩
#guard rejected .certificateBounds 17 ⟨17, [(17, 1, some (.ecpp Frozen.ecpp17))]⟩
  { noSearch with maxEcppRows := 0 }
#guard rejected .certificateBounds 17 ⟨17, [(17, 1, some (.ecpp Frozen.ecpp17))]⟩
  { noSearch with maxEcppNodes := 2 }
#guard rejected .certificateBounds 17
  ⟨17, [(17, 1, some (.ecpp (.step 17 2 3 3 6 6 (List.replicate 1025 0) (.base (.small 11)))))]⟩
#guard rejected .certificateBounds 17
  ⟨17, [(17, 1, some (.ecpp (.step 17 (2^512) 3 3 6 6 [] (.base (.small 11)))))]⟩
#guard rejected .bounds (2^4096) ⟨2^4096, []⟩
#guard rejected .bounds (2^512) ⟨2^512, [(2^512, 1, none)]⟩
#guard rejected .bounds 34 ⟨34, [(2, 1, none), (17, 1, none)]⟩ { noSearch with maxEntries := 1 }
#guard rejected .bounds 1 ⟨1, []⟩ { noSearch with ecppBits := some 1024 }
#guard rejected .invalidExponent 4 ⟨4, [(2, 1, none), (2, 1, none)]⟩
  { noSearch with maxExponent := 1 }
#guard rejected .invalidCertificate 4
  ⟨4, [(2, 1, some (.legacy (.small 2))), (2, 1, some (.legacy (.pock 2 [])))]⟩

#guard match importFactors noSearch 578
    ⟨578, [(17, 1, some (.ecpp Frozen.ecpp17)), (2, 1, some (.legacy (.small 2))),
      (17, 1, some (.legacy (.small 17))) ]⟩ seed with
  | .ok r => r.value.raw.factors.map (fun e => (e.prime, e.exponent)) == [(2, 1), (17, 2)] &&
      match (r.value.raw.factors[1]?).map (fun (e : PrimePower) => e.cert) with | some (Evidence.ecpp _) => true | _ => false
  | _ => false
#guard match importFactors {} 12 ⟨12, [(4, 1, none), (3, 1, none)]⟩ seed with
  | .ok r => r.value.raw.residual == 4 && r.unresolved.any (·.stop == .composite) && checkPartial r.value.raw
  | _ => false
#guard match importFactors { noSearch with ecppBits := some 256, maxEcppCalls := 1 }
    6 ⟨6, [(2, 1, none), (3, 1, none)]⟩ seed with
  | .ok r => r.ecppCalls == 1 && r.rand.state == seed.state && r.value.raw.residual == 3 &&
      r.unresolved.any (·.stop == .ecppStarved) && checkPartial r.value.raw
  | _ => false
#guard match importFactors { maxLegacyAttempts := 0 } 6 ⟨6, [(2, 1, none), (3, 1, none)]⟩ seed with
  | .ok r => r.attempts == 0 && r.unresolved.all (·.legacyStop == .legacyStarved) && checkPartial r.value.raw
  | _ => false
#guard match importFactors noSearch 34 ⟨34, [(2, 1, some (.legacy (.small 2)))]⟩ seed with
  | .ok r => r.value.raw.residual == 17 && r.unlisted == 17 && checkPartial r.value.raw
  | _ => false
#guard !checkAt 35 Frozen.small
#guard !checkPartialAt 579 Frozen.partialOverlap
#guard Frozen.small_checked.toLegacy.isNone
#guard Frozen.partialOverlap_checked.toLegacy.isNone

private def legacy : Hex.Nat.CheckedFactorization 12 :=
  ⟨⟨12, [⟨2, .small 2⟩, ⟨1, .small 3⟩]⟩, rfl, by decide +kernel⟩
#guard (CheckedFactorization.ofLegacy legacy).toLegacy.isSome
#guard checkFactorization (Factorization.ofLegacy legacy.raw)
#guard match importFactors noSearch 1 ⟨1, []⟩ seed with | .ok r => r.value.raw.residual == 1 | _ => false

-- Caller limits may tighten, but cannot widen, the supported structural ceilings.
#guard rejected .bounds (2^65) ⟨2^65, List.replicate 65 (2, 1, none)⟩
  { noSearch with maxEntries := 1000 }

private def deepCert : Nat → Hex.Nat.PrimeCert
  | 0 => .small 2
  | k + 1 => .pock 2 [(1, 1, deepCert k)]

#guard !FactorImport.certificateFits { maxCertDepth := 1000, maxCertNodes := 100000 }
  (.legacy (deepCert 65))

#guard match importFactors { noSearch with ecppBits := some 256, maxEcppCalls := 3 }
    30 ⟨30, [(2, 1, none), (3, 1, none), (5, 1, none)]⟩ seed with
  | .ok r => r.ecppCalls == 2 && r.unresolved.any (·.stop == .ecppStarved) && checkPartial r.value.raw
  | _ => false
#guard match importFactors { noSearch with ecppBits := some 256, maxEcppCalls := 0 }
    2 ⟨2, [(2, 1, none)]⟩ seed with
  | .ok r => r.ecppCalls == 0 && r.completions.all (·.ecppStop == .ecppSkipped) &&
      r.unresolved.all (·.stop == .ecppSkipped)
  | _ => false
#guard match importFactors { ecppBits := some 256 } 4 ⟨4, [(4, 1, none)]⟩ seed with
  | .ok r => r.ecppCalls == 0 && r.completions.all (·.ecppStop == .ecppSkipped) &&
      r.unresolved.all (·.stop == .composite)
  | _ => false
