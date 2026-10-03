/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Import

/-!
Pure importer conformance.
Oracle: exact products and checker acceptance are independently asserted below;
external primality labels do not occur in the proposal schema.
Mode: internal
Covered operations: importFactors, bounded syntax inspection, canonicalization,
complete/partial acceptance and finite native completion.
Edge cases: zero/one, signed fields, omissions, duplicates/order, excessive
multiplicities, composite bases, supplied evidence and allocation exhaustion.
-/

open Hex.Nat

private def seed := Hex.Rand.ofSeed 1729
private def noSearch : ImportBudget :=
  { completion := { maxAttempts := 0 } }

private def complete (n : Nat) (entries : List (Int × Int × Option PrimeCert)) : Bool :=
  match importFactors {} n ⟨n, entries⟩ seed with
  | .ok r => match r.value with
      | .complete F => checkFactorization F.raw && F.raw.subject == n
      | _ => false
  | _ => false

private def rejects (kind : ImportError) (n : Nat) (p : FactorProposal)
    (b : ImportBudget := {}) : Bool :=
  match importFactors b n p seed with
  | .error err => err == kind
  | _ => false

#guard complete 1 []
#guard rejects .zero 0 ⟨0, []⟩
#guard rejects .subjectMismatch 12 ⟨18, [(2, 1, none)]⟩
#guard rejects .subjectMismatch 12 ⟨-12, []⟩
#guard rejects .invalidBase 12 ⟨12, [(0, 1, none)]⟩
#guard rejects .invalidBase 12 ⟨12, [(1, 1, none)]⟩
#guard rejects .invalidBase 12 ⟨12, [(-2, 1, none)]⟩
#guard rejects .invalidExponent 12 ⟨12, [(2, 0, none)]⟩
#guard rejects .invalidExponent 12 ⟨12, [(2, -1, none)]⟩
#guard rejects .invalidExponent 12 ⟨12, [(2, 2^1000, none)]⟩
#guard rejects .invalidArithmetic 12 ⟨12, [(2, 3, none)]⟩
#guard rejects .invalidArithmetic 12 ⟨12, [(5, 1, none)]⟩
#guard rejects .invalidArithmetic 1 ⟨1, [(2, 1, none)]⟩
#guard rejects .bounds (2^256) ⟨2^256, []⟩
#guard rejects .bounds 12 ⟨12, [(2^256, 1, none)]⟩
#guard rejects .bounds 12 ⟨12, [(2, 1, none), (3, 1, none)]⟩ { maxEntries := 1 }
#guard rejects .invalidExponent 4 ⟨4, [(2, 1, none), (2, 1, none)]⟩ { maxExponent := 1 }
#guard complete 72 [(3, 1, none), (2, 1, none), (3, 1, none), (2, 2, none)]
#guard complete 1000003 [(1000003, 1, none)]
#guard rejects .invalidCertificate 12 ⟨12, [(2, 2, some (.small 3))]⟩
#guard rejects .invalidCertificate 4 ⟨4, [(4, 1, some (.small 4))]⟩
#guard rejects .invalidCertificate 4
  ⟨4, [(2, 1, some (.small 2)), (2, 1, some (.pock 2 []))]⟩
#guard rejects .certificateBounds 2 ⟨2, [(2, 1, some (.small 2))]⟩ { maxCertNodes := 0 }
#guard rejects .certificateBounds 2
  ⟨2, [(2, 1, some (.pock 2 [(3, 2^1000, .small 2)]))]⟩
#guard rejects .certificateBounds 2
  ⟨2, [(2, 1, some (.pock 2 [(3, 0, .small 2)]))]⟩ { maxCertDepth := 1 }
#guard rejects .certificateBounds 2
  ⟨2, [(2, 1, some (.pock3Sieve 2 0 0 0 65 []))]⟩

#guard match importFactors {} 72 ⟨72, [(3, 2, none), (2, 3, none)]⟩ seed with
  | .ok r => r.value.raw.factors.map (fun e => (e.prime, e.exponent)) == [(2, 3), (3, 2)]
  | _ => false
#guard match importFactors {} 12 ⟨12, [(2, 2, none)]⟩ seed with
  | .ok r => r.value.raw.residual == 3 && r.unlisted == 3 && checkPartial r.value.raw
  | _ => false
#guard match importFactors {} 12 ⟨12, [(4, 1, none), (3, 1, none)]⟩ seed with
  | .ok r => r.value.raw.residual == 4 && r.unresolved.any (·.stop == .composite) &&
      r.value.raw.factors.map (·.prime) == [3] && checkPartial r.value.raw
  | _ => false
#guard match importFactors noSearch 12 ⟨12, [(2, 2, some (.small 2)), (3, 1, none)]⟩ seed with
  | .ok r => r.value.raw.residual == 3 && r.unresolved.any (·.stop == .skipped) &&
      r.attempts == 0 && r.rand.state == seed.state && checkPartial r.value.raw
  | _ => false
#guard match importFactors noSearch 12 ⟨12, []⟩ seed with
  | .ok r => r.value.raw.residual == 12 && r.unlisted == 12 && r.unresolved.isEmpty
  | _ => false
#guard match importFactors noSearch 2 ⟨2, [(2, 1, none)]⟩ seed with
  | .ok r => r.value.raw.residual == 2 && r.unresolved.any (·.stop == .skipped)
  | _ => false

example : checkFactorization ⟨72, [⟨3, .small 2⟩, ⟨2, .small 3⟩]⟩ = true := by decide +kernel
example : (2^3 * 3^2 : Nat) = 72 := by decide +kernel
example : checkPartial ⟨12, [⟨2, .small 2⟩], 3⟩ = true := by decide +kernel

-- Distinct accepted certificates for a repeated base preserve proposal order.
#guard checkPrime (.pock 3 [(2, 0, .small 2)])
#guard match importFactors noSearch 9
    ⟨9, [(3, 1, some (.pock 3 [(2, 0, .small 2)])), (3, 1, some (.small 3))]⟩ seed with
  | .ok r => match r.value.raw.factors.head? with
      | some ⟨2, .pock 3 [(2, 0, .small 2)]⟩ => true
      | _ => false
  | _ => false
#guard match importFactors { maxCertNodes := 1 } 1000003
    ⟨1000003, [(1000003, 1, none)]⟩ seed with
  | .ok r => r.value.raw.residual == 1000003 &&
      r.unresolved.any (·.stop == .certificateBounds) && checkPartial r.value.raw
  | _ => false
