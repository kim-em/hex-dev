/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Pari

public meta import HexIntFactor.Pari

public section

/-!
Optional producer conformance.
Oracle: pure parser checks and checked native fallback; optional real GP is
exercised by check_intfactor_pari.py.
Mode: internal
Covered operations: parse, factor and fallback.
Edge cases: framing, grammar, bounds, backend absence, bounded native exhaustion,
preserved partial progress and cancellation before work.
-/

open Hex.Nat Hex.Nat.Pari

private def frame (n : Nat) (entries : String) :=
  s!"HEX_FACTOR_BEGIN\n{n}\n{entries}HEX_FACTOR_END\n"

#guard (parse {} 12 (frame 12 "2 2\n3 1\n")).isOk
#guard (parse {} 1 (frame 1 "")).isOk
#guard match parse {} 12 (frame 18 "2 2\n3 1\n") with
  | .error .subjectMismatch => true | _ => false
#guard match parse {} 12 "HEX_FACTOR_BEGIN\n12\n2 2\n" with
  | .error .framing => true | _ => false
#guard !(parse {} 12 (frame 12 "2 2\n" ++ "extra\n")).isOk
#guard !(parse {} 12 (frame 12 "2 2\n" ++ "\n")).isOk
#guard !(parse {} 12 (frame 12 " 2 2\n")).isOk
#guard !(parse {} 12 (frame 12 "2  2\n")).isOk
#guard !(parse {} 12 (frame 12 "2 -2\n")).isOk
#guard !(parse {} 12 (frame 12 "2 0\n")).isOk
#guard !(parse {} 12 (frame 12 "2 257\n")).isOk
#guard !(parse {} 12 (frame 12 "2 2 prime\n")).isOk
#guard !(parse {} 12 (frame 12 "[2,2]\n")).isOk
#guard !(parse { maxDigits := 1 } 12 (frame 12 "")).isOk
#guard !(parse { maxBits := 3 } 12 (frame 12 "")).isOk
#guard !(parse { maxEntries := 0 } 12 (frame 12 "2 2\n")).isOk
#guard !(parse { maxBytes := 8 } 12 (frame 12 "")).isOk
#guard (parse {} 12 (frame 12 "02 02\n")).isOk

private def checks : IO Unit := do
  let missing ← factor 12 (Hex.Rand.ofSeed 12) (executable := "/hex-missing-gp")
  unless missing.value.any (fun v => v.raw.residual == 1 && checkPartial v.raw) &&
      missing.diagnostics.any (fun d => match d with
        | .producer (.process .missing) => true | _ => false) do
    throw <| IO.userError "missing-backend fallback failed"
  let bounded ← factor 1000036000099 (Hex.Rand.ofSeed 12)
    (native := { factorFuel := 0 }) (executable := "/hex-missing-gp")
  unless bounded.value.any (fun v => v.raw.residual == 1000036000099 && checkPartial v.raw) &&
      bounded.nativeFailures.any (fun f => f.2.stop == .incomplete) do
    throw <| IO.userError "native exhaustion or backend diagnostic was lost"
  let .ok partialData := importFactors {} 12 ⟨12, [(2, 1, none)]⟩ (Hex.Rand.ofSeed 12)
    | throw <| IO.userError "could not prepare partial data"
  let joined ← fallback {} {} 12 partialData
  unless joined.value.any (fun v => v.raw.residual == 1 &&
      v.raw.factors.map (fun e => (e.prime, e.exponent)) == [(2, 2), (3, 1)]) do
    throw <| IO.userError "overlapping powers were not merged"
  let .ok composite := importFactors {} 144 ⟨144, [(12, 2, none)]⟩ (Hex.Rand.ofSeed 144)
    | throw <| IO.userError "could not prepare composite proposal"
  let split ← fallback {} {} 144 composite
  unless split.value.any (fun v => v.raw.residual == 1 &&
      v.raw.factors.map (fun e => (e.prime, e.exponent)) == [(2, 4), (3, 2)]) do
    throw <| IO.userError "composite multiplicities were not scaled"
  let .ok skipped := importFactors { completion := { maxAttempts := 0 } }
      1000036000099 ⟨1000036000099, [(1000003, 1, none), (1000033, 1, none)]⟩
      (Hex.Rand.ofSeed 1729) | throw <| IO.userError "skipped preparation failed"
  let resumed ← fallback {} {} 1000036000099 skipped
  unless resumed.value.any (fun v => v.raw.residual == 1 && checkPartial v.raw) do
    throw <| IO.userError "skipped completion did not use its separate native allocation"
  let rejected : FactorFailure := {
    stop := .rejected, attempts := 7, rand := Hex.Rand.ofSeed 99
    culprit := some ⟨6, [⟨2, .small 3⟩], 1⟩ }
  let preserved := mergeNative {} 12 6 1 partialData.value (.error rejected)
  unless preserved.value.any (fun v => v.raw.residual == partialData.value.raw.residual) &&
      preserved.rand.state == rejected.rand.state && preserved.nativeFailures.length == 1 &&
      preserved.diagnostics.any (fun d => match d with
        | .native 6 .rejected => true | _ => false) do
    throw <| IO.userError "native rejection erased checked data or diagnostics"
  let .ok full := importFactors {} 3000009
      ⟨3000009, [(3, 1, none), (1000003, 1, none)]⟩ (Hex.Rand.ofSeed 3000009)
      | throw <| IO.userError "mixed certificate preparation failed"
  let .complete full := full.value | throw <| IO.userError "mixed certificates incomplete"
  let .ok empty := importFactors {} 3000009 ⟨3000009, []⟩ (Hex.Rand.ofSeed 3000009)
      | throw <| IO.userError "empty preparation failed"
  let boundedCerts := mergeNative { maxCertNodes := 1 } 3000009 3000009 1 empty.value
    (.ok { factorization := full, attempts := 4, rand := Hex.Rand.ofSeed 101 })
  unless boundedCerts.value.any (fun v => v.raw.residual == 1000003 &&
      v.raw.factors.map (·.prime) == [3] && checkPartial v.raw) &&
      boundedCerts.diagnostics.any (fun d => match d with
        | .mergeError _ .certificateBounds => true | _ => false) do
    throw <| IO.userError "certificate limit discarded admissible native progress"
  let token ← IO.CancelToken.new
  token.set
  let cancelled ← factor 12 (Hex.Rand.ofSeed 12)
    (executable := "/hex-missing-gp") (cancel := some token)
  unless cancelled.nativeFailures.isEmpty && cancelled.diagnostics.any (fun d => match d with
      | .cancelled => true | _ => false) do throw <| IO.userError "cancellation started native work"

#eval checks
