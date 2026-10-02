/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Search
import HexECPP.Fixture65
import HexECPP.Fixture256
import HexECPP.Fixture512
import HexECPP.ImportConformance
import HexECPP.PariFixtures
import LeanBench

/-!
Mathlib-free compiled ECPP measurements. Conversion, checking, and raw
certificate size have separate registrations; kernel replay is measured in
fresh bridge proof modules.

The complete accepted-certificate and native endpoint registrations use
mode 3. Subject-bit ladders vary witness counts, recursive leaves and search
branches independently; the frozen corpus has both success and exhaustion
at each size. Those ladders therefore do not have a tight scalar wall-time
model, and a published bound on scalar replay does not cover factor search
or terminal construction. Asymptotic detection for these complete endpoints
is replaced by operation-specific regression budgets in `ecpp_audit.py`,
derived before measurement from twice the retained endpoint medians. Parser
and scalar primitives instead use the independently derived ladders below.
`runSize*` remain observation/hash anchors without budgets.
-/

open Hex.ECPP

private instance : Inhabited Cert := ⟨.base (.small 2)⟩

initialize cert65Ref : IO.Ref Cert ← IO.mkRef Fixture65.cert
initialize cert256Ref : IO.Ref Cert ← IO.mkRef Fixture256.cert
initialize cert512Ref : IO.Ref Cert ← IO.mkRef Fixture512.cert
initialize pari65Ref : IO.Ref String ← IO.mkRef ImportConformance.pari65
initialize pari256Ref : IO.Ref String ← IO.mkRef PariFixtures.pari256
initialize pari512Ref : IO.Ref String ← IO.mkRef PariFixtures.pari512

def runCheck65 (_ : Unit) : IO Nat := do
  return if checkAt 18446744073709551629 (← cert65Ref.get) then 1 else 0

def runCheck256 (_ : Unit) : IO Nat := do
  return if check (← cert256Ref.get) then 1 else 0

def runCheck512 (_ : Unit) : IO Nat := do
  return if check (← cert512Ref.get) then 1 else 0

def runConvert65 (_ : Unit) : IO Nat := do
  return match convertText ImportConformance.budget (← pari65Ref.get)
      Fixture65.child with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runConvert256 (_ : Unit) : IO Nat := do
  return match convertText defaultImportBudget (← pari256Ref.get)
      PariFixtures.leaf256 with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runConvert512 (_ : Unit) : IO Nat := do
  return match convertText defaultImportBudget (← pari512Ref.get)
      PariFixtures.leaf512 with
  | .ok c => if check c then 1 else 0
  | .error _ => 0

def runParse512 (_ : Unit) : IO Nat := do
  return match parsePari defaultImportBudget (← pari512Ref.get) with
  | .ok c => c.rows.length
  | .error _ => 0

private partial def certSize : Cert → Nat
  | .base _ => 1
  | .step _ _ _ _ _ _ ws child => 1 + ws.length + certSize child

def runSize65 (_ : Unit) : IO Nat := return certSize (← cert65Ref.get)
def runSize256 (_ : Unit) : IO Nat := return certSize (← cert256Ref.get)
def runSize512 (_ : Unit) : IO Nat := return certSize (← cert512Ref.get)

setup_fixed_benchmark runCheck65 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runCheck256 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runCheck512 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert65 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert256 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runConvert512 where {
  repeats := 3
  expectedHash := some (hash (1 : Nat))
}
setup_fixed_benchmark runParse512 where {
  repeats := 3
  expectedHash := some (hash (17 : Nat))
}
setup_fixed_benchmark runSize65 where { repeats := 3 }
setup_fixed_benchmark runSize256 where { repeats := 3 }
setup_fixed_benchmark runSize512 where { repeats := 3 }

private def terminal : Cert → Hex.Nat.PrimeCert
  | .base c => c
  | .step _ _ _ _ _ _ _ c => terminal c

initialize native128Ref : IO.Ref Nat ← IO.mkRef 177080666831933235355717939809840315427
initialize native256Ref : IO.Ref Nat ← IO.mkRef 69199437377629051939477864552334532767081794053034238723740032946332041487367
initialize nativeHardRef : IO.Ref Nat ← IO.mkRef 96590133568377947488922651108406533027621815589740576200326951544495709460191
initialize nativeCertRef : IO.Ref (Option Cert) ← IO.mkRef none

/-- Warm the fixed replay input outside measurement; ordinary scalar/parser
children need no native search during startup. Failure cannot become a leaf. -/
def nativeCert : IO Cert := do
  if let some c ← nativeCertRef.get then return c
  let n ← native256Ref.get
  let .ok c := (produce n 0).result | throw (IO.userError "native fixture exhausted")
  nativeCertRef.set (some c)
  return c

@[noinline] def runNative128 (_ : Unit) : IO Nat := do
  let n ← native128Ref.get
  return if (produce n 0).result.toOption.any (checkAt n) then 1 else 0

@[noinline] def runNative256 (_ : Unit) : IO Nat := do
  let n ← native256Ref.get
  return if (produce n 0).result.toOption.any (checkAt n) then 1 else 0

/-- Frozen validation-256-7, seed seven: the longest retained native chain.
Its 3.3-second per-call ceiling is twice the retained 1.638-second observation
rounded upward, not the harness timeout. -/
@[noinline] def runNativeHard (_ : Unit) : IO Nat := do
  let n ← nativeHardRef.get
  return if (produce n 7).result.toOption.any (checkAt n) then 1 else 0

@[noinline] def runNativeCheck (_ : Unit) : IO Nat := do
  return if checkAt (← native256Ref.get) (← nativeCert) then 1 else 0

@[noinline] def runNativeConvert (_ : Unit) : IO Nat := do
  let c ← nativeCert
  return if (convertText defaultImportBudget (frozenRows c) (terminal c)).toOption.any
    (checkAt c.subject) then 1 else 0

setup_fixed_benchmark runNative128 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNative256 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeHard where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeCheck where {
  repeats := 5, warmupFirstIter := true, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeConvert where {
  repeats := 5, warmupFirstIter := true, expectedHash := some (hash (1 : Nat)) }

/-- Square root, Cornacchia norm and the complete exceptional twist portfolio,
checked by their integer equations on runtime inputs. -/
private def cmProposals (n d : Nat) : Bool := Id.run do
  let k := if d % 4 == 0 then d / 4 else d
  let a := modSub n 0 k
  let some r := CM.sqrt? n 3 a | return false
  let some (t, v) := CM.norm? n d r | return false
  let curves := CM.portfolio.flatMap (fun inv => CM.curves n inv 3)
  return CM.rootValid n a r && CM.normValid n d t v &&
    (CM.traces d t v).length == (if d == 3 then 6 else 4) &&
    curves.length == 24 && curves.all (fun (a, b) =>
      a < n && b < n && (4 * a * a * a + 27 * b * b) % n != 0)

initialize cm128Ref : IO.Ref Nat ← IO.mkRef 305927751028606010005614597858307057793
initialize exhaustedRef : IO.Ref Nat ← IO.mkRef 86906364443826889462434168665794151905575430136092680752789091262591140309013

@[noinline] def runCM128 (_ : Unit) : IO Nat := do
  return if cmProposals (← cm128Ref.get) 4 then 1 else 0

@[noinline] def runCM256 (_ : Unit) : IO Nat := do
  return if cmProposals (← nativeHardRef.get) 3 then 1 else 0

@[noinline] def runCountedConvert65 (_ : Unit) : IO Nat := do
  return match parsePari defaultImportBudget (← pari65Ref.get) with
  | .error _ => 0
  | .ok input => if (convertCounted defaultImportBudget Hex.Nat.defaultPrimeCertBudget
      (Hex.Rand.ofSeed 1) 200 input).toOption.any (fun result => checkAt input.subject result.1) then 1 else 0

/-- Frozen tuning-256-3 exercises the complete root portfolio without an
accepted point; its resource result is content checked. -/
@[noinline] def runNativeExhaust (_ : Unit) : IO Nat := do
  let n ← exhaustedRef.get
  return match (produce n 3).result with
  | .error e => if e.resource == .portfolio && e.subject == n then 1 else 0
  | .ok _ => 0

setup_fixed_benchmark runCM128 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runCM256 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runCountedConvert65 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeExhaust where { repeats := 5, expectedHash := some (hash (1 : Nat)) }

/-!
# Controlled ECPP input families

Scalar length varies with a fixed small modulus and a nonidentity point of
order thirteen. Parsing varies the number of fixed-width rows, independently
of primality and certificate generation. Setup remains outside timed regions.
-/

namespace Hex.ECPPBench
open Hex.ECPP

private instance : Hashable ImportBudget := ⟨fun b => hash (reprStr b)⟩
private instance : Hashable PariCertificate := ⟨fun c => hash (reprStr c)⟩

def scalarInput (bits : Nat) : Nat × List Nat :=
  let q := 13 * (2 ^ (max 1 bits) - 1)
  let b := { defaultImportBudget with
    maxScalarBits := bits + 4, maxInverseOps := 2 * (bits + 4) }
  let ws := match proposeScalar b 7 0 q (.affine 1 2) with
    | .ok (_, ws) => ws
    | .error _ => []
  (q, ws)

@[noinline] def runReplay (input : Nat × List Nat) : Bool :=
  replayDone 7 0 3 input.1 (.affine 1 2) input.2

@[noinline] def runProposal (input : Nat × List Nat) : Bool :=
  (proposeScalar { defaultImportBudget with
    maxScalarBits := HexArith.bitLength input.1,
    maxInverseOps := 2 * HexArith.bitLength input.1 }
    7 0 input.1 (.affine 1 2)).toOption.any fun (p, ws) =>
      p == .infinity && ws == input.2

-- Derivation: dense scalars 13*(2^k-1) have k+O(1) bits. The SPEC
-- prescribes Nat.testBit, defined in Lean 4.35 as 1 &&& (q >>> i) != 0.
-- For a bignum q, each shift materializes its remaining suffix: summing
-- k-i bits over the k positions costs Theta(k^2 / wordBits). The affine
-- operations modulo seven and witness traversal contribute Theta(k).
-- Thus the compiled large-scalar family is quadratic, while the SPEC's
-- separate O(L) modular-ring-operation count remains linear. These
-- sizes expose the bignum regime.
setup_benchmark runReplay k => k * k with prep := scalarInput where {
  paramFloor := 262144, paramCeiling := 4194304, outerTrials := 3
  targetInnerNanos := 5000000000, maxSecondsPerCall := 1200.0
}

-- Derivation: the identical bit extraction has Theta(k^2 / wordBits)
-- suffix-copy cost. Fixed-modulus extended GCD, witness reversal and
-- comparison contribute only Theta(k). This is a compiled-time claim,
-- not a replacement for the SPEC's modular-operation bound.
setup_benchmark runProposal k => k * k with prep := scalarInput where {
  paramFloor := 262144, paramCeiling := 4194304, outerTrials := 3
  targetInnerNanos := 5000000000, maxSecondsPerCall := 240.0
}

def rowBudget (rows : Nat) : ImportBudget :=
  { defaultImportBudget with maxInputBytes := 64 * rows + 64, maxRows := rows }

def textInput (rows : Nat) : ImportBudget × String :=
  (rowBudget rows, "[" ++ String.intercalate ","
    (List.replicate (max 1 rows) "[7,-5,1,0,[1,2]]") ++ "]")

@[noinline] def runParse (input : ImportBudget × String) : Nat :=
  match parsePari input.1 input.2 with
  | .ok c => c.rows.length
  | .error _ => 0

def parsedInput (rows : Nat) : ImportBudget × PariCertificate :=
  (rowBudget rows, ⟨List.replicate rows ⟨7, -5, 1, 0, ⟨1, 2, 1⟩⟩, 13⟩)

@[noinline] def runPreflight (input : ImportBudget × PariCertificate) : Bool :=
  (preflight input.1 input.2).isOk

-- Derivation: r fixed-width row tokens contain Theta(r) bytes and integers.
-- Digit scanning, JSON parsing, decoding and the terminal-row lookup each
-- traverse them once. Bounded integer arithmetic has constant cost here.
setup_benchmark runParse r => r with prep := textInput where {
  paramFloor := 1, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 8.0
}

-- Derivation: list length, seven fixed-width bit checks per row and original
-- index traversal each cost Theta(r); no endpoint construction is timed.
setup_benchmark runPreflight r => r with prep := parsedInput where {
  paramFloor := 1, paramCeiling := 4096, outerTrials := 3
  targetInnerNanos := 2000000000, maxSecondsPerCall := 8.0
}

end Hex.ECPPBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
