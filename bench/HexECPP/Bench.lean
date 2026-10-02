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
`runParse512` and `runSize*` remain observation/hash anchors without budgets.
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
initialize nativeCertRef : IO.Ref Cert ← IO.mkRef ((produce 69199437377629051939477864552334532767081794053034238723740032946332041487367 0).result.toOption.getD (.base (.small 2)))

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
  return if check (← nativeCertRef.get) then 1 else 0

@[noinline] def runNativeConvert (_ : Unit) : IO Nat := do
  let c ← nativeCertRef.get
  return if (convertText defaultImportBudget (frozenRows c) (terminal c)).toOption.any
    (checkAt c.subject) then 1 else 0

setup_fixed_benchmark runNative128 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNative256 where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeHard where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeCheck where { repeats := 5, expectedHash := some (hash (1 : Nat)) }
setup_fixed_benchmark runNativeConvert where { repeats := 5, expectedHash := some (hash (1 : Nat)) }

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

-- Derivation: dense scalars 13*(2^k-1) have k+O(1) bits and a periodic
-- fixed-width residue schedule. Each bit runs at most two word-size affine
-- additions. Both checked replay and transcript generation therefore take
-- Theta(k) time; this isolates the SPEC's O(L) ring-operation bound.
setup_benchmark runReplay k => k with prep := scalarInput where {
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
}

-- Derivation: the same bit schedule performs Theta(k) extended-GCD calls on
-- fixed operands modulo seven; reversing and comparing the witnesses adds
-- Theta(k) work. Arbitrary subject-bit growth is deliberately held constant.
setup_benchmark runProposal k => k with prep := scalarInput where {
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
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
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
}

-- Derivation: list length, seven fixed-width bit checks per row and original
-- index traversal each cost Theta(r); no endpoint construction is timed.
setup_benchmark runPreflight r => r with prep := parsedInput where {
  paramFloor := 64, paramCeiling := 4096, outerTrials := 3
}

end Hex.ECPPBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
