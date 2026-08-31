/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexConway
import LeanBench

/-!
Benchmark registrations for `hex-conway`.

This Phase 4 slice covers the two implemented tiers: Tier 1 committed-table
surfaces (imported Luebeck lookup and fixed irreducibility verification of
selected entries) and Tier 2 divisor compatibility. It does not benchmark
Tier 3 on-demand Conway search, which is unimplemented. Tier 2 primitivity is
implemented but is not a separate advertised input family in this Phase 4
slice.

Scientific registrations:

* `runLuebeckConwayPolynomialLookupChecksum`: look up every committed Luebeck
  table key in the current Tier 1 slice, using the one-based table ordinal as
  the benchmark parameter.
* `runConwayPolySupported_2_1Checksum`: fixed canonical measurement for the
  `SupportedEntry` recovery path, taken at `C(2, 1)`. Recovery itself reads the
  stored polynomial out of the witness in constant time, but the target also
  checksums the result, and that traversal is linear in the degree, so this
  measurement stands for `C(2, 1)` rather than for the committed table.
* `runTier1Irreducibility_13_6Checksum`: mode-3 Rabin irreducibility
  verification for the hardest committed Tier 1 entry, `C(13, 6)`.
* `runTier2Compat_13_1_6Checksum`: mode-3 divisor compatibility for the
  deepest largest-prime committed pair, `C(13, 1)` inside `C(13, 6)`.

The remaining fixed Tier 1 and Tier 2 registrations are correctness/hash
anchors for selected entries and make no complexity claim. The headline report
records the failed controlled parameter ladders that rule out stronger modes
for the two performance-evidence registrations.

Fixed registrations are wrapped as `Unit → IO α` so the harness exercises
them per-call rather than measuring a closed compile-time-folded constant
load. Each polynomial input is threaded through an `IO.Ref` to defeat the
same folding on the workload itself, and the per-bench `expectedHash`
catches silent value regressions that the cross-repeat agreement check
cannot see (e.g. a stable but wrong `Bool`).
-/

namespace Hex.ConwayBench

/-- One committed Luebeck table key. -/
structure EntryKey where
  p : Nat
  n : Nat
  deriving Repr, BEq, Hashable

/-- The committed Tier 1 Luebeck table keys, in source-table order. -/
def committedEntryKeys : Array EntryKey := #[
  ⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 3⟩, ⟨2, 4⟩, ⟨2, 5⟩, ⟨2, 6⟩, ⟨2, 7⟩, ⟨2, 8⟩,
  ⟨3, 1⟩, ⟨3, 2⟩, ⟨3, 3⟩, ⟨3, 4⟩, ⟨3, 5⟩, ⟨3, 6⟩,
  ⟨5, 1⟩, ⟨5, 2⟩, ⟨5, 3⟩, ⟨5, 4⟩, ⟨5, 5⟩, ⟨5, 6⟩,
  ⟨7, 1⟩, ⟨7, 2⟩, ⟨7, 3⟩, ⟨7, 4⟩, ⟨7, 5⟩, ⟨7, 6⟩,
  ⟨11, 1⟩, ⟨11, 2⟩, ⟨11, 3⟩, ⟨11, 4⟩, ⟨11, 5⟩, ⟨11, 6⟩,
  ⟨13, 1⟩, ⟨13, 2⟩, ⟨13, 3⟩, ⟨13, 4⟩, ⟨13, 5⟩, ⟨13, 6⟩
]

/-- One-based ordinal lookup for the committed table-key domain. -/
def committedEntryKeyAt (ordinal : Nat) : EntryKey :=
  committedEntryKeys.getD (ordinal - 1) ⟨2, 1⟩

/-- Stable checksum for a Conway polynomial over a fixed prime field. -/
def checksumPoly {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff.toNat)) 0

/-- Stable checksum for an optional Conway-polynomial lookup result. -/
def checksumLookup {p : Nat} [ZMod64.Bounds p] (result : Option (FpPoly p)) : UInt64 :=
  match result with
  | none => 0
  | some f => mixHash 1 (checksumPoly f)

/-- Benchmark target: committed Tier 1 Luebeck lookup by table ordinal. -/
def runLuebeckConwayPolynomialLookupChecksum (ordinal : Nat) : UInt64 :=
  match committedEntryKeyAt ordinal with
  | ⟨2, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 2 n)
  | ⟨3, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 3 n)
  | ⟨5, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 5 n)
  | ⟨7, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 7 n)
  | ⟨11, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 11 n)
  | ⟨13, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 13 n)
  | _ => 0

/-- `Nonempty` witness for the `IO.Ref` declaration below. The
`SupportedEntry` field is a dependent record, so `Nonempty` does not
auto-derive — we hand it the canonical witness. -/
private instance : Nonempty (Conway.SupportedEntry 2 1) :=
  ⟨Conway.supportedEntry_2_1⟩

/-- Mutable cell used to defeat compile-time folding of the closed
`SupportedEntry` literal in the canonical Tier 1 fixed bench. -/
private initialize supportedEntry_2_1Ref :
    IO.Ref (Conway.SupportedEntry 2 1) ←
  IO.mkRef Conway.supportedEntry_2_1

/-- Fixed canonical target: recover the currently exported supported entry. -/
def runConwayPolySupported_2_1Checksum : Unit → IO UInt64 := fun () => do
  let entry ← supportedEntry_2_1Ref.get
  return checksumPoly (Conway.conwayPoly 2 1 entry)

/-- A monic polynomial over `ZMod64 q` paired with its monicity proof.
Used to thread a Tier 1 irreducibility input through an `IO.Ref` while
keeping `Berlekamp.rabinTest`'s dependent monicity argument satisfied. -/
private structure MonicPoly (q : Nat) [ZMod64.Bounds q] where
  poly : FpPoly q
  monic : DensePoly.Monic poly

/- `Nonempty` witnesses for the `IO.Ref (MonicPoly q)` declarations below.
The dependent monicity proof blocks auto-derivation, so we supply a
canonical witness per prime — the same committed Tier 1 entry the ref
will hold at runtime. -/
private instance : Nonempty (MonicPoly 2) :=
  ⟨⟨Conway.luebeckConwayPolynomial_2_1,
    Conway.luebeckConwayPolynomial_2_1_monic⟩⟩
private instance : Nonempty (MonicPoly 3) :=
  ⟨⟨Conway.luebeckConwayPolynomial_3_6,
    Conway.luebeckConwayPolynomial_3_6_monic⟩⟩
private instance : Nonempty (MonicPoly 5) :=
  ⟨⟨Conway.luebeckConwayPolynomial_5_6,
    Conway.luebeckConwayPolynomial_5_6_monic⟩⟩
private instance : Nonempty (MonicPoly 7) :=
  ⟨⟨Conway.luebeckConwayPolynomial_7_6,
    Conway.luebeckConwayPolynomial_7_6_monic⟩⟩
private instance : Nonempty (MonicPoly 11) :=
  ⟨⟨Conway.luebeckConwayPolynomial_11_6,
    Conway.luebeckConwayPolynomial_11_6_monic⟩⟩
private instance : Nonempty (MonicPoly 13) :=
  ⟨⟨Conway.luebeckConwayPolynomial_13_6,
    Conway.luebeckConwayPolynomial_13_6_monic⟩⟩

private initialize tier1_2_1Ref : IO.Ref (MonicPoly 2) ←
  IO.mkRef ⟨Conway.luebeckConwayPolynomial_2_1,
            Conway.luebeckConwayPolynomial_2_1_monic⟩
private initialize tier1_2_6Ref : IO.Ref (MonicPoly 2) ←
  IO.mkRef ⟨Conway.luebeckConwayPolynomial_2_6,
            Conway.luebeckConwayPolynomial_2_6_monic⟩
private initialize tier1_3_6Ref : IO.Ref (MonicPoly 3) ←
  IO.mkRef ⟨Conway.luebeckConwayPolynomial_3_6,
            Conway.luebeckConwayPolynomial_3_6_monic⟩
private initialize tier1_5_6Ref : IO.Ref (MonicPoly 5) ←
  IO.mkRef ⟨Conway.luebeckConwayPolynomial_5_6,
            Conway.luebeckConwayPolynomial_5_6_monic⟩
private initialize tier1_7_6Ref : IO.Ref (MonicPoly 7) ←
  IO.mkRef ⟨Conway.luebeckConwayPolynomial_7_6,
            Conway.luebeckConwayPolynomial_7_6_monic⟩
private initialize tier1_11_6Ref : IO.Ref (MonicPoly 11) ←
  IO.mkRef ⟨Conway.luebeckConwayPolynomial_11_6,
            Conway.luebeckConwayPolynomial_11_6_monic⟩
private initialize tier1_13_6Ref : IO.Ref (MonicPoly 13) ←
  IO.mkRef ⟨Conway.luebeckConwayPolynomial_13_6,
            Conway.luebeckConwayPolynomial_13_6_monic⟩

/- `maxSecondsPerCall` bounds the whole child process, including startup. A
scientific mode-3 run sets `HEXCONWAY_ENFORCE_BUDGETS=1`; only then does this
wrapper time the operation body and throw on a ceiling violation. Throwing
checks every auto-tuned invocation, including iterations whose result the
harness discards. The CI `verify` smoke gate leaves the variable unset and
therefore does not assert timing on a noisy hosted runner. -/
def withBudget (name : String) (ceilingNanos : Nat) (work : IO Bool) : IO Bool := do
  if (← IO.getEnv "HEXCONWAY_ENFORCE_BUDGETS") == some "1" then
    let start ← IO.monoNanosNow
    let value ← work
    let elapsed := (← IO.monoNanosNow) - start
    if ceilingNanos < elapsed then
      throw <| IO.userError
        s!"{name} exceeded its {ceilingNanos} ns operation budget: {elapsed} ns"
    return value
  else
    work

/-- Benchmark target: Tier 1 irreducibility check for imported `C(2, 1)`. -/
def runTier1Irreducibility_2_1Checksum : Unit → IO Bool := fun () => do
  let mp ← tier1_2_1Ref.get
  return Berlekamp.rabinTest mp.poly mp.monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(2, 6)`. -/
def runTier1Irreducibility_2_6Checksum : Unit → IO Bool := fun () => do
  let mp ← tier1_2_6Ref.get
  return Berlekamp.rabinTest mp.poly mp.monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(3, 6)`. -/
def runTier1Irreducibility_3_6Checksum : Unit → IO Bool := fun () => do
  let mp ← tier1_3_6Ref.get
  return Berlekamp.rabinTest mp.poly mp.monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(5, 6)`. -/
def runTier1Irreducibility_5_6Checksum : Unit → IO Bool := fun () => do
  let mp ← tier1_5_6Ref.get
  return Berlekamp.rabinTest mp.poly mp.monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(7, 6)`. -/
def runTier1Irreducibility_7_6Checksum : Unit → IO Bool := fun () => do
  let mp ← tier1_7_6Ref.get
  return Berlekamp.rabinTest mp.poly mp.monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(11, 6)`. -/
def runTier1Irreducibility_11_6Checksum : Unit → IO Bool := fun () => do
  let mp ← tier1_11_6Ref.get
  return Berlekamp.rabinTest mp.poly mp.monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(13, 6)`. -/
def runTier1Irreducibility_13_6Checksum : Unit → IO Bool := fun () => do
  withBudget "Tier 1 C(13, 6) irreducibility" 2_000_000 do
    let mp ← tier1_13_6Ref.get
    return Berlekamp.rabinTest mp.poly mp.monic

/-- One committed Tier 2 divisor pair, carried through an `IO.Ref` so the
workload is not constant-folded. -/
structure CompatPair (p : Nat) [ZMod64.Bounds p] where
  /-- The smaller modulus `C(p, m)`. -/
  small : FpPoly p
  /-- The larger modulus `C(p, n)`. -/
  large : FpPoly p
  /-- Monicity of the larger modulus, which the norm construction needs. -/
  largeMonic : DensePoly.Monic large
  /-- The subfield degree `m`. -/
  m : Nat
  /-- The number of Frobenius factors, `n / m`. -/
  k : Nat

/- `Nonempty` witnesses for the `IO.Ref (CompatPair p)` declarations, for the
same reason as `MonicPoly`: the dependent monicity field blocks derivation. -/
private instance : Nonempty (CompatPair 2) :=
  ⟨⟨Conway.conwayPoly 2 3 Conway.supportedEntry_2_3,
    Conway.conwayPoly 2 6 Conway.supportedEntry_2_6,
    Conway.conwayPoly_monic 2 6 Conway.supportedEntry_2_6, 3, 2⟩⟩
private instance : Nonempty (CompatPair 13) :=
  ⟨⟨Conway.conwayPoly 13 1 Conway.supportedEntry_13_1,
    Conway.conwayPoly 13 6 Conway.supportedEntry_13_6,
    Conway.conwayPoly_monic 13 6 Conway.supportedEntry_13_6, 1, 6⟩⟩

private initialize compat_2_3_6Ref : IO.Ref (CompatPair 2) ←
  IO.mkRef ⟨Conway.conwayPoly 2 3 Conway.supportedEntry_2_3,
            Conway.conwayPoly 2 6 Conway.supportedEntry_2_6,
            Conway.conwayPoly_monic 2 6 Conway.supportedEntry_2_6, 3, 2⟩
private initialize compat_13_1_6Ref : IO.Ref (CompatPair 13) ←
  IO.mkRef ⟨Conway.conwayPoly 13 1 Conway.supportedEntry_13_1,
            Conway.conwayPoly 13 6 Conway.supportedEntry_13_6,
            Conway.conwayPoly_monic 13 6 Conway.supportedEntry_13_6, 1, 6⟩
private initialize compat_2_4_8Ref : IO.Ref (CompatPair 2) ←
  IO.mkRef ⟨Conway.conwayPoly 2 4 Conway.supportedEntry_2_4,
            Conway.conwayPoly 2 8 Conway.supportedEntry_2_8,
            Conway.conwayPoly_monic 2 8 Conway.supportedEntry_2_8, 4, 2⟩

/-- Benchmark target: Tier 2 compatibility for the binary mid-degree pair
`C(2, 3)` inside `C(2, 6)`. -/
def runTier2Compat_2_3_6Checksum : Unit → IO Bool := fun () => do
  let cp ← compat_2_3_6Ref.get
  return Conway.compatCheck cp.small cp.large cp.largeMonic cp.m cp.k

/-- Benchmark target: Tier 2 compatibility for the largest odd-prime pair,
`C(13, 1)` inside `C(13, 6)`. This is the deepest Frobenius chain in the
committed table: six factors. -/
def runTier2Compat_13_1_6Checksum : Unit → IO Bool := fun () => do
  withBudget "Tier 2 C(13, 1) in C(13, 6) compatibility" 1_000_000 do
    let cp ← compat_13_1_6Ref.get
    return Conway.compatCheck cp.small cp.large cp.largeMonic cp.m cp.k

/-- Benchmark target: Tier 2 compatibility for the deepest binary pair,
`C(2, 4)` inside `C(2, 8)`. -/
def runTier2Compat_2_4_8Checksum : Unit → IO Bool := fun () => do
  let cp ← compat_2_4_8Ref.get
  return Conway.compatCheck cp.small cp.large cp.largeMonic cp.m cp.k

namespace Tier1

/-- The committed binary column, bundled with the monicity witnesses consumed
by Rabin's test. Entry `n - 1` is `C(2, n)` for `n = 1..8`. -/
private def gf2Entries : Array (MonicPoly 2) := #[
  ⟨Conway.luebeckConwayPolynomial_2_1, Conway.luebeckConwayPolynomial_2_1_monic⟩,
  ⟨Conway.luebeckConwayPolynomial_2_2, Conway.luebeckConwayPolynomial_2_2_monic⟩,
  ⟨Conway.luebeckConwayPolynomial_2_3, Conway.luebeckConwayPolynomial_2_3_monic⟩,
  ⟨Conway.luebeckConwayPolynomial_2_4, Conway.luebeckConwayPolynomial_2_4_monic⟩,
  ⟨Conway.luebeckConwayPolynomial_2_5, Conway.luebeckConwayPolynomial_2_5_monic⟩,
  ⟨Conway.luebeckConwayPolynomial_2_6, Conway.luebeckConwayPolynomial_2_6_monic⟩,
  ⟨Conway.luebeckConwayPolynomial_2_7, Conway.luebeckConwayPolynomial_2_7_monic⟩,
  ⟨Conway.luebeckConwayPolynomial_2_8, Conway.luebeckConwayPolynomial_2_8_monic⟩
]

/-- Rabin irreducibility verification for committed `C(2, n)`. -/
def runIrreducibilityGF2 (n : Nat) : Bool :=
  let default : MonicPoly 2 :=
    ⟨Conway.luebeckConwayPolynomial_2_1, Conway.luebeckConwayPolynomial_2_1_monic⟩
  let mp := gf2Entries.getD (n - 1) default
  Berlekamp.rabinTest mp.poly mp.monic

end Tier1

namespace Tier2

/-- Compatibility inputs for `C(2, 1)` inside `C(2, n)`. Entry `n - 2`
corresponds to `n = 2..8`, and its Frobenius-factor count is `n`. -/
private def gf2Pairs : Array (CompatPair 2) := #[
  ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
    Conway.conwayPoly 2 2 Conway.supportedEntry_2_2,
    Conway.conwayPoly_monic 2 2 Conway.supportedEntry_2_2, 1, 2⟩,
  ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
    Conway.conwayPoly 2 3 Conway.supportedEntry_2_3,
    Conway.conwayPoly_monic 2 3 Conway.supportedEntry_2_3, 1, 3⟩,
  ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
    Conway.conwayPoly 2 4 Conway.supportedEntry_2_4,
    Conway.conwayPoly_monic 2 4 Conway.supportedEntry_2_4, 1, 4⟩,
  ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
    Conway.conwayPoly 2 5 Conway.supportedEntry_2_5,
    Conway.conwayPoly_monic 2 5 Conway.supportedEntry_2_5, 1, 5⟩,
  ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
    Conway.conwayPoly 2 6 Conway.supportedEntry_2_6,
    Conway.conwayPoly_monic 2 6 Conway.supportedEntry_2_6, 1, 6⟩,
  ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
    Conway.conwayPoly 2 7 Conway.supportedEntry_2_7,
    Conway.conwayPoly_monic 2 7 Conway.supportedEntry_2_7, 1, 7⟩,
  ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
    Conway.conwayPoly 2 8 Conway.supportedEntry_2_8,
    Conway.conwayPoly_monic 2 8 Conway.supportedEntry_2_8, 1, 8⟩
]

/-- Check that `C(2, 1)` is compatible with committed `C(2, n)`. -/
def runCompatibilityGF2 (n : Nat) : Bool :=
  let default : CompatPair 2 :=
    ⟨Conway.conwayPoly 2 1 Conway.supportedEntry_2_1,
      Conway.conwayPoly 2 2 Conway.supportedEntry_2_2,
      Conway.conwayPoly_monic 2 2 Conway.supportedEntry_2_2, 1, 2⟩
  let cp := gf2Pairs.getD (n - 2) default
  Conway.compatCheck cp.small cp.large cp.largeMonic cp.m cp.k

end Tier2

/-- Degree of the committed entry selected by a one-based table ordinal. -/
def tier1LookupDegree (ordinal : Nat) : Nat :=
  if ordinal ≤ 8 then ordinal
  else if ordinal ≤ 14 then ordinal - 8
  else if ordinal ≤ 20 then ordinal - 14
  else if ordinal ≤ 26 then ordinal - 20
  else if ordinal ≤ 32 then ordinal - 26
  else ordinal - 32

/-- Dispatch plus materialization and checksum cost for a committed lookup. -/
def tier1LookupComplexity (ordinal : Nat) : Nat :=
  tier1LookupDegree ordinal + 2

/- Complexity derivation: Tier 1 is a committed finite database lookup keyed by
`(p, n)`. The benchmark parameter is the one-based ordinal into the committed
key set. A lookup performs one finite-key dispatch, materializes `n + 1`
coefficients, and `checksumPoly` walks all `n + 1` coefficients. The linear
walk dominates and the dispatch contributes a fixed term, so the registration
uses the two-sided affine model `n + 2`, with `n` recovered from the generated
table's six degree columns. -/
setup_benchmark runLuebeckConwayPolynomialLookupChecksum ordinal =>
    tier1LookupComplexity ordinal
  where {
    paramFloor := 1
    paramCeiling := 38
    paramSchedule := .custom #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
      13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Audit-only mode-1 attempt. At fixed `p = 2`, Rabin's test computes a
degree-`n` Frobenius remainder and gcd checks. Dense modular polynomial
arithmetic gives the independently derived cubic degree model already used by
HexBerlekamp. This registration is removed after the clean audit run because
the committed `n = 1..8` transition range is too short for a stable verdict. -/
setup_benchmark Tier1.runIrreducibilityGF2 n => n * n * n where {
  paramFloor := 1
  paramCeiling := 8
  paramSchedule := .custom #[1, 2, 3, 4, 5, 6, 7, 8]
  maxSecondsPerCall := 2.0
  targetInnerNanos := 100000000
  signalFloorMultiplier := 1.0
  slopeTolerance := 0.35
}

/- Audit-only mode-1 attempt. For `m = 1`, `k = n`, and fixed `p = 2`,
`normX` performs `n` Frobenius steps and `n` dense modular products, followed
by composition of the fixed linear smaller polynomial. Each modular operation
is quadratic in the degree of the larger modulus, so the independently
derived model is cubic in `n`. This registration is removed after the clean
audit run because the committed `n = 2..8` transition range is too short for
a stable verdict. -/
setup_benchmark Tier2.runCompatibilityGF2 n => n * n * n where {
  paramFloor := 2
  paramCeiling := 8
  paramSchedule := .custom #[2, 3, 4, 5, 6, 7, 8]
  maxSecondsPerCall := 2.0
  targetInnerNanos := 100000000
  signalFloorMultiplier := 1.0
  slopeTolerance := 0.35
}

/- Except for the two canonical hard registrations annotated below, these
fixed registrations are correctness/hash anchors, not Phase-4 performance
evidence, and therefore have no complexity mode. They declare an
`expectedHash` so the harness fails on
silent value regressions: every Tier 1 irreducibility benchmark must report
`true` (the Conway entries are irreducible by construction), and the
`SupportedEntry` checksum must agree with its first observation. The
`expectedHash` for the `Bool` benches is `Hashable.hash true`; the
`SupportedEntry` checksum's literal is the `observed hash:` value the
harness emits on its first run. The cross-repeat `hashesAgree` check is
vacuous on `Bool` results (a stable `false` regression would still agree
with itself), which is why `expectedHash` is mandatory here. -/

setup_fixed_benchmark runConwayPolySupported_2_1Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash
    (checksumPoly (Conway.conwayPoly 2 1 Conway.supportedEntry_2_1)))
}

setup_fixed_benchmark runTier1Irreducibility_2_1Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

setup_fixed_benchmark runTier1Irreducibility_2_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

setup_fixed_benchmark runTier1Irreducibility_3_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

setup_fixed_benchmark runTier1Irreducibility_5_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

setup_fixed_benchmark runTier1Irreducibility_7_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

setup_fixed_benchmark runTier1Irreducibility_11_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

/- Mode 3: Rabin verification at `C(13, 6)`, the slowest committed Tier 1
entry. The 2 ms operation-scoped ceiling is 13.7× the clean 146.576 µs
calibration maximum on `chungus2` and 2.46× the prior 812.958 µs `carica`
median. Modes 1 and 2 are ruled out in the headline report. -/
setup_fixed_benchmark runTier1Irreducibility_13_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

setup_fixed_benchmark runTier2Compat_2_3_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

/- Mode 3: compatibility of `C(13, 1)` inside `C(13, 6)`, the committed pair
with both the largest prime and deepest six-factor Frobenius chain. The 1 ms
operation-scoped ceiling is 11.5× the clean 87.061 µs calibration maximum.
Modes 1 and 2 are ruled out in the headline report. -/
setup_fixed_benchmark runTier2Compat_13_1_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

setup_fixed_benchmark runTier2Compat_2_4_8Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

end Hex.ConwayBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
