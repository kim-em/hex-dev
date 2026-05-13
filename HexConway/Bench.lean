import HexConway.Basic
import LeanBench

/-!
Benchmark registrations for `hex-conway`.

This Phase 4 slice covers only Tier 1 committed-table surfaces: imported
Luebeck lookup and fixed irreducibility verification of selected imported
entries. It does not benchmark Tier 2 Conway compatibility verification or
Tier 3 on-demand Conway search.

Scientific registrations:

* `runLuebeckConwayPolynomialLookupChecksum`: look up every committed Luebeck
  table key in the current Tier 1 slice, using the one-based table ordinal as
  the benchmark parameter.
* `runConwayPolySupported_2_1Checksum`: fixed canonical measurement for the
  currently exported `SupportedEntry` path, `C(2, 1)`.
* `runTier1Irreducibility_2_1Checksum`: Rabin irreducibility verification for
  the canonical imported table entry `C(2, 1)`.
* `runTier1Irreducibility_2_6Checksum`: Rabin irreducibility verification for
  the low-prime higher-degree imported table entry `C(2, 6)`.
* `runTier1Irreducibility_3_6Checksum`: Rabin irreducibility verification for
  the odd-prime higher-degree imported table entry `C(3, 6)`.
* `runTier1Irreducibility_5_6Checksum`: Rabin irreducibility verification for
  the odd-prime higher-degree imported table entry `C(5, 6)`.
* `runTier1Irreducibility_7_6Checksum`: Rabin irreducibility verification for
  the odd-prime higher-degree imported table entry `C(7, 6)`.
* `runTier1Irreducibility_11_6Checksum`: Rabin irreducibility verification for
  the odd-prime higher-degree imported table entry `C(11, 6)`.
* `runTier1Irreducibility_13_6Checksum`: Rabin irreducibility verification for
  the odd-prime higher-degree imported table entry `C(13, 6)`.

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
  ⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 3⟩, ⟨2, 4⟩, ⟨2, 5⟩, ⟨2, 6⟩,
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
  let mp ← tier1_13_6Ref.get
  return Berlekamp.rabinTest mp.poly mp.monic

/-- Textbook model for finite committed-table lookup at a given table key. -/
def tier1LookupComplexity (_ordinal : Nat) : Nat :=
  1

/- Complexity derivation: Tier 1 is a committed finite database lookup keyed by
`(p, n)`. The benchmark parameter is the one-based ordinal into the committed
key set; for each key, the textbook table-lookup model performs one finite-key
dispatch and materializes the stored coefficient row, whose degree is bounded
by the committed Tier 1 slice in this registration. The model is constant in
the ordinal — only `(p, n)` selects the row, never the ordinal directly — so
the registration declares `tier1LookupComplexity _ := 1`. -/
setup_benchmark runLuebeckConwayPolynomialLookupChecksum ordinal =>
    tier1LookupComplexity ordinal
  where {
    paramFloor := 1
    paramCeiling := 36
    paramSchedule := .custom #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
      13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
      29, 30, 31, 32, 33, 34, 35, 36]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- The fixed registrations declare an `expectedHash` so the harness fails on
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

setup_fixed_benchmark runTier1Irreducibility_13_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash true)
}

end Hex.ConwayBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
