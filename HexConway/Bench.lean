import HexConway.Basic
import LeanBench

/-!
Benchmark registrations for `hex-conway`.

This first Phase 4 slice covers only the Tier 1 committed-table lookup surface.
It does not benchmark Tier 2 Conway compatibility verification or Tier 3
on-demand Conway search.

Scientific registrations:

* `runLuebeckConwayPolynomialLookupChecksum`: look up every committed Luebeck
  table key in the current Tier 1 slice, using the one-based table ordinal as
  the benchmark parameter.
* `runConwayPolySupported_2_1Checksum`: fixed canonical measurement for the
  currently exported `SupportedEntry` path, `C(2, 1)`.
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

/-- Fixed repeat count for the nanosecond-scale lookup path. -/
def lookupHotRepeats : Nat :=
  65536

/-- Repeat a deterministic `UInt64` target with a rolling checksum. -/
def repeatUInt64Checksum (repeats : Nat) (f : Unit → UInt64) : UInt64 :=
  (List.range repeats).foldl
    (fun acc _ => mixHash acc (f ()))
    0

/-- Benchmark target: committed Tier 1 Luebeck lookup by table ordinal. -/
def runLuebeckConwayPolynomialLookupChecksum (ordinal : Nat) : UInt64 :=
  repeatUInt64Checksum lookupHotRepeats fun _ =>
    match committedEntryKeyAt ordinal with
    | ⟨2, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 2 n)
    | ⟨3, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 3 n)
    | ⟨5, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 5 n)
    | ⟨7, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 7 n)
    | ⟨11, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 11 n)
    | ⟨13, n⟩ => checksumLookup (Conway.luebeckConwayPolynomial? 13 n)
    | _ => 0

/-- Fixed canonical target: recover the currently exported supported entry. -/
def runConwayPolySupported_2_1Checksum : UInt64 :=
  checksumPoly (Conway.conwayPoly 2 1 Conway.supportedEntry_2_1)

/-- Textbook model for finite committed-table lookup at a given table key. -/
def tier1LookupComplexity (_ordinal : Nat) : Nat :=
  1

/- Complexity derivation: Tier 1 is a committed finite database lookup keyed by
`(p, n)`. The benchmark parameter is the one-based ordinal into the committed
key set; for each key, the textbook table-lookup model performs one finite-key
dispatch and materializes the stored coefficient row, whose degree is bounded
by the committed Tier 1 slice in this registration. The fixed hot-loop repeat
count is independent of the ordinal, so it changes only the constant factor. -/
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

setup_fixed_benchmark runConwayPolySupported_2_1Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

end Hex.ConwayBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
