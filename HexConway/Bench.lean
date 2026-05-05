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
-/

namespace Hex.ConwayBench

private theorem one_ne_zero_two : (1 : ZMod64 2) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 2) 1 0).mp h
  simp at hm

private theorem one_ne_zero_three : (1 : ZMod64 3) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 3) 1 0).mp h
  simp at hm

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem one_ne_zero_seven : (1 : ZMod64 7) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 7) 1 0).mp h
  simp at hm

private theorem one_ne_zero_eleven : (1 : ZMod64 11) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 11) 1 0).mp h
  simp at hm

private theorem one_ne_zero_thirteen : (1 : ZMod64 13) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 13) 1 0).mp h
  simp at hm

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

/-- Fixed repeat count for the selected Tier 1 irreducibility checks. -/
def irreducibilityHotRepeats : Nat :=
  256

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

/-- The committed `C(2, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_2_6 : FpPoly 2 :=
  { coeffs := #[(1 : ZMod64 2), 1, 0, 1, 1, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_two }

/-- The committed `C(2, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_2_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_6 := by
  rfl

/-- The committed `C(3, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_3_6 : FpPoly 3 :=
  { coeffs := #[(2 : ZMod64 3), 2, 1, 0, 2, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_three }

/-- The committed `C(3, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_3_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_3_6 := by
  rfl

/-- The committed `C(5, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_5_6 : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1, 4, 1, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

/-- The committed `C(5, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_5_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_5_6 := by
  rfl

/-- The committed `C(7, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_7_6 : FpPoly 7 :=
  { coeffs := #[(3 : ZMod64 7), 6, 4, 5, 1, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_seven }

/-- The committed `C(7, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_7_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_7_6 := by
  rfl

/-- The committed `C(11, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_11_6 : FpPoly 11 :=
  { coeffs := #[(2 : ZMod64 11), 7, 6, 4, 3, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_eleven }

/-- The committed `C(11, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_11_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_11_6 := by
  rfl

/-- The committed `C(13, 6)` Luebeck entry, stored ascending by degree. -/
def luebeckConwayPolynomial_13_6 : FpPoly 13 :=
  { coeffs := #[(2 : ZMod64 13), 11, 11, 10, 0, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_thirteen }

/-- The committed `C(13, 6)` entry is monic. -/
theorem luebeckConwayPolynomial_13_6_monic :
    DensePoly.Monic luebeckConwayPolynomial_13_6 := by
  rfl

#guard Conway.luebeckConwayPolynomial? 2 1 == some Conway.luebeckConwayPolynomial_2_1
#guard Conway.luebeckConwayPolynomial? 2 6 == some luebeckConwayPolynomial_2_6
#guard Conway.luebeckConwayPolynomial? 3 6 == some luebeckConwayPolynomial_3_6
#guard Conway.luebeckConwayPolynomial? 5 6 == some luebeckConwayPolynomial_5_6
#guard Conway.luebeckConwayPolynomial? 7 6 == some luebeckConwayPolynomial_7_6
#guard Conway.luebeckConwayPolynomial? 11 6 == some luebeckConwayPolynomial_11_6
#guard Conway.luebeckConwayPolynomial? 13 6 == some luebeckConwayPolynomial_13_6

/-- Benchmark target: Tier 1 irreducibility check for imported `C(2, 1)`. -/
def runTier1Irreducibility_2_1Checksum : UInt64 :=
  repeatUInt64Checksum irreducibilityHotRepeats fun _ =>
    hash <| Berlekamp.rabinTest
      Conway.luebeckConwayPolynomial_2_1
      Conway.luebeckConwayPolynomial_2_1_monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(2, 6)`. -/
def runTier1Irreducibility_2_6Checksum : UInt64 :=
  repeatUInt64Checksum irreducibilityHotRepeats fun _ =>
    hash <| Berlekamp.rabinTest
      luebeckConwayPolynomial_2_6
      luebeckConwayPolynomial_2_6_monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(3, 6)`. -/
def runTier1Irreducibility_3_6Checksum : UInt64 :=
  repeatUInt64Checksum irreducibilityHotRepeats fun _ =>
    hash <| Berlekamp.rabinTest
      luebeckConwayPolynomial_3_6
      luebeckConwayPolynomial_3_6_monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(5, 6)`. -/
def runTier1Irreducibility_5_6Checksum : UInt64 :=
  repeatUInt64Checksum irreducibilityHotRepeats fun _ =>
    hash <| Berlekamp.rabinTest
      luebeckConwayPolynomial_5_6
      luebeckConwayPolynomial_5_6_monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(7, 6)`. -/
def runTier1Irreducibility_7_6Checksum : UInt64 :=
  repeatUInt64Checksum irreducibilityHotRepeats fun _ =>
    hash <| Berlekamp.rabinTest
      luebeckConwayPolynomial_7_6
      luebeckConwayPolynomial_7_6_monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(11, 6)`. -/
def runTier1Irreducibility_11_6Checksum : UInt64 :=
  repeatUInt64Checksum irreducibilityHotRepeats fun _ =>
    hash <| Berlekamp.rabinTest
      luebeckConwayPolynomial_11_6
      luebeckConwayPolynomial_11_6_monic

/-- Benchmark target: Tier 1 irreducibility check for imported `C(13, 6)`. -/
def runTier1Irreducibility_13_6Checksum : UInt64 :=
  repeatUInt64Checksum irreducibilityHotRepeats fun _ =>
    hash <| Berlekamp.rabinTest
      luebeckConwayPolynomial_13_6
      luebeckConwayPolynomial_13_6_monic

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

/- Fixed Tier 1 irreducibility registrations use committed Luebeck inputs and
the executable Rabin checker from `HexBerlekamp`. They intentionally measure
only the imported-polynomial irreducibility path: no Tier 2 Conway compatibility
conditions and no Tier 3 search are included. `C(2, 1)` is the canonical
supported entry; `C(2, 6)`, `C(3, 6)`, `C(5, 6)`, `C(7, 6)`, `C(11, 6)`,
and `C(13, 6)` cover representative higher-degree committed-table entries
across small binary and odd-prime fields. -/
setup_fixed_benchmark runTier1Irreducibility_2_1Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

setup_fixed_benchmark runTier1Irreducibility_2_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

setup_fixed_benchmark runTier1Irreducibility_3_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

setup_fixed_benchmark runTier1Irreducibility_5_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

setup_fixed_benchmark runTier1Irreducibility_7_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

setup_fixed_benchmark runTier1Irreducibility_11_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

setup_fixed_benchmark runTier1Irreducibility_13_6Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
}

end Hex.ConwayBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
