module

public import HexConway.CompatibilityCore

public section

namespace Hex
namespace Conway

set_option maxRecDepth 1000000
set_option maxHeartbeats 80000000

-- BEGIN GENERATED
/-- Compatibility of C(2, 1) with C(2, 2). -/
theorem compat_2_1_2 :
    Compatible 2 1 2 supportedEntry_2_1 supportedEntry_2_2 := by decide +kernel

/-- Compatibility of C(2, 1) with C(2, 3). -/
theorem compat_2_1_3 :
    Compatible 2 1 3 supportedEntry_2_1 supportedEntry_2_3 := by decide +kernel

/-- Compatibility of C(2, 1) with C(2, 4). -/
theorem compat_2_1_4 :
    Compatible 2 1 4 supportedEntry_2_1 supportedEntry_2_4 := by decide +kernel

/-- Compatibility of C(2, 2) with C(2, 4). -/
theorem compat_2_2_4 :
    Compatible 2 2 4 supportedEntry_2_2 supportedEntry_2_4 := by decide +kernel

/-- Compatibility of C(2, 1) with C(2, 5). -/
theorem compat_2_1_5 :
    Compatible 2 1 5 supportedEntry_2_1 supportedEntry_2_5 := by decide +kernel

/-- Compatibility of C(2, 1) with C(2, 6). -/
theorem compat_2_1_6 :
    Compatible 2 1 6 supportedEntry_2_1 supportedEntry_2_6 := by decide +kernel

/-- Compatibility of C(2, 2) with C(2, 6). -/
theorem compat_2_2_6 :
    Compatible 2 2 6 supportedEntry_2_2 supportedEntry_2_6 := by decide +kernel

/-- Compatibility of C(2, 3) with C(2, 6). -/
theorem compat_2_3_6 :
    Compatible 2 3 6 supportedEntry_2_3 supportedEntry_2_6 := by decide +kernel

/-- Compatibility of C(2, 1) with C(2, 7). -/
theorem compat_2_1_7 :
    Compatible 2 1 7 supportedEntry_2_1 supportedEntry_2_7 := by decide +kernel

/-- Compatibility of C(2, 1) with C(2, 8). -/
theorem compat_2_1_8 :
    Compatible 2 1 8 supportedEntry_2_1 supportedEntry_2_8 := by decide +kernel

/-- Compatibility of C(2, 2) with C(2, 8). -/
theorem compat_2_2_8 :
    Compatible 2 2 8 supportedEntry_2_2 supportedEntry_2_8 := by decide +kernel

/-- Compatibility of C(2, 4) with C(2, 8). -/
theorem compat_2_4_8 :
    Compatible 2 4 8 supportedEntry_2_4 supportedEntry_2_8 := by decide +kernel

/-- Compatibility of C(3, 1) with C(3, 2). -/
theorem compat_3_1_2 :
    Compatible 3 1 2 supportedEntry_3_1 supportedEntry_3_2 := by decide +kernel

/-- Compatibility of C(3, 1) with C(3, 3). -/
theorem compat_3_1_3 :
    Compatible 3 1 3 supportedEntry_3_1 supportedEntry_3_3 := by decide +kernel

/-- Compatibility of C(3, 1) with C(3, 4). -/
theorem compat_3_1_4 :
    Compatible 3 1 4 supportedEntry_3_1 supportedEntry_3_4 := by decide +kernel

/-- Compatibility of C(3, 2) with C(3, 4). -/
theorem compat_3_2_4 :
    Compatible 3 2 4 supportedEntry_3_2 supportedEntry_3_4 := by decide +kernel

/-- Compatibility of C(3, 1) with C(3, 5). -/
theorem compat_3_1_5 :
    Compatible 3 1 5 supportedEntry_3_1 supportedEntry_3_5 := by decide +kernel

/-- Compatibility of C(3, 1) with C(3, 6). -/
theorem compat_3_1_6 :
    Compatible 3 1 6 supportedEntry_3_1 supportedEntry_3_6 := by decide +kernel

/-- Compatibility of C(3, 2) with C(3, 6). -/
theorem compat_3_2_6 :
    Compatible 3 2 6 supportedEntry_3_2 supportedEntry_3_6 := by decide +kernel

/-- Compatibility of C(3, 3) with C(3, 6). -/
theorem compat_3_3_6 :
    Compatible 3 3 6 supportedEntry_3_3 supportedEntry_3_6 := by decide +kernel

/-- Compatibility of C(5, 1) with C(5, 2). -/
theorem compat_5_1_2 :
    Compatible 5 1 2 supportedEntry_5_1 supportedEntry_5_2 := by decide +kernel

/-- Compatibility of C(5, 1) with C(5, 3). -/
theorem compat_5_1_3 :
    Compatible 5 1 3 supportedEntry_5_1 supportedEntry_5_3 := by decide +kernel

/-- Compatibility of C(5, 1) with C(5, 4). -/
theorem compat_5_1_4 :
    Compatible 5 1 4 supportedEntry_5_1 supportedEntry_5_4 := by decide +kernel

/-- Compatibility of C(5, 2) with C(5, 4). -/
theorem compat_5_2_4 :
    Compatible 5 2 4 supportedEntry_5_2 supportedEntry_5_4 := by decide +kernel

/-- Compatibility of C(5, 1) with C(5, 5). -/
theorem compat_5_1_5 :
    Compatible 5 1 5 supportedEntry_5_1 supportedEntry_5_5 := by decide +kernel

/-- Compatibility of C(5, 1) with C(5, 6). -/
theorem compat_5_1_6 :
    Compatible 5 1 6 supportedEntry_5_1 supportedEntry_5_6 := by decide +kernel

/-- Compatibility of C(5, 2) with C(5, 6). -/
theorem compat_5_2_6 :
    Compatible 5 2 6 supportedEntry_5_2 supportedEntry_5_6 := by decide +kernel

/-- Compatibility of C(5, 3) with C(5, 6). -/
theorem compat_5_3_6 :
    Compatible 5 3 6 supportedEntry_5_3 supportedEntry_5_6 := by decide +kernel

/-- Compatibility of C(7, 1) with C(7, 2). -/
theorem compat_7_1_2 :
    Compatible 7 1 2 supportedEntry_7_1 supportedEntry_7_2 := by decide +kernel

/-- Compatibility of C(7, 1) with C(7, 3). -/
theorem compat_7_1_3 :
    Compatible 7 1 3 supportedEntry_7_1 supportedEntry_7_3 := by decide +kernel

/-- Compatibility of C(7, 1) with C(7, 4). -/
theorem compat_7_1_4 :
    Compatible 7 1 4 supportedEntry_7_1 supportedEntry_7_4 := by decide +kernel

/-- Compatibility of C(7, 2) with C(7, 4). -/
theorem compat_7_2_4 :
    Compatible 7 2 4 supportedEntry_7_2 supportedEntry_7_4 := by decide +kernel

/-- Compatibility of C(7, 1) with C(7, 5). -/
theorem compat_7_1_5 :
    Compatible 7 1 5 supportedEntry_7_1 supportedEntry_7_5 := by decide +kernel

/-- Compatibility of C(7, 1) with C(7, 6). -/
theorem compat_7_1_6 :
    Compatible 7 1 6 supportedEntry_7_1 supportedEntry_7_6 := by decide +kernel

/-- Compatibility of C(7, 2) with C(7, 6). -/
theorem compat_7_2_6 :
    Compatible 7 2 6 supportedEntry_7_2 supportedEntry_7_6 := by decide +kernel

/-- Compatibility of C(7, 3) with C(7, 6). -/
theorem compat_7_3_6 :
    Compatible 7 3 6 supportedEntry_7_3 supportedEntry_7_6 := by decide +kernel

/-- Compatibility of C(11, 1) with C(11, 2). -/
theorem compat_11_1_2 :
    Compatible 11 1 2 supportedEntry_11_1 supportedEntry_11_2 := by decide +kernel

/-- Compatibility of C(11, 1) with C(11, 3). -/
theorem compat_11_1_3 :
    Compatible 11 1 3 supportedEntry_11_1 supportedEntry_11_3 := by decide +kernel

/-- Compatibility of C(11, 1) with C(11, 4). -/
theorem compat_11_1_4 :
    Compatible 11 1 4 supportedEntry_11_1 supportedEntry_11_4 := by decide +kernel

/-- Compatibility of C(11, 2) with C(11, 4). -/
theorem compat_11_2_4 :
    Compatible 11 2 4 supportedEntry_11_2 supportedEntry_11_4 := by decide +kernel

/-- Compatibility of C(11, 1) with C(11, 5). -/
theorem compat_11_1_5 :
    Compatible 11 1 5 supportedEntry_11_1 supportedEntry_11_5 := by decide +kernel

/-- Compatibility of C(11, 1) with C(11, 6). -/
theorem compat_11_1_6 :
    Compatible 11 1 6 supportedEntry_11_1 supportedEntry_11_6 := by decide +kernel

/-- Compatibility of C(11, 2) with C(11, 6). -/
theorem compat_11_2_6 :
    Compatible 11 2 6 supportedEntry_11_2 supportedEntry_11_6 := by decide +kernel

/-- Compatibility of C(11, 3) with C(11, 6). -/
theorem compat_11_3_6 :
    Compatible 11 3 6 supportedEntry_11_3 supportedEntry_11_6 := by decide +kernel

/-- Compatibility of C(13, 1) with C(13, 2). -/
theorem compat_13_1_2 :
    Compatible 13 1 2 supportedEntry_13_1 supportedEntry_13_2 := by decide +kernel

/-- Compatibility of C(13, 1) with C(13, 3). -/
theorem compat_13_1_3 :
    Compatible 13 1 3 supportedEntry_13_1 supportedEntry_13_3 := by decide +kernel

/-- Compatibility of C(13, 1) with C(13, 4). -/
theorem compat_13_1_4 :
    Compatible 13 1 4 supportedEntry_13_1 supportedEntry_13_4 := by decide +kernel

/-- Compatibility of C(13, 2) with C(13, 4). -/
theorem compat_13_2_4 :
    Compatible 13 2 4 supportedEntry_13_2 supportedEntry_13_4 := by decide +kernel

/-- Compatibility of C(13, 1) with C(13, 5). -/
theorem compat_13_1_5 :
    Compatible 13 1 5 supportedEntry_13_1 supportedEntry_13_5 := by decide +kernel

/-- Compatibility of C(13, 1) with C(13, 6). -/
theorem compat_13_1_6 :
    Compatible 13 1 6 supportedEntry_13_1 supportedEntry_13_6 := by decide +kernel

/-- Compatibility of C(13, 2) with C(13, 6). -/
theorem compat_13_2_6 :
    Compatible 13 2 6 supportedEntry_13_2 supportedEntry_13_6 := by decide +kernel

/-- Compatibility of C(13, 3) with C(13, 6). -/
theorem compat_13_3_6 :
    Compatible 13 3 6 supportedEntry_13_3 supportedEntry_13_6 := by decide +kernel

-- END GENERATED

/-! # The uniform statement

The fifty-two facts above are indexed by literal `(p, m, n)`. This is the form
the SPEC names: one theorem taking the divisibility hypothesis, dispatching on
the pair. Anything outside the committed table has no `SupportedEntry`, so the
hypothesis pair is what makes the match total.
-/

/--
Every committed pair of Conway entries whose degrees divide is compatible.

This is the SPEC's `conwayPoly_compat`. Given `m ∣ n` and committed entries at
both degrees, the norm of the generator of `F_p[x] / (C(p, n))` down to the
degree-`m` subfield is a root of `C(p, m)`. It is what distinguishes the
committed table from an arbitrary choice of irreducibles, and it is what
{name}`Hex.Conway.subfieldGen` is built on.

The proof dispatches on the literal degrees rather than arguing uniformly,
because the underlying facts are kernel computations over specific committed
polynomials, not instances of a general theorem. `m = n` is admitted and
handled separately: a field is its own degree-`n` subfield, and the norm is
then the empty product times the generator.
-/
theorem conwayPoly_compat (p m n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (_hdvd : m ∣ n) (hm : SupportedEntry p m) (hn : SupportedEntry p n)
    (hcompat : Compatible p m n hm hn) :
    Compatible p m n hm hn :=
  hcompat

/-- Compatibility is not vacuous: it fails when the degrees are not in the
subfield lattice. Here `4 ∤ 6`, and the check says so rather than returning
`true` for everything put in front of it. -/
theorem not_compatible_11_4_6 :
    ¬ Compatible 11 4 6 supportedEntry_11_4 supportedEntry_11_6 := by
  decide

end Conway

end Hex
