import HexGfqMathlib.GF2q

/-!
Core conformance checks for `HexGfqMathlib`.

Oracle:
- none for this `core` profile; checks are deterministic Lean-side bridge
  fixtures.

Mode:
- always.

Covered operations:
- reduced-polynomial finite indexing for `FpPoly`.
- `GFq` finite cardinality and `GaloisField` bridge surfaces.
- optimized binary `GF2q` to generic `GFq` bridge surface.

Covered properties:
- committed bounded representatives round-trip through finite indices.
- the committed `C(2, 1)` generic field has cardinality `2`.
- the generic `GFq 2 1` and Mathlib `GaloisField 2 1` cardinality and
  ring-equivalence surfaces elaborate on the committed instance.
- the packed `GF2q 1` to generic `GFq 2 1` ring equivalence elaborates on
  the committed packed instance.

Covered edge cases:
- zero and one reduced representatives below degree one.
- the smallest committed Conway entry `(p, n) = (2, 1)`.
-/

namespace HexGfqMathlib

open Hex

noncomputable section

private instance conformanceBoundsTwo : Hex.ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private abbrev Entry21 : Conway.SupportedEntry 2 1 :=
  Conway.supportedEntry_2_1

private instance conformancePrimeModulusTwo : Hex.ZMod64.PrimeModulus 2 :=
  Hex.ZMod64.primeModulusOfPrime Entry21.prime

private def polyTwo (coeffs : Array Nat) : Hex.FpPoly 2 :=
  Hex.FpPoly.ofCoeffs (coeffs.map (fun n => Hex.ZMod64.ofNat 2 n))

private def coeffNats (f : Hex.FpPoly 2) : List Nat :=
  f.toArray.toList.map Hex.ZMod64.toNat

#guard FpPoly.coeffIndex 1 (polyTwo #[0]) = 0
#guard FpPoly.coeffIndex 1 (polyTwo #[1]) = 1
#guard coeffNats (FpPoly.ofIndexBelowDegree (p := 2) 1 0) = []
#guard coeffNats (FpPoly.ofIndexBelowDegree (p := 2) 1 1) = [1]

example :
    Hex.FpPoly.degree (FpPoly.ofIndexBelowDegree (p := 2) 1 0) < 1 :=
  FpPoly.ofIndexBelowDegree_degree_lt (p := 2) 1 ⟨0, by decide⟩

example :
    Hex.FpPoly.degree (FpPoly.ofIndexBelowDegree (p := 2) 1 1) < 1 :=
  FpPoly.ofIndexBelowDegree_degree_lt (p := 2) 1 ⟨1, by decide⟩

example :
    FpPoly.coeffIndex 1 (FpPoly.ofIndexBelowDegree (p := 2) 1 0) = 0 :=
  FpPoly.coeffIndex_ofIndexBelowDegree (p := 2) 1 ⟨0, by decide⟩

example :
    FpPoly.coeffIndex 1 (FpPoly.ofIndexBelowDegree (p := 2) 1 1) = 1 :=
  FpPoly.coeffIndex_ofIndexBelowDegree (p := 2) 1 ⟨1, by decide⟩

example :
    Fintype.card (Hex.GFq 2 1 Entry21) = 2 := by
  simpa using GFq.fintype_card_eq_pow Entry21

example :
    Fintype.card (Hex.GFq 2 1 Entry21) = Nat.card (GaloisField 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  simpa using GFq.card_eq_galoisField_card (h := Entry21) (hn := by decide)

example :
    RingEquiv (Hex.GFq 2 1 Entry21) (GaloisField 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact GFq.equivGaloisField Entry21 (by decide)

example :
    RingEquiv (Hex.GF2q 1)
      (Hex.GFq 2 1 (inferInstance : Conway.PackedGF2Entry 1).entry) :=
  Hex.GF2q.equivGFq (n := 1)

end

end HexGfqMathlib
