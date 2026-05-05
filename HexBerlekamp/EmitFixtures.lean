import Hex.Conformance.Emit
import HexBerlekamp.DistinctDegree

/-!
JSONL emit driver for the `hex-berlekamp` oracle.

`lake exe hexberlekamp_emit_fixtures` writes one fixture record plus
one or more `result` records per case to `stdout` (or to
`$HEX_FIXTURE_OUTPUT` when set).  The companion oracle driver
`scripts/oracle/berlekamp_flint.py` reads the same stream and
re-runs the factorisation through python-flint's `nmod_poly` for
cross-check.

Fixtures cover monic `F_p[x]` polynomials at `p ∈ {5, 7, 11, 13}`
spanning the three structural shapes the SPEC distinguishes:
already-irreducible polynomials, products of distinct-degree
irreducibles, and polynomials with repeated factors.  For each case
we emit two `result` records that the oracle verifies:

* `rabin` — `Berlekamp.rabinTest` (the Bool irreducibility verdict).
  python-flint cross-checks by counting irreducible factors of the
  expected total degree.
* `ddf` — `Berlekamp.distinctDegreeFactor` (degree-bucketed
  factorisation product).  python-flint cross-checks by grouping
  its irreducible factor list by degree and multiplying within each
  group.

`squareFreeDecomposition` is intentionally **not** cross-checked
here: Lean's executable SFD splits out leading-coefficient units as
explicit constant factors, so it is not directly comparable to
FLINT's canonical square-free factorisation without a lossy
re-normalisation step.  Lean already self-verifies SFD
reconstruction in `HexPolyFp/Conformance.lean`; a dedicated SFD
oracle is left for a follow-up issue.

The fixture set is committed and intentionally small.  Coordinate
any future case-id additions with the `HexBerlekamp` Conformance
module so identical ids stay in sync.
-/

namespace Hex.BerlekampEmit

open Hex.Conformance.Emit
open Hex.Berlekamp

private def lib : String := "HexBerlekamp"

private instance bounds5 : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance bounds7 : ZMod64.Bounds 7 := ⟨by decide, by decide⟩
private instance bounds11 : ZMod64.Bounds 11 := ⟨by decide, by decide⟩
private instance bounds13 : ZMod64.Bounds 13 := ⟨by decide, by decide⟩

private theorem one_ne_zero_5 : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem one_ne_zero_7 : (1 : ZMod64 7) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 7) 1 0).mp h
  simp at hm

private theorem one_ne_zero_11 : (1 : ZMod64 11) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 11) 1 0).mp h
  simp at hm

private theorem one_ne_zero_13 : (1 : ZMod64 13) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 13) 1 0).mp h
  simp at hm

/-- Lift a `ZMod64 p` coefficient list to `List Int` via the canonical
representative in `[0, p)`.  Used both for fixture emission and for
serialising `result` records. -/
private def liftCoeffs {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Int :=
  f.toArray.toList.map (fun c => Int.ofNat c.toNat)

/-- Coefficient list of an `FpPoly p` rendered as a JSON array. -/
private def fpPolyJson {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : String :=
  polyValue (liftCoeffs f)

private def boolValue (b : Bool) : String :=
  if b then "true" else "false"

private def degreeBucketJson {p : Nat} [ZMod64.Bounds p]
    (b : DegreeBucket p) : String :=
  "[" ++ toString b.degree ++ "," ++ fpPolyJson b.factor ++ "]"

/-- `ddf` value: `{"buckets":[[deg,[coeffs]]...],"residual":[coeffs]}`. -/
private def ddfValue {p : Nat} [ZMod64.Bounds p]
    (d : DistinctDegreeFactorization p) : String :=
  let bucketsArr :=
    "[" ++ String.intercalate "," (d.buckets.map degreeBucketJson) ++ "]"
  "{\"buckets\":" ++ bucketsArr ++ ",\"residual\":" ++ fpPolyJson d.residual ++ "}"

/-- Emit one fixture record plus the two Berlekamp result records. -/
private def emitMonicCase {p : Nat} [ZMod64.Bounds p]
    (case : String) (f : FpPoly p) (hmonic : DensePoly.Monic f) : IO Unit := do
  emitPolyFixture lib case (liftCoeffs f) (some (Int.ofNat p))
  emitResult lib case "rabin" (boolValue (rabinTest f hmonic))
  emitResult lib case "ddf" (ddfValue (distinctDegreeFactor f hmonic))

/-- Build a monic `FpPoly p` from the lower-degree coefficients
(leading `1` is appended).  The returned proof witnesses that the
result is monic. -/
private def mkMonicAux {p : Nat} [ZMod64.Bounds p]
    (h1ne0 : (1 : ZMod64 p) ≠ 0) (lower : Array (ZMod64 p)) :
    { f : FpPoly p // DensePoly.Monic f } :=
  let coeffs := lower.push (1 : ZMod64 p)
  let f : FpPoly p :=
    { coeffs
      normalized := by
        right
        intro hback
        have hlast : coeffs.back? = some 1 := by
          simp [coeffs]
        rw [hlast] at hback
        exact h1ne0 (Option.some.inj hback) }
  ⟨f, by
    show f.leadingCoeff = 1
    show f.coeffs.back?.getD 0 = 1
    have hlast : f.coeffs.back? = some 1 := by
      simp [f, coeffs]
    rw [hlast]
    rfl⟩

/-- Wrap a list of `Nat` coefficients as a monic `FpPoly p`. -/
private def mkMonic {p : Nat} [ZMod64.Bounds p]
    (h1ne0 : (1 : ZMod64 p) ≠ 0) (lower : Array Nat) :
    { f : FpPoly p // DensePoly.Monic f } :=
  mkMonicAux h1ne0 (lower.map (fun n => ZMod64.ofNat p n))

/-- One fixture: prime, case id, lower-degree (sub-leading) coefficients. -/
private structure Case (p : Nat) [ZMod64.Bounds p] where
  id     : String
  lower  : Array Nat

private def cases5 : List (Case 5) :=
  [ -- Irreducible polynomials over F_5.
    { id := "p5/irr/deg2",       lower := #[2, 0] },                 -- x² + 2
    { id := "p5/irr/deg3",       lower := #[1, 1, 0] },              -- x³ + x + 1
    -- Reducible: products of 2-3 irreducibles, distinct degrees.
    -- (x+1)(x+2)(x+3) over F_5 = x³ + 6x² + 11x + 6 = x³ + x² + x + 1
    { id := "p5/red/lin3",       lower := #[1, 1, 1] },
    -- (x²+2)(x²+3) = x⁴ + 5x² + 6 ≡ x⁴ + 1 over F_5
    { id := "p5/red/quad2",      lower := #[1, 0, 0, 0] },
    -- (x²+2)(x+1)(x+2) = (x²+2)(x²+3x+2) = x⁴ + 3x³ + 4x² + 6x + 4
    --                                    ≡ x⁴ + 3x³ + 4x² + x + 4 over F_5
    { id := "p5/red/mixed",      lower := #[4, 1, 4, 3] },
    -- Repeated factors: (x+1)²(x+2) = (x²+2x+1)(x+2) = x³+4x²+5x+2 ≡ x³+4x²+2
    { id := "p5/rep/sqLin",      lower := #[2, 0, 4] },
    -- (x+1)³ = x³ + 3x² + 3x + 1
    { id := "p5/rep/cube",       lower := #[1, 3, 3] } ]

private def cases7 : List (Case 7) :=
  [ -- x² + 1: f(0..6) = 1,2,5,3,3,5,2 — no root, irreducible.
    { id := "p7/irr/deg2",       lower := #[1, 0] },
    -- x³ + 2: roots in F_7? 0³=0, 1³=1, 2³=1, 3³=6, 4³=1, 5³=6, 6³=6.
    -- x³+2 evaluated: 2,3,3,8≡1,3,8≡1,8≡1. No root → irreducible (deg 3).
    { id := "p7/irr/deg3",       lower := #[2, 0, 0] },
    -- (x+1)(x+2) = x² + 3x + 2
    { id := "p7/red/lin2",       lower := #[2, 3] },
    -- (x²+1)(x+1) = x³ + x² + x + 1 over F_7
    { id := "p7/red/mixed",      lower := #[1, 1, 1] },
    -- (x+1)²(x+3) = (x²+2x+1)(x+3) = x³+5x²+7x+3 ≡ x³+5x²+3 over F_7
    { id := "p7/rep/sqLin",      lower := #[3, 0, 5] } ]

private def cases11 : List (Case 11) :=
  [ -- x² + 7 over F_11: -7 ≡ 4 = 2² is a square, so reducible.  Try x² + 3:
    -- -3 ≡ 8 — squares mod 11 are {0,1,3,4,5,9}; 8 not a square → irreducible.
    { id := "p11/irr/deg2",      lower := #[3, 0] },
    -- (x+1)(x+2) = x² + 3x + 2
    { id := "p11/red/lin2",      lower := #[2, 3] },
    -- (x+1)²(x+2) = (x²+2x+1)(x+2) = x³+4x²+5x+2 over F_11
    { id := "p11/rep/sqLin",     lower := #[2, 5, 4] } ]

private def cases13 : List (Case 13) :=
  [ -- x² + 2 over F_13: -2 ≡ 11; squares mod 13 are {0,1,3,4,9,10,12}; 11 not
    -- a square → irreducible.
    { id := "p13/irr/deg2",      lower := #[2, 0] },
    -- (x+1)(x+5) = x² + 6x + 5 over F_13
    { id := "p13/red/lin2",      lower := #[5, 6] },
    -- (x+1)²(x+2) = x³+4x²+5x+2 over F_13
    { id := "p13/rep/sqLin",     lower := #[2, 5, 4] } ]

private def emitCase5 (c : Case 5) : IO Unit :=
  let m := mkMonic one_ne_zero_5 c.lower
  emitMonicCase c.id m.1 m.2

private def emitCase7 (c : Case 7) : IO Unit :=
  let m := mkMonic one_ne_zero_7 c.lower
  emitMonicCase c.id m.1 m.2

private def emitCase11 (c : Case 11) : IO Unit :=
  let m := mkMonic one_ne_zero_11 c.lower
  emitMonicCase c.id m.1 m.2

private def emitCase13 (c : Case 13) : IO Unit :=
  let m := mkMonic one_ne_zero_13 c.lower
  emitMonicCase c.id m.1 m.2

end Hex.BerlekampEmit

def main : IO Unit := do
  for c in Hex.BerlekampEmit.cases5  do Hex.BerlekampEmit.emitCase5  c
  for c in Hex.BerlekampEmit.cases7  do Hex.BerlekampEmit.emitCase7  c
  for c in Hex.BerlekampEmit.cases11 do Hex.BerlekampEmit.emitCase11 c
  for c in Hex.BerlekampEmit.cases13 do Hex.BerlekampEmit.emitCase13 c
