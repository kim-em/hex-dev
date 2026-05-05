import Hex.Conformance.Emit
import HexGF2.Field

/-!
JSONL emit driver for the `hex-gf2` oracle.

`lake exe hexgf2_emit_fixtures` writes one fixture record per
component (a poly fixture per polynomial input) plus one `result`
record per cross-checked operation to `stdout` (or to
`$HEX_FIXTURE_OUTPUT` when set).  The companion oracle driver
`scripts/oracle/gf2_flint.py` reads the same stream and re-runs each
operation through python-flint's `nmod_poly` (for `F_2[x]` arithmetic)
and `fq_default_ctx` (for the `GF(2^n)` extension fields).

Two families of fixtures
------------------------

* **`F_2[x]` arithmetic** — `mul`, `gcd`, `divmod` on polynomial pairs
  at degrees 16, 32, 64, 128.  Source polynomials are standard
  generator polynomials from CRC and GHASH so the inputs exercise
  realistic high-degree code paths through the packed XOR / clmul /
  long-division pipeline.

* **`GF(2^n)` field arithmetic** — `gf_mul`, `gf_inverse`,
  `gf_frobenius` (squaring in characteristic 2) at `n ∈ {4, 8, 16}`.
  The `n = 8` case uses the AES irreducible `x^8 + x^4 + x^3 + x + 1`.
  The modulus polynomial is emitted alongside the inputs so the oracle
  reconstructs the field independently.

Irreducibility witnesses are local `sorry` axioms — the same pattern
`HexGF2/Conformance.lean` uses for the AES modulus, since Hex does
not yet have native irreducibility certificates for these polynomials.
python-flint independently rejects a non-irreducible modulus when
constructing `fq_default_ctx`, so the oracle catches a misclassified
modulus on the next run rather than silently masking it.
-/

namespace Hex.GF2Emit

open Hex.Conformance.Emit
open Hex
open Hex.GF2Poly

private def lib : String := "HexGF2"

/-- Convert a `GF2Poly` to its ascending coefficient list (0/1).  The
empty list represents the zero polynomial, matching python-flint's
`nmod_poly([], 2)` normalisation. -/
private def coeffsOf (p : GF2Poly) : List Int :=
  if p.isZero then []
  else (List.range (p.degree + 1)).map fun i =>
    if p.coeff i then (1 : Int) else 0

/-- Coefficient list of the packed-word residue stored in a `GF2n.val`. -/
private def coeffsOfWord (w : UInt64) : List Int :=
  coeffsOf (ofUInt64 w)

/-- Emit a `poly` fixture with `modulus = 2`, the `F_2`-coefficient
form expected by the gf2 oracle. -/
private def emitPoly2 (case : String) (p : GF2Poly) : IO Unit :=
  emitPolyFixture lib case (coeffsOf p) (some 2)

/-! ## `F_2[x]` arithmetic fixtures -/

private structure PolyCase where
  id : String
  a  : GF2Poly
  b  : GF2Poly

private def emitPolyCase (c : PolyCase) : IO Unit := do
  emitPoly2 (c.id ++ "/a") c.a
  emitPoly2 (c.id ++ "/b") c.b
  emitResult lib c.id "mul"
    (polyValue (coeffsOf (c.a * c.b)))
  emitResult lib c.id "gcd"
    (polyValue (coeffsOf (gcd c.a c.b)))
  let qr := divMod c.a c.b
  emitResult lib c.id "divmod"
    (divModValue (coeffsOf qr.1) (coeffsOf qr.2))

private def cases_f2x : List PolyCase :=
  [ -- deg 16: CRC-16-CCITT generator `x^16 + x^12 + x^5 + 1` paired
    -- with the reflected CRC-16-IBM tap polynomial.
    { id := "f2x/deg16"
      a  := ofUInt64 0x1021 + monomial 16
      b  := ofUInt64 0xA001 }
    -- deg 32: CRC-32-IEEE generator paired with the reflected form
    -- — both polynomials live entirely inside the low word, so the
    -- product crosses one word boundary.
  , { id := "f2x/deg32"
      a  := ofUInt64 0x04C11DB7 + monomial 32
      b  := ofUInt64 0xEDB88320 }
    -- deg 64: CRC-64-ECMA generator paired with the reflected form
    -- — `a` straddles the implicit `x^64` bit, exercising the
    -- packed-word boundary in mul/divmod.
  , { id := "f2x/deg64"
      a  := ofUInt64 0x42F0E1EBA9EA3693 + monomial 64
      b  := ofUInt64 0xC96C5795D7870F42 }
    -- deg 128: GHASH polynomial `x^128 + x^7 + x^2 + x + 1` paired
    -- with a degree-127 dense pattern; product reaches degree 255 and
    -- exercises the third packed word.
  , { id := "f2x/deg128"
      a  := ofUInt64 0x87 + monomial 128
      b  := ofWords #[0xDEADBEEFCAFEBABE, 0x0123456789ABCDEF] } ]

/-! ## `GF(2^n)` field fixtures -/

private theorem gf16Irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x3 4) := by
  sorry

private theorem aesIrr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x1B 8) := by
  sorry

private theorem gf65kIrr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x100B 16) := by
  sorry

private abbrev GF16  : Type :=
  Hex.GF2n 4  0x3    (by decide) (by decide) gf16Irr

private abbrev AES   : Type :=
  Hex.GF2n 8  0x1B   (by decide) (by decide) aesIrr

private abbrev GF65K : Type :=
  Hex.GF2n 16 0x100B (by decide) (by decide) gf65kIrr

private def gf16  (w : UInt64) : GF16  := Hex.GF2n.reduce w
private def aes   (w : UInt64) : AES   := Hex.GF2n.reduce w
private def gf65k (w : UInt64) : GF65K := Hex.GF2n.reduce w

/-- Emit one GF(2^n) case: the modulus, two single-word inputs, and
result records for `gf_mul`, `gf_inverse`, `gf_frobenius`.  Frobenius
in characteristic two collapses to squaring, so we feed the oracle
`(a * a)` directly rather than going through the binary-exponentiation
loop in `Hex.GF2n.pow`. -/
private def emitGFCase (id : String) (modulus : GF2Poly)
    (aVal bVal mulVal invVal frobVal : UInt64) : IO Unit := do
  emitPoly2 (id ++ "/modulus") modulus
  emitPoly2 (id ++ "/a") (ofUInt64 aVal)
  emitPoly2 (id ++ "/b") (ofUInt64 bVal)
  emitResult lib id "gf_mul"       (polyValue (coeffsOfWord mulVal))
  emitResult lib id "gf_inverse"   (polyValue (coeffsOfWord invVal))
  emitResult lib id "gf_frobenius" (polyValue (coeffsOfWord frobVal))

private def emitGF16Case (id : String) (a b : GF16) : IO Unit :=
  emitGFCase id (ofUInt64Monic 0x3 4) a.val b.val
    (a * b).val a⁻¹.val (a * a).val

private def emitAESCase (id : String) (a b : AES) : IO Unit :=
  emitGFCase id (ofUInt64Monic 0x1B 8) a.val b.val
    (a * b).val a⁻¹.val (a * a).val

private def emitGF65KCase (id : String) (a b : GF65K) : IO Unit :=
  emitGFCase id (ofUInt64Monic 0x100B 16) a.val b.val
    (a * b).val a⁻¹.val (a * a).val

end Hex.GF2Emit

def main : IO Unit := do
  for c in Hex.GF2Emit.cases_f2x do Hex.GF2Emit.emitPolyCase c
  -- GF(2^4) over `x^4 + x + 1`: typical pair from a quick sweep.
  Hex.GF2Emit.emitGF16Case "gf2n/n4/typical"
    (Hex.GF2Emit.gf16 0xC) (Hex.GF2Emit.gf16 0x7)
  -- GF(2^8) AES — `0x53 * 0xCA = 1` is the classical AES test pair,
  -- so this case also incidentally cross-checks the AES inverse table.
  Hex.GF2Emit.emitAESCase "gf2n/n8/aes"
    (Hex.GF2Emit.aes 0x53) (Hex.GF2Emit.aes 0xCA)
  -- GF(2^16) over `x^16 + x^12 + x^3 + x + 1`: a Cafe + Babe pair so
  -- corruption of the high-byte reduction shows up in the diff.
  Hex.GF2Emit.emitGF65KCase "gf2n/n16/typical"
    (Hex.GF2Emit.gf65k 0x2A39) (Hex.GF2Emit.gf65k 0xCAFE)
