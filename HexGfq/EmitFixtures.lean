import Hex.Conformance.Emit
import HexGfq.Basic

/-!
JSONL emit driver for the `hex-gfq` packed/generic bridge oracle.

`lake exe hexgfq_emit_fixtures` writes one `gfq_bridge` fixture record
plus eight `result` records per case to `stdout` (or to
`$HEX_FIXTURE_OUTPUT` when set).  The companion oracle driver
`scripts/oracle/gfq_flint.py` reads the same stream and re-runs each
operation through python-flint's `fq_default_ctx` (binary extension
field with the explicit modulus); each op's python-flint result is
compared against both the packed (`HexGF2.GF2n`) and the generic
(`HexGfqField.FiniteField`) Lean answers.  If the two Lean paths
agree on a wrong polynomial, the python-flint comparison still trips
because both `packed_*` and `generic_*` would mismatch.

The `HexConway` Tier-1 table currently exposes a `Conway.SupportedEntry`
plus `Conway.PackedGF2Entry` only at extension degree `(2, 1)`, which
makes the committed bridge trivial.  Following the
`HexGfq/CrossCheck.lean` pattern, this driver exercises the bridge at
larger binary degrees by constructing ad-hoc moduli with `sorry`'d
irreducibility witnesses; the operations themselves still execute and
their outputs feed the python-flint cross-check.

The bridge is binary-only by design — `HexGF2.GF2n` packs `F_2`
extensions into a single `UInt64` and there is no packed counterpart
for odd characteristic.  Odd-characteristic finite-field cross-checks
live in `HexGfqField`'s separate oracle.

Cases cover `(p, n)` ∈ `{(2, 4), (2, 8), (2, 16)}` with hand-picked
known irreducibles (`x^4+x+1`, the AES `x^8+x^4+x^3+x+1`, and the
CRC-16-CCITT `x^16+x^12+x^3+x+1`).  For each case we emit:

* `packed_add`   / `generic_add`   — `(a + b) mod m` over `F_2[x]`;
* `packed_mul`   / `generic_mul`   — `(a * b) mod m` over `F_2[x]`;
* `packed_inv`   / `generic_inv`   — `a⁻¹ mod m` (cases keep `a ≠ 0`);
* `packed_frob`  / `generic_frob`  — `a^p` (binary squaring).

Every emitted polynomial value is the canonical ascending coefficient
list with trailing zeros trimmed, matching python-flint's
`nmod_poly.coeffs()` form after a `_trim_zeros` pass.
-/

namespace Hex.GfqEmit

open Hex.Conformance.Emit
open Hex
open Hex.GFqField

private def lib : String := "HexGfq"

private instance bounds2 : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private def primeTwo : Hex.Nat.Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · exact Or.inr rfl

local instance instPrimeModulusTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime primeTwo

/-- Mask the low `n` bits of `w`, matching the canonical packed-form
representative for an extension of degree `n`. -/
private def maskBits (w : UInt64) (n : Nat) : UInt64 :=
  if n = 0 then
    0
  else if 64 ≤ n then
    w
  else
    w &&& (((1 : UInt64) <<< n.toUInt64) - 1)

/-- Bit `i` of `w` becomes coefficient `i` of the generic `FpPoly 2`
representative. -/
private def wordToPoly2 (w : UInt64) (n : Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (((List.range n).map fun i =>
    if (((w >>> i.toUInt64) &&& 1) = 0) then
      (0 : ZMod64 2)
    else
      (1 : ZMod64 2)).toArray)

/-- Coefficient-list serialisation of a packed word truncated to `n`
bits, with trailing zeros trimmed. -/
private def packedWordToCoeffs (w : UInt64) (n : Nat) : List Int := Id.run do
  let mut acc : List Int := []
  let mut hi : Nat := 0
  for i in [0:n] do
    let bit := ((w >>> i.toUInt64) &&& 1).toNat
    if bit ≠ 0 then
      hi := i + 1
    acc := acc.concat (Int.ofNat bit)
  pure (acc.take hi)

/-- Coefficient-list serialisation of a generic `FpPoly 2`
representative.  `FpPoly.ofCoeffs` already trims trailing zeros so the
underlying array is canonical. -/
private def fp2Coeffs (f : FpPoly 2) : List Int :=
  f.toArray.toList.map (fun c => Int.ofNat c.toNat)

/-! ## Per-degree case bundles

Each namespace fixes a known irreducible packed modulus, packages the
matching generic `FpPoly 2` modulus via `Conway.packedGF2FpPoly`, and
provides `sorry`'d irreducibility plus positive-degree witnesses for
both representations.  This mirrors `HexGfq/CrossCheck.lean`.
-/

namespace N4

/-- Irreducible polynomial `x^4 + x + 1`. -/
private def lower : UInt64 := 0x3
private def n : Nat := 4

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  sorry

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  sorry

private abbrev Packed : Type :=
  GF2n n lower (by decide) (by decide) packed_irr

private abbrev Generic : Type :=
  GFqField.FiniteField genericMod generic_pos primeTwo generic_irr

private def packedOf (w : UInt64) : Packed :=
  GF2n.reduce (maskBits w n)

private def genericOf (w : UInt64) : Generic :=
  GFqField.ofPoly genericMod generic_pos primeTwo generic_irr (wordToPoly2 w n)

private def packedCoeffs (x : Packed) : List Int :=
  packedWordToCoeffs x.val n

private def genericCoeffs (x : Generic) : List Int :=
  fp2Coeffs (GFqField.repr x)

private structure Case where
  id : String
  a  : UInt64
  b  : UInt64

private def cases : List Case :=
  [ { id := "p2/n4/typical-1", a := 0xA, b := 0x5 }
  , { id := "p2/n4/typical-2", a := 0xC, b := 0x9 }
  , { id := "p2/n4/edge-one",  a := 0x1, b := 0xF } ]

private def emitCase (c : Case) : IO Unit := do
  let a := maskBits c.a n
  let b := maskBits c.b n
  let pa : Packed  := packedOf a
  let ga : Generic := genericOf a
  let pb : Packed  := packedOf b
  let gb : Generic := genericOf b
  emitGfqBridgeFixture lib c.id 2
    (fp2Coeffs genericMod)
    (packedWordToCoeffs a n)
    (packedWordToCoeffs b n)
  emitResult lib c.id "packed_add"   (polyValue (packedCoeffs  (pa + pb)))
  emitResult lib c.id "generic_add"  (polyValue (genericCoeffs (ga + gb)))
  emitResult lib c.id "packed_mul"   (polyValue (packedCoeffs  (pa * pb)))
  emitResult lib c.id "generic_mul"  (polyValue (genericCoeffs (ga * gb)))
  emitResult lib c.id "packed_inv"   (polyValue (packedCoeffs  (pa⁻¹)))
  emitResult lib c.id "generic_inv"  (polyValue (genericCoeffs (ga⁻¹)))
  emitResult lib c.id "packed_frob"  (polyValue (packedCoeffs  (pa ^ (2 : Nat))))
  emitResult lib c.id "generic_frob" (polyValue (genericCoeffs (GFqField.frob ga)))

end N4

namespace N8

/-- AES (Rijndael) irreducible polynomial `x^8 + x^4 + x^3 + x + 1`. -/
private def lower : UInt64 := 0x1B
private def n : Nat := 8

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  sorry

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  sorry

private abbrev Packed : Type :=
  GF2n n lower (by decide) (by decide) packed_irr

private abbrev Generic : Type :=
  GFqField.FiniteField genericMod generic_pos primeTwo generic_irr

private def packedOf (w : UInt64) : Packed :=
  GF2n.reduce (maskBits w n)

private def genericOf (w : UInt64) : Generic :=
  GFqField.ofPoly genericMod generic_pos primeTwo generic_irr (wordToPoly2 w n)

private def packedCoeffs (x : Packed) : List Int :=
  packedWordToCoeffs x.val n

private def genericCoeffs (x : Generic) : List Int :=
  fp2Coeffs (GFqField.repr x)

private structure Case where
  id : String
  a  : UInt64
  b  : UInt64

private def cases : List Case :=
  [ { id := "p2/n8/typical-1", a := 0x53, b := 0xCA }
  , { id := "p2/n8/typical-2", a := 0xA9, b := 0x37 }
  , { id := "p2/n8/edge-low",  a := 0x01, b := 0xFE } ]

private def emitCase (c : Case) : IO Unit := do
  let a := maskBits c.a n
  let b := maskBits c.b n
  let pa : Packed  := packedOf a
  let ga : Generic := genericOf a
  let pb : Packed  := packedOf b
  let gb : Generic := genericOf b
  emitGfqBridgeFixture lib c.id 2
    (fp2Coeffs genericMod)
    (packedWordToCoeffs a n)
    (packedWordToCoeffs b n)
  emitResult lib c.id "packed_add"   (polyValue (packedCoeffs  (pa + pb)))
  emitResult lib c.id "generic_add"  (polyValue (genericCoeffs (ga + gb)))
  emitResult lib c.id "packed_mul"   (polyValue (packedCoeffs  (pa * pb)))
  emitResult lib c.id "generic_mul"  (polyValue (genericCoeffs (ga * gb)))
  emitResult lib c.id "packed_inv"   (polyValue (packedCoeffs  (pa⁻¹)))
  emitResult lib c.id "generic_inv"  (polyValue (genericCoeffs (ga⁻¹)))
  emitResult lib c.id "packed_frob"  (polyValue (packedCoeffs  (pa ^ (2 : Nat))))
  emitResult lib c.id "generic_frob" (polyValue (genericCoeffs (GFqField.frob ga)))

end N8

namespace N16

/-- CRC-16-CCITT irreducible polynomial `x^16 + x^12 + x^3 + x + 1`. -/
private def lower : UInt64 := 0x100B
private def n : Nat := 16

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  sorry

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  sorry

private abbrev Packed : Type :=
  GF2n n lower (by decide) (by decide) packed_irr

private abbrev Generic : Type :=
  GFqField.FiniteField genericMod generic_pos primeTwo generic_irr

private def packedOf (w : UInt64) : Packed :=
  GF2n.reduce (maskBits w n)

private def genericOf (w : UInt64) : Generic :=
  GFqField.ofPoly genericMod generic_pos primeTwo generic_irr (wordToPoly2 w n)

private def packedCoeffs (x : Packed) : List Int :=
  packedWordToCoeffs x.val n

private def genericCoeffs (x : Generic) : List Int :=
  fp2Coeffs (GFqField.repr x)

private structure Case where
  id : String
  a  : UInt64
  b  : UInt64

private def cases : List Case :=
  [ { id := "p2/n16/typical-1", a := 0x4321, b := 0xBEEF }
  , { id := "p2/n16/typical-2", a := 0xCAFE, b := 0x1234 }
  , { id := "p2/n16/edge-low",  a := 0x0003, b := 0xFFFE } ]

private def emitCase (c : Case) : IO Unit := do
  let a := maskBits c.a n
  let b := maskBits c.b n
  let pa : Packed  := packedOf a
  let ga : Generic := genericOf a
  let pb : Packed  := packedOf b
  let gb : Generic := genericOf b
  emitGfqBridgeFixture lib c.id 2
    (fp2Coeffs genericMod)
    (packedWordToCoeffs a n)
    (packedWordToCoeffs b n)
  emitResult lib c.id "packed_add"   (polyValue (packedCoeffs  (pa + pb)))
  emitResult lib c.id "generic_add"  (polyValue (genericCoeffs (ga + gb)))
  emitResult lib c.id "packed_mul"   (polyValue (packedCoeffs  (pa * pb)))
  emitResult lib c.id "generic_mul"  (polyValue (genericCoeffs (ga * gb)))
  emitResult lib c.id "packed_inv"   (polyValue (packedCoeffs  (pa⁻¹)))
  emitResult lib c.id "generic_inv"  (polyValue (genericCoeffs (ga⁻¹)))
  emitResult lib c.id "packed_frob"  (polyValue (packedCoeffs  (pa ^ (2 : Nat))))
  emitResult lib c.id "generic_frob" (polyValue (genericCoeffs (GFqField.frob ga)))

end N16

end Hex.GfqEmit

def main : IO Unit := do
  for c in Hex.GfqEmit.N4.cases  do Hex.GfqEmit.N4.emitCase  c
  for c in Hex.GfqEmit.N8.cases  do Hex.GfqEmit.N8.emitCase  c
  for c in Hex.GfqEmit.N16.cases do Hex.GfqEmit.N16.emitCase c
