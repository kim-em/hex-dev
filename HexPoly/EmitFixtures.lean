import Hex.Conformance.Emit
import HexPoly

/-!
JSONL emit driver for the `hex-poly` oracle.

`lake exe hexpoly_emit_fixtures` writes one JSONL record per fixture
followed by one `result` record per Lean-side computed value to
`stdout` (or to `$HEX_FIXTURE_OUTPUT` when set).  The companion
oracle driver `scripts/oracle/poly_flint.py` reads the same stream
and re-runs each operation through python-flint for cross-check.

Coverage:

* `mul` over `DensePoly Int` at degrees 8 / 16 / 32 / 64, sparse and
  dense, with coefficients drawn deterministically from an LCG modulo
  ~2^16 so the committed JSONL is reproducible across machines.
* `divmod` over `DensePoly Int` at degrees 8 and 16 with exact-division
  fixtures (dividend constructed as `quotient * divisor`) so the Lean
  result matches `flint.fmpz_poly`'s `divrem` exactly.
* `gcd` over `DensePoly Rat` at degrees 8 / 16 / 32: the input
  polynomial pairs are constructed as `g * a` and `g * b` for known
  factors `g`, `a`, `b` (via Lean multiplication), then cast to
  rational coefficients before invoking `gcd`.  The Lean gcd is only
  determined up to a rational scalar associate, so the oracle compares
  the monic associate of Lean's value to `flint.fmpq_poly.gcd` (which
  is monic by construction).  Cross-checking gcd over `Int` directly
  is not viable: `Hex.DensePoly Int.gcd` runs Euclidean reduction with
  truncating integer division, so it does not match `fmpz_poly.gcd`'s
  primitive associate even on inputs constructed from a known gcd.
-/

namespace Hex.PolyEmit

open Hex.Conformance.Emit
open Hex.DensePoly

private def lib : String := "HexPoly"

/-! Deterministic polynomial generators.

LCG borrowed from glibc-style `rand`:
`state ↦ state * 1103515245 + 12345 (mod 2^32)`.
We sample the low 16 bits and re-centre to roughly `[-2^15, 2^15)` so
the emitted coefficients stay within `~2^16` per the issue.
-/

/-- Convert a 16-bit LCG sample into a signed coefficient. -/
private def sample (state : UInt32) : Int :=
  let raw : Int := Int.ofNat (state.toNat % 65536)
  raw - 32768

/-- Generate `count` deterministic coefficients starting from `seed`.
The trailing element (highest-degree coefficient) is forced nonzero by
post-processing so the polynomial has the requested degree. -/
private def lcgCoeffs (seed : UInt32) (count : Nat) : List Int := Id.run do
  let mut s : UInt32 := seed
  let mut out : Array Int := Array.mkEmpty count
  for _ in [:count] do
    s := s * 1103515245 + 12345
    out := out.push (sample s)
  -- Force a nonzero leading coefficient when possible.
  if out.size > 0 then
    let lastIdx := out.size - 1
    if out[lastIdx]! = 0 then
      out := out.set! lastIdx (1 : Int)
  return out.toList

/-- Dense polynomial of given degree, generated from an LCG seed. -/
private def densePoly (seed : UInt32) (deg : Nat) : DensePoly Int :=
  ofCoeffs (lcgCoeffs seed (deg + 1)).toArray

/-- Sparse polynomial: only every `stride`-th coefficient is nonzero. -/
private def sparsePoly (seed : UInt32) (deg stride : Nat) : DensePoly Int := Id.run do
  let dense := lcgCoeffs seed (deg + 1)
  let mut out : Array Int := Array.mkEmpty (deg + 1)
  for i in [:deg + 1] do
    let c := dense[i]?.getD 0
    if i % stride == 0 ∨ i = deg then
      out := out.push c
    else
      out := out.push 0
  return ofCoeffs out

/-! `mul` fixtures over `DensePoly Int`. -/

private structure MulCase where
  id     : String
  left   : DensePoly Int
  right  : DensePoly Int

private def mulCases : List MulCase := [
  -- Bootstrap small cases (kept for backwards-compatible oracle coverage).
  { id := "mul/typical",
    left  := ofCoeffs #[3, 0, -2],
    right := ofCoeffs #[-1, 5, 2] },
  { id := "mul/byOne",
    left  := ofCoeffs #[3, 0, -2],
    right := ofCoeffs #[1] },
  { id := "mul/zero",
    left  := ofCoeffs #[],
    right := ofCoeffs #[0, 4, 0, -5] },
  { id := "mul/sparseShift",
    left  := ofCoeffs #[0, 4, 0, -5],
    right := ofCoeffs #[0, 0, 0, -2] },
  -- Larger fixtures at the issue-specified degrees.
  { id := "mul/dense8",
    left  := densePoly 0x1001 8,
    right := densePoly 0x2002 8 },
  { id := "mul/sparse8",
    left  := sparsePoly 0x3003 8 3,
    right := sparsePoly 0x4004 8 4 },
  { id := "mul/dense16",
    left  := densePoly 0x5005 16,
    right := densePoly 0x6006 16 },
  { id := "mul/sparse16",
    left  := sparsePoly 0x7007 16 5,
    right := sparsePoly 0x8008 16 7 },
  { id := "mul/dense32",
    left  := densePoly 0x9009 32,
    right := densePoly 0xA00A 32 },
  { id := "mul/sparse32",
    left  := sparsePoly 0xB00B 32 11,
    right := sparsePoly 0xC00C 32 13 },
  { id := "mul/dense64",
    left  := densePoly 0xD00D 64,
    right := densePoly 0xE00E 64 },
  { id := "mul/sparse64",
    left  := sparsePoly 0xF00F 64 17,
    right := sparsePoly 0x10010 64 19 }
]

private def emitMulCase (c : MulCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left")  c.left.toArray.toList
  emitPolyFixture lib (c.id ++ "/right") c.right.toArray.toList
  let prod : DensePoly Int := c.left * c.right
  emitResult lib c.id "mul" (polyValue prod.toArray.toList)

/-! `divmod` fixtures over `DensePoly Int`.

We construct each case by choosing a `quotient` and `divisor` and
emitting `dividend = quotient * divisor`.  Lean's integer `divMod`
recovers the original `(quotient, 0)` exactly, matching the
`flint.fmpz_poly` divrem semantics. -/

private structure DivModCase where
  id        : String
  quotient  : DensePoly Int
  divisor   : DensePoly Int

private def divModCases : List DivModCase := [
  -- Bootstrap small cases.
  { id := "divmod/exact",
    quotient := ofCoeffs #[3, 0, -2],
    divisor  := ofCoeffs #[-1, 5, 2] },
  { id := "divmod/byMonic",
    quotient := ofCoeffs #[-1, 1, 1],
    divisor  := ofCoeffs #[-1, 1] },
  -- Issue-specified larger fixtures.
  { id := "divmod/dense8",
    quotient := densePoly 0x11011 8,
    divisor  := densePoly 0x12012 4 },
  { id := "divmod/monic8",
    quotient := densePoly 0x13013 8,
    -- Force monic divisor by setting the trailing coeff to 1.
    divisor  := ofCoeffs ((lcgCoeffs 0x14014 4).toArray.push 1) },
  { id := "divmod/dense16",
    quotient := densePoly 0x15015 16,
    divisor  := densePoly 0x16016 6 },
  { id := "divmod/monic16",
    quotient := densePoly 0x17017 16,
    divisor  := ofCoeffs ((lcgCoeffs 0x18018 8).toArray.push 1) }
]

private def emitDivModCase (c : DivModCase) : IO Unit := do
  let dividend : DensePoly Int := c.quotient * c.divisor
  emitPolyFixture lib (c.id ++ "/dividend") dividend.toArray.toList
  emitPolyFixture lib (c.id ++ "/divisor")  c.divisor.toArray.toList
  let (q, r) := divMod dividend c.divisor
  emitResult lib c.id "divmod" (divModValue q.toArray.toList r.toArray.toList)

/-! `gcd` fixtures over `DensePoly Rat`.

Each fixture is constructed as `left = g * a`, `right = g * b` (over
`Int`), then cast to `Rat` for the gcd run.  The cross-check is up to
the monic associate, performed on the oracle side.

The committed JSONL emits the input polynomials as their `Int`
preimages and the gcd value as parallel `num`/`den` arrays.  This keeps
the fixture file diffable while still capturing the rational result. -/

private structure GcdCase where
  id     : String
  g      : DensePoly Int
  a      : DensePoly Int
  b      : DensePoly Int

private def divisor4 (seed : UInt32) : DensePoly Int :=
  -- Helper: build a degree-4 monic polynomial from an LCG seed.  Monic
  -- factors keep the integer-side multiplication well-conditioned.
  ofCoeffs ((lcgCoeffs seed 4).toArray.push 1)

private def gcdCases : List GcdCase := [
  { id := "gcd/deg8",
    g := divisor4 0x21021,
    a := densePoly 0x22022 4,
    b := densePoly 0x23023 4 },
  { id := "gcd/deg16",
    g := divisor4 0x24024,
    a := densePoly 0x25025 12,
    b := densePoly 0x26026 12 },
  { id := "gcd/deg32",
    -- Larger common factor for the deg-32 case.
    g := ofCoeffs ((lcgCoeffs 0x27027 8).toArray.push 1),
    a := densePoly 0x28028 24,
    b := densePoly 0x29029 24 }
]

private def toRatPoly (p : DensePoly Int) : DensePoly Rat :=
  ofCoeffs (p.toArray.map (fun (c : Int) => (Rat.ofInt c)))

private def emitGcdCase (c : GcdCase) : IO Unit := do
  let left  : DensePoly Int := c.g * c.a
  let right : DensePoly Int := c.g * c.b
  emitPolyFixture lib (c.id ++ "/left")  left.toArray.toList
  emitPolyFixture lib (c.id ++ "/right") right.toArray.toList
  let leftRat  : DensePoly Rat := toRatPoly left
  let rightRat : DensePoly Rat := toRatPoly right
  let g : DensePoly Rat := gcd leftRat rightRat
  emitResult lib c.id "gcd" (polyRatValue g.toArray.toList)

end Hex.PolyEmit

def main : IO Unit := do
  for c in Hex.PolyEmit.mulCases    do Hex.PolyEmit.emitMulCase    c
  for c in Hex.PolyEmit.divModCases do Hex.PolyEmit.emitDivModCase c
  for c in Hex.PolyEmit.gcdCases    do Hex.PolyEmit.emitGcdCase    c
