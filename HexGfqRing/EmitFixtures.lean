import Hex.Conformance.Emit
import HexGfqRing.Operations

/-!
JSONL emit driver for the `hex-gfq-ring` oracle.

`lake exe hexgfqring_emit_fixtures` writes one `gfqring` fixture
record plus four `result` records per case to `stdout` (or to
`$HEX_FIXTURE_OUTPUT` when set).  The companion oracle driver
`scripts/oracle/gfqring_flint.py` reads the same stream and re-runs
each operation through python-flint's `nmod_poly(p)` plus explicit
polynomial reduction by the modulus.

Cases cover `F_p[x] / (m(x))` at `p ∈ {5, 7, 11}` and modulus degree
`d ∈ {2, 4, 6}`.  For each case we emit:

* `add`    — coefficients of `(a + b) mod m` over `F_p`;
* `mul`    — coefficients of `(a * b) mod m` over `F_p`;
* `nsmul`  — coefficients of `(n · a) mod m` over `F_p` for the
  scalar `n` carried by the fixture record;
* `reduce` — coefficients of `c mod m` over `F_p`, where `c` is an
  unreduced polynomial of degree at least the modulus degree.

The `gfqring` fixture record carries every input the oracle needs
(`p`, `modulus`, `a`, `b`, `c`, `n`) so that each oracle step is
self-contained.
-/

namespace Hex.GFqRingEmit

open Hex.Conformance.Emit
open Hex
open Hex.GFqRing

private def lib : String := "HexGfqRing"

private instance bounds5 : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance bounds7 : ZMod64.Bounds 7 := ⟨by decide, by decide⟩
private instance bounds11 : ZMod64.Bounds 11 := ⟨by decide, by decide⟩

/-- Lift an `FpPoly p` coefficient list to `List Int` via the canonical
representative in `[0, p)`.  Used for fixture emission and result
serialisation. -/
private def liftCoeffs {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Int :=
  f.toArray.toList.map (fun c => Int.ofNat c.toNat)

/-- Build an `FpPoly p` from a coefficient list (constant term first). -/
private def mkPoly {p : Nat} [ZMod64.Bounds p] (coeffs : List Nat) : FpPoly p :=
  FpPoly.ofCoeffs (coeffs.toArray.map (fun n => ZMod64.ofNat p n))

/-- Description of a single emitted case: prime `p`, ascending
modulus / `a` / `b` / `c` coefficient lists, and the scalar `n`.

`a` and `b` are required to be reduced (degree strictly less than the
modulus degree); `c` is intentionally unreduced so that the `reduce`
op exercises a non-trivial division.  Per-case correctness comes from
`emitCaseAt` invoking `reduceMod` on the Lean-side products before
emission. -/
private structure Case where
  id      : String
  p       : Nat
  modulus : List Nat
  a       : List Nat
  b       : List Nat
  c       : List Nat
  n       : Nat

private def cases5 : List Case :=
  [ -- d=2: modulus x^2 + 1 over F_5 (reducible: x^2 + 1 = (x+2)(x+3)).
    -- a = 2 + 3x, b = 4 + x, c = 1 + 2x + 3x^2 + x^3 (deg ≥ 2), n = 7.
    { id      := "p5/d2/typical"
      p       := 5
      modulus := [1, 0, 1]
      a       := [2, 3]
      b       := [4, 1]
      c       := [1, 2, 3, 1]
      n       := 7 }
    -- d=4: modulus x^4 + 2 over F_5 (matches HexGfqRing.Conformance).
    -- Reduction rule: x^4 ≡ -2 ≡ 3 (mod 5).
  , { id      := "p5/d4/typical"
      p       := 5
      modulus := [2, 0, 0, 0, 1]
      a       := [2, 3]
      b       := [4, 1, 0, 1]
      c       := [0, 0, 0, 0, 0, 1]   -- x^5 (reduces to 3x).
      n       := 8 }
    -- d=4 edge: a = 0, b = 1 + 2x + 3x^2 + 4x^3, exercises the
    -- zero-operand branches of add/mul/nsmul.  `c` is degree 5 to
    -- still exercise the reduction loop.
  , { id      := "p5/d4/edge-zero"
      p       := 5
      modulus := [2, 0, 0, 0, 1]
      a       := []
      b       := [1, 2, 3, 4]
      c       := [3, 1, 4, 1, 0, 2]
      n       := 0 }
  ]

private def cases7 : List Case :=
  [ -- d=2: modulus x^2 + 1 over F_7 (irreducible; -1 is a non-square mod 7).
    { id      := "p7/d2/typical"
      p       := 7
      modulus := [1, 0, 1]
      a       := [3, 5]
      b       := [6, 2]
      c       := [4, 0, 6, 1]
      n       := 11 }
    -- d=4: modulus x^4 + 3 over F_7.
  , { id      := "p7/d4/typical"
      p       := 7
      modulus := [3, 0, 0, 0, 1]
      a       := [1, 2, 4, 6]
      b       := [5, 3, 0, 1]
      c       := [1, 0, 0, 0, 1, 0, 2]
      n       := 13 }
  ]

private def cases11 : List Case :=
  [ -- d=2: modulus x^2 + 7 over F_11 (-7 ≡ 4 = 2^2, so reducible
    -- but ring conformance is independent of irreducibility).
    { id      := "p11/d2/typical"
      p       := 11
      modulus := [7, 0, 1]
      a       := [4, 9]
      b       := [10, 3]
      c       := [1, 5, 8, 2, 7]
      n       := 23 }
    -- d=6: modulus x^6 + 5 over F_11.
  , { id      := "p11/d6/typical"
      p       := 11
      modulus := [5, 0, 0, 0, 0, 0, 1]
      a       := [3, 7, 1, 9, 0, 4]
      b       := [10, 6, 2, 0, 8, 1]
      c       := [9, 4, 7, 2, 6, 0, 3, 5, 1]
      n       := 17 }
  ]

/-- Run one case at a fixed `p` after the `[ZMod64.Bounds p]` instance
has been resolved by the dispatchers below.  Builds the polynomials,
constructs canonical quotient elements, and emits one fixture record
plus the four operation results. -/
private def emitCaseAt (p : Nat) [ZMod64.Bounds p] (c : Case)
    (hpos : 0 < FpPoly.degree (mkPoly (p := p) c.modulus)) : IO Unit := do
  let m       : FpPoly p := mkPoly c.modulus
  let aPoly   : FpPoly p := mkPoly c.a
  let bPoly   : FpPoly p := mkPoly c.b
  let cPoly   : FpPoly p := mkPoly c.c
  let xa : PolyQuotient m hpos := ofPoly m hpos aPoly
  let xb : PolyQuotient m hpos := ofPoly m hpos bPoly
  emitGfqRingFixture lib c.id (Int.ofNat p)
    (liftCoeffs m) (liftCoeffs (repr xa)) (liftCoeffs (repr xb))
    (liftCoeffs cPoly) (Int.ofNat c.n)
  emitResult lib c.id "add"    (polyValue (liftCoeffs (repr (xa + xb))))
  emitResult lib c.id "mul"    (polyValue (liftCoeffs (repr (xa * xb))))
  emitResult lib c.id "nsmul"  (polyValue (liftCoeffs (repr (nsmul c.n xa))))
  emitResult lib c.id "reduce" (polyValue (liftCoeffs (reduceMod m cPoly)))

private def emitCase5 (c : Case) : IO Unit := do
  if c.p ≠ 5 then return ()
  let m : FpPoly 5 := mkPoly c.modulus
  -- All cases at this dispatcher have a degree ≥ 2 modulus.
  if hpos : 0 < FpPoly.degree m then
    emitCaseAt 5 c hpos
  else return ()

private def emitCase7 (c : Case) : IO Unit := do
  if c.p ≠ 7 then return ()
  let m : FpPoly 7 := mkPoly c.modulus
  if hpos : 0 < FpPoly.degree m then
    emitCaseAt 7 c hpos
  else return ()

private def emitCase11 (c : Case) : IO Unit := do
  if c.p ≠ 11 then return ()
  let m : FpPoly 11 := mkPoly c.modulus
  if hpos : 0 < FpPoly.degree m then
    emitCaseAt 11 c hpos
  else return ()

end Hex.GFqRingEmit

def main : IO Unit := do
  for c in Hex.GFqRingEmit.cases5  do Hex.GFqRingEmit.emitCase5  c
  for c in Hex.GFqRingEmit.cases7  do Hex.GFqRingEmit.emitCase7  c
  for c in Hex.GFqRingEmit.cases11 do Hex.GFqRingEmit.emitCase11 c
