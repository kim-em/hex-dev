/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexResultant.SubresultantExt
public meta import HexPolyZGcd.Fast
public import HexResultant.SubresultantExt
public import HexPolyZGcd.Fast

public section

/-!
Deterministic subresultant gcd candidates and constant witnesses.

The terminal polynomial supplies the primitive gcd candidate.  A second
extended chain on its exact cofactors supplies the nonzero constant Bezout
identity required by `CoprimeWitness.constant`.  Both pieces are replayed by
`checkGcd`, so Brown scaling conventions and extended-chain bookkeeping remain
outside the trusted result.
-/

namespace Hex

namespace ZPoly

/-- The first caller-order-sensitive row of the extended chain.  This is a
genuine Bézout row even when one input is zero; it also gives a data-level
initializer from which `prsTerminal` can fold a known-nonempty route without
an option projection or a dummy default. -/
def prsInitial (f h : ZPoly) : DensePoly.SubresultantExt.Entry Int :=
  if f.isZero then (0, 1, h)
  else if h.isZero then (1, 0, f)
  else if f.size < h.size then (0, 1, h)
  else (1, 0, f)

/-- Last extended-subresultant row, computed as a fold from the actual first
row.  The doubly-zero input is handled before this helper is used by
`prsCert`; on every other input `prsInitial` is exactly the chain's first row.
-/
def prsTerminal (f h : ZPoly) : DensePoly.SubresultantExt.Entry Int :=
  (DensePoly.subresultantChainExt f h).foldl (fun _ entry => entry)
    (prsInitial f h)

/-- Primitive-normalized PRS gcd candidate with common integer content
restored. -/
def prsCandidate (f h : ZPoly) : ZPoly :=
  let terminal := prsTerminal (primitivePart f) (primitivePart h)
  let primitive := normalizePrimitiveSign (primitivePart terminal.2.2)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  normalizePrimitiveSign (DensePoly.scale commonContent primitive)

/-- Extract and replay a constant Bezout identity from the terminal extended
chain of two candidate cofactors. -/
def prsCoprimeWitness (f h : ZPoly) : CoprimeWitness :=
  let terminal := prsTerminal f h
  let k := terminal.2.2.coeff 0
  CoprimeWitness.constant terminal.1 terminal.2.1 k

/-- Route 4: a total, deterministic extended-subresultant certificate.  The
only special case is the mathematically degenerate pair `(0, 0)`.  Every
other field is computed directly from the Brown chain and ordinary long
division; correctness is the separate theorem `prsCert_checks` and no proof
is inspected to manufacture runtime data. -/
def prsCert (f h : ZPoly) : GcdCert :=
  if f.isZero && h.isZero then
    { gcd := 0
      cofL := 1
      cofR := 1
      coprime := .constant 1 0 1 }
  else
    let candidate := prsCandidate f h
    let cofL := (DensePoly.divMod f candidate).1
    let cofR := (DensePoly.divMod h candidate).1
    { gcd := candidate
      cofL
      cofR
      coprime := prsCoprimeWitness cofL cofR }

/-- Completeness of the deterministic extended-subresultant fallback. -/
theorem prsCert_checks (f h : ZPoly) : checkGcd f h (prsCert f h) = true := by
  sorry

/-- Checked optional view retained for route-level diagnostics.  Public
dispatch uses total `prsCert` directly. -/
def prsCert? (f h : ZPoly) : Option GcdCert :=
  let cert := prsCert f h
  if checkGcd f h cert then some cert else none

/-! Executable pin for the extended-chain route, including rationally
nonmonic cofactors. -/

#guard
  let common : ZPoly := DensePoly.ofList [2, 1]
  let f := common * DensePoly.ofList [1, 2]
  let h := common * DensePoly.ofList [1, 3]
  let cert := prsCert f h
  cert.gcd == common && checkGcd f h cert

#guard checkGcd (0 : ZPoly) 0 (prsCert 0 0)

end ZPoly

end Hex
