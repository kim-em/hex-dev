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

/-- Last extended-subresultant row.  The doubly-zero chain is empty and has no
synthetic terminal row. -/
def prsTerminal? (f h : ZPoly) :
    Option (DensePoly.SubresultantExt.Entry Int) :=
  (DensePoly.subresultantChainExt f h).back?

/-- Primitive-normalized PRS gcd candidate with common integer content
restored. -/
def prsCandidate? (f h : ZPoly) : Option ZPoly := do
  let terminal ← prsTerminal? (primitivePart f) (primitivePart h)
  let primitive := normalizePrimitiveSign (primitivePart terminal.2.2)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  pure (normalizePrimitiveSign (DensePoly.scale commonContent primitive))

/-- Extract and replay a constant Bezout identity from the terminal extended
chain of two candidate cofactors. -/
def prsCoprimeWitness? (f h : ZPoly) : Option CoprimeWitness := do
  let terminal ← prsTerminal? f h
  let k := terminal.2.2.coeff 0
  pure (CoprimeWitness.constant terminal.1 terminal.2.1 k)

/-- Route 4: a deterministic extended-subresultant certificate.  Absence of
an actual terminal row is propagated to the dispatcher, which classifies the
rational implementation as the audited fallback. -/
def prsCert? (f h : ZPoly) : Option GcdCert :=
  if f.isZero && h.isZero then
    some
      { gcd := 0
        cofL := 1
        cofR := 1
        coprime := .constant 1 0 1 }
  else do
    let candidate ← prsCandidate? f h
    let cofL := (DensePoly.divMod f candidate).1
    let cofR := (DensePoly.divMod h candidate).1
    let coprime ← prsCoprimeWitness? cofL cofR
    pure
      { gcd := candidate
        cofL := cofL
        cofR := cofR
        coprime := coprime }

/-- Completeness of the deterministic extended-subresultant fallback. -/
theorem prsCert_checks {f h : ZPoly} {cert : GcdCert}
    (hcert : prsCert? f h = some cert) : checkGcd f h cert = true := by
  sorry

/-! Executable pin for the extended-chain route, including rationally
nonmonic cofactors. -/

#guard
  let common : ZPoly := DensePoly.ofList [2, 1]
  let f := common * DensePoly.ofList [1, 2]
  let h := common * DensePoly.ofList [1, 3]
  match prsCert? f h with
  | some cert => cert.gcd == common && checkGcd f h cert
  | none => false

#guard
  match prsCert? (0 : ZPoly) 0 with
  | some cert => checkGcd 0 0 cert
  | none => false

-- The raw extended chain for `(0, 0)` is genuinely empty.
#guard (prsTerminal? (0 : ZPoly) 0).isNone

end ZPoly

end Hex
