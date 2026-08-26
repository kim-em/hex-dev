/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqField.Operations
public import HexBerlekamp.RabinSoundness

public section

/-!
A committed example field, `GF(5⁴)` presented as `𝔽₅[x] / (x⁴ + 2)`.

Forming a `FiniteField` needs an irreducibility proof, and producing one means
writing a Rabin certificate and replaying it in the kernel, which costs a
recursion-depth and heartbeat bump. That is a poor thing to make every reader
of an example do, so one such field is committed here: the manual's worked
examples and the conformance drivers cite `modulus_irreducible` instead of
rebuilding a certificate each time.

This is example data, not a general facility. A caller with their own modulus
uses `HexBerlekamp` directly; a caller who wants a canonical field of a given
order uses `hex-gfq`'s Conway constructors.
-/

namespace Hex

namespace GFqField

namespace Example

open Hex.GFqField

/-- Word bounds for the example characteristic. -/
instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

/-- The example characteristic is prime. -/
theorem prime_five : Hex.Nat.Prime 5 := by decide

instance : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime prime_five

/-- A monic degree-four modulus `x⁴ + 2` over `𝔽₅`, committed with its
irreducibility certificate so that a small `GF(5⁴)` is available without
hand-writing one. Used by the manual's worked examples and by conformance. -/
def modulus : FpPoly 5 := #p[2, 0, 0, 0, 1]

/-- The example modulus is nonconstant, which is what the field wrapper needs
beside irreducibility. -/
theorem modulus_pos_degree :
    0 < FpPoly.degree modulus := by decide

/-- The example modulus is monic. -/
theorem modulus_monic :
    DensePoly.Monic modulus := by rfl

private theorem maxProperDiv_4 :
    Berlekamp.maximalProperDivisors 4 = [2] := by
  decide

/-- Rabin irreducibility certificate for the example modulus: the Frobenius
pow chain and the Bézout witness the kernel replays. -/
def cert :
    Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 4
  powChain := #[
    #p[0, 1],
    #p[0, 3],
    #p[0, 4],
    #p[0, 2],
    #p[0, 1]
  ]
  bezout := #[
    { left := #p[3]
      right := #p[0, 0, 0, 4] }
  ]

set_option maxRecDepth 131072 in
set_option maxHeartbeats 8000000 in
/-- The committed certificate passes the kernel-reducible checker. The heartbeat
and recursion bumps live here rather than at every call site: replaying a
certificate is the expensive step, and doing it once means downstream users of
`modulus_irreducible` pay nothing. -/
theorem cert_check :
    Berlekamp.checkIrreducibilityCertificateLinear
        modulus modulus_monic cert = true := by
  decide

/-- The example modulus is irreducible, by routing the checked certificate
through Rabin soundness. -/
theorem modulus_irreducible :
    FpPoly.Irreducible modulus :=
  have h :=
    Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      modulus modulus_monic cert cert_check
  Berlekamp.rabinTest_imp_irreducible
    modulus modulus_monic h

/-- The example field `GF(5⁴)`. -/
abbrev F : Type :=
  FiniteField modulus modulus_pos_degree prime_five modulus_irreducible

/-- Inject a polynomial into the example field by reducing it. -/
def ofPoly (f : FpPoly 5) : F :=
  GFqField.ofPoly modulus modulus_pos_degree prime_five modulus_irreducible f

end Example

end GFqField

end Hex
