/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateBasis

public section

namespace Hex.Groebner

/-- A complete accepted basis tied to its original generators, field and order.
The constructor requires actual Boolean acceptance, never an unchecked flag. -/
structure CheckedBasis where
  private mk ::
  context : Context
  generators : Array Certificate.Polynomial
  polynomials : Array Certificate.Polynomial
  certificate : Certificate.Basis
  forwardNodes : Nat
  backwardNodes : Nat
  forward_size : forwardNodes = certificate.forward.nodes.length
  backward_size : backwardNodes = certificate.backward.nodes.length
  accepted : checkBasis context generators polynomials certificate = true

/-- Import a literal certificate with a proof of independent acceptance. This
performs no candidate computation; bounded native verification can use the same
constructor after charging replay and proving its Boolean branch. -/
def CheckedBasis.ofCertificate (context : Context) (generators basis : Array Certificate.Polynomial)
    (certificate : Certificate.Basis) (accepted : checkBasis context generators basis certificate = true) :
    CheckedBasis :=
  ⟨context, generators, basis, certificate, certificate.forward.nodes.length, certificate.backward.nodes.length, rfl, rfl, accepted⟩

end Hex.Groebner
