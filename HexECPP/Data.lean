/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert

public section

/-!
# Raw ECPP certificates

The step contains only a candidate, a short Weierstrass curve, a starting
point, and the inverse transcript for scalar replay. Its child determines the
prime order used by the checker.
-/

namespace Hex.ECPP

/-- A supplied ECPP certificate. The terminal case uses Hex's existing
kernel checked primality certificate. -/
inductive Cert where
  | base (cert : Hex.Nat.PrimeCert)
  | step (n a b x y discrInv : Nat) (inverses : List Nat) (child : Cert)
deriving Repr

/-- The integer certified by a raw certificate. -/
@[expose]
def Cert.subject : Cert → Nat
  | .base cert => cert.subject
  | .step n _ _ _ _ _ _ _ => n

end Hex.ECPP
