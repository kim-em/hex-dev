/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert

public section

/-!
# Data for elliptic curve primality proofs

A certificate for `n` either uses HexPrimality's existing certificates or
records an elliptic curve `y² = x³ + a*x + b` modulo `n` and a finite point
`Q = (x,y)`. A nested certificate proves a smaller integer `q` prime. The
checker verifies that `q • Q` is infinity and that `q` is large enough to
exclude every possible small prime divisor of `n`, using Hasse's bound.

The extra numbers justify divisions modulo `n`: one is an inverse of
`4*a³ + 27*b²`, and the list supplies inverses for the point additions.
Every inverse is verified by multiplication. No claimed curve order is
trusted. The primality implication is proved in `HexECPPTheory`.
-/

namespace Hex.ECPP

/-- Mathematical data to prove an integer prime by elliptic curve primality
proving (ECPP). The data must pass `Hex.ECPP.check` before it proves anything.

`base cert` uses an existing HexPrimality certificate. In
`step n a b x y discrInv inverses child`, the curve is
`y² = x³ + a*x + b` modulo `n`, the point is `(x,y)`, and `child` certifies
the prime scalar used to multiply the point. `discrInv` witnesses that
`4*a³ + 27*b²` is invertible; `inverses` justifies the divisions in that
scalar multiplication. The checker also verifies the curve equation and
the strict size condition needed for Hasse's bound. -/
inductive Cert where
  | base (cert : Hex.Nat.PrimeCert)
  | step (n a b x y discrInv : Nat) (inverses : List Nat) (child : Cert)
deriving Repr

/-- The integer whose primality this certificate is intended to establish.
Its primality follows only after the certificate passes the checker. -/
@[expose]
def Cert.subject : Cert → Nat
  | .base cert => cert.subject
  | .step n _ _ _ _ _ _ _ => n

end Hex.ECPP
