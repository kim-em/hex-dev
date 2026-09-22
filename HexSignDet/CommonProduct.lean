/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Produce
public import HexPoly.Euclid

public section

namespace Hex.SignDet

/-- Literal identities for a common root polynomial. Squarefreeness belongs
to its separately checked prepared domain. The factor need not be a particular
normalization of the gcd: the three division identities certify the root union. -/
structure CommonProduct (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  context : Ctx
  left : DensePoly E
  right : DensePoly E
  head : DensePoly E
  factor : DensePoly E
  leftQuotient : DensePoly E
  rightQuotient : DensePoly E

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [Add E] [Sub E] [Mul E]

/-- Exact context/head bindings use literal equality. Polynomial identities
use zero differences so equivalent noncanonical coefficients are accepted. -/
@[expose] def CommonProduct.check (context : Ctx) (p q : DensePoly E)
    (c : CommonProduct E Ctx) : Bool :=
  decide (c.context = context ∧ c.left = p ∧ c.right = q) &&
  SignedRemainderChain.subIsZero (p * q) (c.head * c.factor) &&
  SignedRemainderChain.subIsZero c.head (p * c.leftQuotient) &&
  SignedRemainderChain.subIsZero c.head (q * c.rightQuotient)

theorem CommonProduct.check_eq {context : Ctx} {p q : DensePoly E}
    {c : CommonProduct E Ctx} (h : c.check context p q = true) :
    (c.context = context ∧ c.left = p ∧ c.right = q) ∧
    SignedRemainderChain.subIsZero (p * q) (c.head * c.factor) = true ∧
    SignedRemainderChain.subIsZero c.head (p * c.leftQuotient) = true ∧
    SignedRemainderChain.subIsZero c.head (q * c.rightQuotient) = true := by
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

variable [One E] [Div E]

/-- Compute the common product using the shared polynomial gcd/division
kernels, retaining quotients for independent replay. A prepared-domain check
must still validate squarefreeness before using this head in sign determination. -/
def CommonProduct.build (context : Ctx) (p q : DensePoly E) :
    Except BuildError {c : CommonProduct E Ctx // c.check context p q = true} :=
  let g := DensePoly.gcd p q
  let h := (DensePoly.divMod (p * q) g).1
  let c : CommonProduct E Ctx :=
    ⟨context, p, q, h, g, (DensePoly.divMod h p).1, (DensePoly.divMod h q).1⟩
  if hc : c.check context p q = true then .ok ⟨c, hc⟩ else .error .system

end Hex.SignDet
