/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Basic

public section

namespace Hex.Sturm.PreparedDomain

variable {E : Type} [Zero E] [DecidableEq E]
variable [targetOne : One E] [targetAdd : Add E] [targetSub : Sub E]
variable [targetMul : Mul E] [targetNatCast : NatCast E] [targetNeg : Neg E] [targetInv : Inv E]

/-- Retain all prepared-domain data along equal coefficient operations.
The exact producer equation and endpoint proofs are transported, not rerun. -/
@[expose] def changeOps (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E) (neg : Neg E) (inv : Inv E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : natCast = targetNatCast)
    (hg : neg = targetNeg) (hi : inv = targetInv)
    (domain : @PreparedDomain E _ _ one add sub mul natCast neg inv) :
    @PreparedDomain E _ _ targetOne targetAdd targetSub targetMul targetNatCast targetNeg targetInv :=
  let sign := @PreparedDomain.sign E _ _ one add sub mul natCast neg inv domain
  let head := @PreparedDomain.head E _ _ one add sub mul natCast neg inv domain
  let lower := @PreparedDomain.lower E _ _ one add sub mul natCast neg inv domain
  let upper := @PreparedDomain.upper E _ _ one add sub mul natCast neg inv domain
  let squarefree := @PreparedDomain.squarefree E _ _ one add sub mul natCast neg inv domain
  @PreparedDomain.ofChecked E _ _ targetOne targetAdd targetSub targetMul targetNatCast
    targetNeg targetInv sign head lower upper squarefree
    (by
      have endpoints := @PreparedDomain.endpoints_valid E _ _ one add sub mul natCast neg inv domain
      change TarskiCertificate.checkEndpoints
        (@EndpointSigns.ofSign E _ _ sub add mul sign) head lower upper = true at endpoints
      rw [hs, ha, hm] at endpoints
      exact endpoints)
    (@PreparedDomain.last_constant E _ _ one add sub mul natCast neg inv domain)
    (by
      have produced := @PreparedDomain.produced E _ _ one add sub mul natCast neg inv domain
      change squarefree = @SignedRemainderChain.build E _ _ one add sub mul neg natCast sign
        (@normalize E _ _ mul neg inv sign) head
        (@One.one (DensePoly E) (@DensePoly.instOne E _ _ one)) at produced
      rw [ho, ha, hs, hm, hn, hg, hi] at produced
      exact produced)

/-- Identity transport preserves the complete prepared-domain value. -/
theorem changeOps_self (domain : PreparedDomain E) :
    changeOps targetOne targetAdd targetSub targetMul targetNatCast targetNeg targetInv
      rfl rfl rfl rfl rfl rfl rfl domain = domain := by
  unfold changeOps
  exact PreparedDomain.ofChecked_eq domain

end Hex.Sturm.PreparedDomain
