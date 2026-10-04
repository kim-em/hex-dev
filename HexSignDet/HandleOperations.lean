/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.QueryHandle
public import HexSignDet.DescriptorOperations
public import HexSturm.DomainOperations

public section

namespace Hex.SignDet.QueryHandle

variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [targetOne : One E] [targetAdd : Add E] [targetSub : Sub E]
variable [targetMul : Mul E] [targetNatCast : NatCast E] [targetNeg : Neg E] [targetInv : Inv E]

/-- Transport a retained canonical query domain to equal coefficient
operations. No domain preparation or query production is executed. -/
@[expose] def changeOps (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E) (neg : Neg E) (inv : Inv E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : natCast = targetNatCast)
    (hg : neg = targetNeg) (hi : inv = targetInv)
    (sign : E → Int) (binding : Ctx)
    (descriptor : @Descriptor E Ctx _ _ one add sub mul natCast _ sign binding)
    (handle : @QueryHandle E Ctx _ _ one add sub mul natCast neg inv _ sign binding descriptor) :
    @QueryHandle E Ctx _ _ targetOne targetAdd targetSub targetMul targetNatCast targetNeg targetInv _
      sign binding
      (@Descriptor.changeOps E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNatCast
        one add sub mul natCast ho ha hs hm hn sign binding descriptor) :=
  let root := @Descriptor.changeOps E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNatCast
    one add sub mul natCast ho ha hs hm hn sign binding descriptor
  let domain := @Sturm.PreparedDomain.changeOps E _ _ targetOne targetAdd targetSub targetMul
    targetNatCast targetNeg targetInv one add sub mul natCast neg inv ho ha hs hm hn hg hi
    (@QueryHandle.domain E Ctx _ _ one add sub mul natCast neg inv _ sign binding descriptor handle)
  @QueryHandle.ofChecked E Ctx _ _ targetOne targetAdd targetSub targetMul targetNatCast
    targetNeg targetInv _ sign binding root domain (by
      cases ho
      cases ha
      cases hs
      cases hm
      cases hn
      cases hg
      cases hi
      simpa only [root, domain, Descriptor.changeOps_self, Sturm.PreparedDomain.changeOps_self]
        using handle.prepared)

/-- The retained domain data is exactly the operation-transported domain. -/
theorem changeOps_domain (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E) (neg : Neg E) (inv : Inv E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : natCast = targetNatCast)
    (hg : neg = targetNeg) (hi : inv = targetInv)
    (sign : E → Int) (binding : Ctx)
    (descriptor : @Descriptor E Ctx _ _ one add sub mul natCast _ sign binding)
    (handle : @QueryHandle E Ctx _ _ one add sub mul natCast neg inv _ sign binding descriptor) :
    @QueryHandle.domain E Ctx _ _ targetOne targetAdd targetSub targetMul targetNatCast targetNeg
      targetInv _ sign binding _
      (@changeOps E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNatCast targetNeg targetInv
        one add sub mul natCast neg inv ho ha hs hm hn hg hi sign binding descriptor handle) =
      @Sturm.PreparedDomain.changeOps E _ _ targetOne targetAdd targetSub targetMul targetNatCast
        targetNeg targetInv one add sub mul natCast neg inv ho ha hs hm hn hg hi
        (@QueryHandle.domain E Ctx _ _ one add sub mul natCast neg inv _ sign binding descriptor handle) := by
  unfold changeOps
  exact @QueryHandle.ofChecked_domain E Ctx _ _ targetOne targetAdd targetSub targetMul
    targetNatCast targetNeg targetInv _ sign binding _ _ _

/-- Identity transport retains the same handle despite its transported
proof index. -/
theorem changeOps_self (sign : E → Int) (binding : Ctx)
    (descriptor : Descriptor E Ctx sign binding) (handle : QueryHandle descriptor) :
    HEq (changeOps targetOne targetAdd targetSub targetMul targetNatCast targetNeg targetInv
      rfl rfl rfl rfl rfl rfl rfl sign binding descriptor handle) handle := by
  unfold changeOps
  simp only [Sturm.PreparedDomain.changeOps_self]
  apply HEq.trans (QueryHandle.ofChecked_heq descriptor _
    (Descriptor.changeOps_self sign binding descriptor) handle.domain handle.prepared _)
  exact heq_of_eq (QueryHandle.ofChecked_eq handle)

end Hex.SignDet.QueryHandle
