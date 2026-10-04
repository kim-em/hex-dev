/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor

public section

namespace Hex.SignDet.Descriptor

variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [targetOne : One E] [targetAdd : Add E] [targetSub : Sub E]
variable [targetMul : Mul E] [targetNatCast : NatCast E]

/-- Transport a descriptor along literal equalities of coefficient operations.
Only its proof changes; its raw subject and complete evidence are retained. -/
@[expose] def changeOps (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : natCast = targetNatCast)
    (sign : E → Int) (binding : Ctx)
    (descriptor : @Descriptor E Ctx _ _ one add sub mul natCast _ sign binding) :
    @Descriptor E Ctx _ _ targetOne targetAdd targetSub targetMul targetNatCast _ sign binding :=
  let raw := @Descriptor.raw E Ctx _ _ one add sub mul natCast _ sign binding descriptor
  let evidence := @Descriptor.evidence E Ctx _ _ one add sub mul natCast _ sign binding descriptor
  @Descriptor.ofChecked E Ctx _ _ targetOne targetAdd targetSub targetMul targetNatCast _
    sign binding raw evidence (by
      have accepted := @Descriptor.accepted E Ctx _ _ one add sub mul natCast _
        sign binding descriptor
      change @RawDescriptor.check E Ctx _ _ one add sub mul natCast _
        sign binding raw evidence = true at accepted
      rw [ho, ha, hs, hm, hn] at accepted
      exact accepted)

/-- The raw subject is preserved literally across equal operations. -/
theorem changeOps_raw (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (natCast : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : natCast = targetNatCast)
    (sign : E → Int) (binding : Ctx)
    (descriptor : @Descriptor E Ctx _ _ one add sub mul natCast _ sign binding) :
    @Descriptor.raw E Ctx _ _ targetOne targetAdd targetSub targetMul targetNatCast _ sign binding
      (@changeOps E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNatCast
        one add sub mul natCast ho ha hs hm hn sign binding descriptor) =
    @Descriptor.raw E Ctx _ _ one add sub mul natCast _ sign binding descriptor := by
  unfold changeOps
  exact @Descriptor.ofChecked_raw E Ctx _ _ targetOne targetAdd targetSub targetMul
    targetNatCast _ sign binding _ _ _

/-- Equal-operation transport is identity when source and target operations
are the same, including every literal evidence field. -/
theorem changeOps_self (sign : E → Int) (binding : Ctx)
    (descriptor : Descriptor E Ctx sign binding) :
    changeOps targetOne targetAdd targetSub targetMul targetNatCast
      rfl rfl rfl rfl rfl sign binding descriptor = descriptor := by
  unfold changeOps
  exact Descriptor.ofChecked_eq descriptor

end Hex.SignDet.Descriptor
