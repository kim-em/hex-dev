/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardAgreementFinal

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementPublic

/-- All original coefficient occurrences share this one finite real reader,
with the original domain, sign agreement, and zero reflection. -/
theorem agreement : Transport.Inventory.Agreement
    (FiniteBaseProbe.base.partialRead GuardInventoryReplay.interpretation)
    (FiniteBaseProbe.base.partialDomain GuardInventoryReplay.interpretation)
    BaseContext.Element.sign (fun x : ℝ => (SignType.sign x : Int))
    GuardAgreementJoin.support :=
  GuardAgreementJoin.agreement

/-- The same interpretation preserves every inherited provider value. -/
theorem fixed : ∀ (a : BaseContext.Element FiniteBaseProbe.base) (r : ℝ),
    FiniteChainProbe.following.RealValue a.stored r →
    FiniteBaseProbe.base.partialDomain GuardInventoryReplay.interpretation a ∧
    FiniteBaseProbe.base.partialRead GuardInventoryReplay.interpretation a = r :=
  GuardAgreementJoin.fixed

/-- Finite coefficient agreement and provider values hold together at one reader. -/
theorem base : Transport.Inventory.Agreement
    (FiniteBaseProbe.base.partialRead GuardInventoryReplay.interpretation)
    (FiniteBaseProbe.base.partialDomain GuardInventoryReplay.interpretation)
    BaseContext.Element.sign (fun x : ℝ => (SignType.sign x : Int))
    GuardAgreementJoin.support ∧
    (∀ (a : BaseContext.Element FiniteBaseProbe.base) (r : ℝ),
      FiniteChainProbe.following.RealValue a.stored r →
      FiniteBaseProbe.base.partialDomain GuardInventoryReplay.interpretation a ∧
      FiniteBaseProbe.base.partialRead GuardInventoryReplay.interpretation a = r) :=
  GuardAgreementJoin.base

end Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementPublic
