/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseCodec
public import HexOrderedFnMathlib.Extension
public import HexOrderedFnMathlib.Infinitesimal

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

attribute [local instance 2000] Field.toGrindField

variable {registry : Registry} {K : Type} [Field K] [DecidableEq K]
variable {approx : K → Rat → Bounds} {baseSign : K → Int}

/-- Derive the erased search progress from the actual registered source's
containment, width and relative transcendence. The core constructor needs
only the resulting termination premises. -/
def RealContext.register (parent : RealContext registry K approx baseSign)
    (key : ConstantKey) (present : (registry key).isSome = true)
    (h : Real.Valid (parent.source key present)) :=
  parent.constant key present (Real.registration h).signProgress (Real.registration h).approxProgress

variable (parent : RealContext registry K approx baseSign)
variable (key : ConstantKey) (present : (registry key).isSome = true)
variable (h : Real.Valid (parent.source key present))
variable {ι : K →+* ℝ} {τ : ℝ}

/-- The sign of the actual newly registered context agrees with real evaluation. -/
theorem RealContext.register_sign
    (ha : ApproximationCorrect ι τ (parent.source key present)) (f : RationalFn K) :
    (⟨f⟩ : Element (.real (parent.register key present h))).sign = sgn (Real.eval ι τ f) :=
  Real.sign_sound ha f ((Real.registration h).signProgress f)

/-- The exact derived bounds contain the value; this is separate from width. -/
theorem RealContext.register_contains
    (ha : ApproximationCorrect ι τ (parent.source key present)) (f : RationalFn K) (δ : Rat) :
    Contains ((parent.register key present h).approx f δ) (Real.eval ι τ f) :=
  Real.approx_contains ha f δ ((Real.registration h).approxProgress f δ)

/-- Relative transcendence makes the registered context's zero sign reflect
the unique stored zero, with no field instance on the wrapper. -/
theorem RealContext.register_zero
    (ha : ApproximationCorrect ι τ (parent.source key present))
    (ht : Real.RelativeTranscendence ι τ) (f : RationalFn K) :
    (⟨f⟩ : Element (.real (parent.register key present h))).sign = 0 ↔
      (⟨f⟩ : Element (.real (parent.register key present h))) = 0 := by
  exact (Real.sign_eq_zero_iff ha ht f ((Real.registration h).signProgress f)).trans
    (Element.stored_eq_zero _)

section Infinitesimal

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The infinitesimal child's actual sign agrees with the shared Hahn-series
interpretation whenever the predecessor sign has its intended meaning. -/
theorem Element.infinitesimal_sign (context : Context registry K baseSign)
    (hs : ∀ a, baseSign a = (SignType.sign a : Int))
    (a : Element (.infinitesimal context)) :
    a.sign = (SignType.sign (Infinitesimal.embed a.stored) : Int) :=
  Infinitesimal.sign_eq baseSign hs a.stored

end Infinitesimal
end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealContext.register_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.RealContext.register_sign
/-- info: 'Hex.RealClosure.BaseContext.RealContext.register_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.RealContext.register_zero
/-- info: 'Hex.RealClosure.BaseContext.Element.infinitesimal_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.infinitesimal_sign
