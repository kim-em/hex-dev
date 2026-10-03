/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CacheGather
public import HexRealRootsMathlib.RealClosed
public import HexOrderedFnMathlib.LiouvilleTests

public section

namespace Hex.RealClosure.BaseContext.GatherTests

open OrderedFn OrderedFn.Oracle

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

private def key (version : Nat) : ConstantKey := ⟨"liouville", version⟩
private def registry : Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none
private abbrev prefixContext := RealContext.rational registry

private theorem present (version : Nat) : (registry (key version)).isSome = true := by
  simp [registry, key]

private noncomputable abbrev rationalModel := RealPrefix.Model.rational registry

private theorem providerTranscendence :
    letI : Field rationalModel.context.Carrier := HexPolyMathlib.fieldOfGrind
    Real.RelativeTranscendence rationalModel.interpretation.hom (liouvilleNumber 2) := by
  let : Field Rat := HexPolyMathlib.fieldOfGrind
  change Real.RelativeTranscendence (Rat.castHom ℝ) (liouvilleNumber 2)
  exact OrderedFn.LiouvilleTests.transcendence

private theorem providerContained (δ : Rat) (_positive : 0 < δ) :
    Contains ((registry (key 1)).get (present 1) δ) (liouvilleNumber 2) :=
  OrderedFn.LiouvilleTests.provider_contains δ

private theorem providerWidth (δ : Rat) (positive : 0 < δ) :
    ((registry (key 1)).get (present 1) δ).width ≤ δ :=
  OrderedFn.LiouvilleTests.provider_width δ positive

/-- This constructs the full native prefix and its coherent predecessor model
using only the actual Liouville provider's analytic premises. -/
private noncomputable def providerModel := rationalModel.register (key 1) (present 1)
  (liouvilleNumber 2) providerContained providerWidth providerTranscendence

set_option backward.isDefEq.respectTransparency false in
/-- A real provider history supplies the complete gathering proof for repeated
nested rational owners over a proper real-prefix enlargement. -/
example
    (parent : SignDet.Descriptor (Tower.Context.base (BaseContext.rational registry)).Value
      Tower.Signature (Tower.Context.base (BaseContext.rational registry)).sign
      (Tower.Context.base (BaseContext.rational registry)).signature)
    (child : SignDet.Descriptor
      ((Tower.Context.base (BaseContext.rational registry)).adjoin parent).context.Value
      Tower.Signature
      ((Tower.Context.base (BaseContext.rational registry)).adjoin parent).context.sign
      ((Tower.Context.base (BaseContext.rational registry)).adjoin parent).context.signature) :
    let first := (Tower.Context.base (BaseContext.rational registry)).adjoin parent
    let second := first.context.adjoin child
    ∃ shared, Tower.Shared.gather? providerModel.context.finish
        [second.context, first.context, second.context] = some shared ∧
      Nonempty (Tower.Shared.Model shared providerModel.realization providerModel.towerModel) := by
  dsimp only
  apply Tower.Shared.gather?_models providerModel.realization providerModel.towerModel
  intro source present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;>
    simp only [Tower.Context.origin_adjoin, Tower.Origin.snoc_base, Tower.Context.origin_base] <;>
    simp only [Tower.Origin.base, PackedContext.signature, BaseContext.rational,
      Context.signature_real, RealContext.keys_rational] <;>
    exact ⟨List.nil_prefix, Nat.zero_le _⟩

end Hex.RealClosure.BaseContext.GatherTests
