/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseInclusion

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry}

/-- The native staged producer preserves every coefficient when its source
is the same actual context, including each infinitesimal variable. -/
theorem Chain.embedding?_self {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (target : Chain registry K sign) :
    target.embedding? (.pack (Context.ofChain target)) =
      some (FieldEmbedding.identity K) := by
  induction target with
  | real parent => rw [Chain.embedding?_real, RealChain.embedding?_self]
  | infinitesimal parent ih =>
    have aligned : ¬ (PackedContext.pack (Context.ofChain parent.infinitesimal)).signature.infinitesimals <
        parent.signature.infinitesimals + 1 := by
      change ¬ (Context.ofChain parent.infinitesimal).chain.signature.infinitesimals <
        parent.signature.infinitesimals + 1
      rw [Context.ofChain_chain]
      change ¬ parent.signature.infinitesimals + 1 < parent.signature.infinitesimals + 1
      exact Nat.lt_irrefl _
    rw [Chain.embedding?_aligned parent parent aligned, ih, Option.map_some,
      FieldEmbedding.rationalFunctions_identity]

/-- Packing an actual base retains the identity coefficient inclusion. -/
theorem PackedContext.embedding?_self (context : PackedContext registry) :
    context.embedding? context = some (FieldEmbedding.identity context.Carrier) := by
  cases context with
  | pack context =>
    rw [← Context.ofChain_eq context, PackedContext.embedding?_ofChain,
      Chain.embedding?_self]

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A checked inclusion of an actual base into itself retains every native
wrapped coefficient value. -/
theorem BaseInclusion.self_value {base : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion base base) (a : (Context.ofBase base).Value) :
    inclusion.value a = a := by
  have same := inclusion.produced
  rw [BaseContext.PackedContext.subsequence?_self] at same
  have coefficients := (Option.some.inj same).symm
  cases base with
  | pack base =>
    apply BaseContext.Element.ext
    change inclusion.coefficients.value a.stored = a.stored
    rw [coefficients, BaseContext.FieldEmbedding.identity_value]

/-- The actual checked map into the next staged base is the old map followed
by the constant rational-function embedding. Earlier infinitesimals retain
their original values. -/
theorem BaseInclusion.next_value {source : BaseContext.PackedContext registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (target : BaseContext.Context registry B sign)
    (old : BaseInclusion source (.pack target))
    (next : BaseInclusion source (.pack target.infinitesimal))
    (a : (Context.ofBase source).Value) :
    next.value a = BaseContext.Element.embed (old.value a) := by
  have compatible := (BaseContext.PackedContext.subsequence?_isSome source (.pack target)).mp
    (by rw [old.produced]; rfl)
  have second := next.produced
  rw [BaseContext.PackedContext.subsequence?_next source target compatible.2,
    old.produced, Option.map_some] at second
  have coefficients := (Option.some.inj second).symm
  apply BaseContext.Element.ext
  change next.coefficients.value (Context.baseStored source a) =
    Hex.RationalFn.C (old.coefficients.value (Context.baseStored source a))
  rw [coefficients, BaseContext.FieldEmbedding.comp_value,
    BaseContext.FieldEmbedding.constants_value]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.self_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.self_value
