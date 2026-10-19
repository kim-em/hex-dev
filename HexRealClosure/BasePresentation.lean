/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseTower
public import HexRealClosure.BaseContext
import all HexRealClosure.BaseContext

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry}

/-- Map an actual real-provider chain to its positional field without changing
any native arithmetic dictionary or evaluating its approximation providers. -/
def RealChain.encode {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) :
    FieldEmbedding K (BaseTower chain.keys.length) :=
  match chain with
  | .base => FieldEmbedding.identity Rat
  | @RealChain.step _ B field eq approximation tag parent key bounds registered sp ap => by
    have depth : parent.keys.length + 1 = (parent.step key bounds registered sp ap).keys.length := by
      change parent.keys.length + 1 = (parent.keys ++ [key]).length
      simp only [List.length_append, List.length_singleton]
    exact depth ▸ (show FieldEmbedding (RationalFn B) (BaseTower (parent.keys.length + 1)) from
      (RealChain.encode parent).rationalFunctions)

/-- Recover the actual provider-chain carrier from its positional field. -/
def RealChain.decode {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) :
    FieldEmbedding (BaseTower chain.keys.length) K :=
  match chain with
  | .base => FieldEmbedding.identity Rat
  | @RealChain.step _ B field eq approximation tag parent key bounds registered sp ap => by
    have depth : parent.keys.length + 1 = (parent.step key bounds registered sp ap).keys.length := by
      change parent.keys.length + 1 = (parent.keys ++ [key]).length
      simp only [List.length_append, List.length_singleton]
    exact depth ▸ (show FieldEmbedding (BaseTower (parent.keys.length + 1)) (RationalFn B) from
      (RealChain.decode parent).rationalFunctions)

private theorem cancel_cast {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {m n : Nat} (depth : m = n)
    (first : FieldEmbedding K (BaseTower m)) (next : FieldEmbedding (BaseTower m) K) :
    (depth ▸ first).comp (depth ▸ next) = first.comp next := by
  cases depth
  rfl

private theorem identity_cast {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {m n : Nat} (depth : m = n)
    (first : FieldEmbedding K (BaseTower m)) (next : FieldEmbedding (BaseTower m) K)
    (inverse : next.comp first = FieldEmbedding.identity (BaseTower m)) :
    (depth ▸ next).comp (depth ▸ first) = FieldEmbedding.identity (BaseTower n) := by
  cases depth
  exact inverse

/-- Positional encoding and decoding restore the actual source carrier. -/
theorem RealChain.decode_encode {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) :
    chain.encode.comp chain.decode = FieldEmbedding.identity K := by
  induction chain with
  | base =>
    apply FieldEmbedding.value_ext
    intro a
    rw [FieldEmbedding.comp_value]
    simp only [RealChain.encode, RealChain.decode, FieldEmbedding.identity_value]
  | step parent key bounds registered sp ap ih =>
    simp only [RealChain.encode, RealChain.decode]
    rw [cancel_cast, FieldEmbedding.rationalFunctions_comp, ih,
      FieldEmbedding.rationalFunctions_identity]

/-- Decoding and encoding restore every positional canonical fraction. -/
theorem RealChain.encode_decode {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) :
    chain.decode.comp chain.encode = FieldEmbedding.identity (BaseTower chain.keys.length) := by
  induction chain with
  | base =>
    apply FieldEmbedding.value_ext
    intro a
    rw [FieldEmbedding.comp_value]
    simp only [RealChain.encode, RealChain.decode, FieldEmbedding.identity_value]
    exact FieldEmbedding.identity_value (a : Rat)
  | step parent key bounds registered sp ap ih =>
    simp only [RealChain.encode, RealChain.decode]
    apply identity_cast
    rw [FieldEmbedding.rationalFunctions_comp, ih,
      FieldEmbedding.rationalFunctions_identity]

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealChain.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.decode_encode

/-- info: 'Hex.RealClosure.BaseContext.RealChain.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.encode_decode
