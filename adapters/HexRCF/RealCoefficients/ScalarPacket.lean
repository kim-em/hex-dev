/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SectionReplay
public import HexRealClosureTheory.SignFacts
public import HexSignDet.DagEncode

public section
namespace Hex.RCF.RealCoefficients.ScalarPacket
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Untrusted literal fields proposed by scalar production. Keeping the sign
separate lets source selection inspect it without decoding its own output. -/
structure Proposal where
  polynomial : Codec.Json
  sign : Int
  evidence : Codec.Json

/-- The existing three-field scalar packet layout. -/
@[expose] def Proposal.packet (proposal : Proposal) : Codec.Json :=
  .arr #[proposal.polynomial, Codec.Json.of proposal.sign, proposal.evidence]

/-- Produce literal fields for one demanded polynomial. Neither the proposed
sign nor the producer's checked row replaces independent frozen replay. -/
def buildParts (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (polynomial : DensePoly parent.Value) :
    Option Proposal := do
  let _ : Hashable parent.Value := ⟨fun a => hash (value.encode a)⟩
  let _ : Hashable Signature := ⟨fun a => hash (Signature.codec.encode a)⟩
  let .ok signs := context.buildSigns [context.queryPoly polynomial] | none
  return ⟨Codec.poly value polynomial, signs.value,
    Codec.graph value Signature.codec (Dag.encode signs.evidence)⟩

/-- Produce a proposed scalar packet for one demanded polynomial. This is
search code; the output must subsequently pass `read` in the ordinary kernel. -/
def build (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (polynomial : DensePoly parent.Value) :
    Option Codec.Json :=
  (buildParts context value polynomial).map Proposal.packet

/-- The actual selected-sign producer supplies a packet at every query over
a lawful ordinary-real parent. No successful producer result is assumed.
Independent frozen acceptance remains a separate obligation. -/
theorem buildParts_success (model : Model parent ℝ)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (polynomial : DensePoly parent.Value) :
    ∃ proposal, buildParts context value polynomial = some proposal := by
  obtain ⟨signs, produced⟩ := context.root.buildSigns_success model.value model.zero_iff
    model.one model.add model.sub model.mul model.nat model.sign model.neg model.inv
    [context.queryPoly polynomial]
  simp [buildParts, Algebraic.Context.buildSigns_eq, produced]

/-- Literal assembly preserves actual production progress for a validated
descriptor in its ordinary-real parent model. -/
theorem build_success (model : Model parent ℝ)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (polynomial : DensePoly parent.Value) :
    ∃ packet, build context value polynomial = some packet := by
  obtain ⟨proposal, produced⟩ := buildParts_success model context value polynomial
  exact ⟨proposal.packet, by simp only [build, produced, Option.map_some]⟩

/-- A literal production boundary keeps partially reduced interpreter terms
out of the compiler. Parsing here proposes data; `read` independently checks it. -/
def buildLiteral (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (value : ValueCodec parent.Value) (polynomial : Codec.Json) : Option Codec.Json := do
  let p ← (Codec.readPoly value polynomial).toOption
  build context value p

/-- Read exactly the supplied polynomial, sign and graph. No producer runs on
a missing, invalid or context-swapped packet. Predecessor arithmetic retains
its supplied implementation; avoiding native production at deeper parents
requires their checked operations. The model is used only in proofs. -/
@[expose, macro_inline] def read (original : Model parent ℝ)
    (value : ValueCodec parent.Value)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (polynomial : Codec.Json) (claimed : Int) (evidence : Codec.Json) :
    Option (Algebraic.SignFact context) := do
  let p ← (Codec.readPoly value polynomial).toOption
  let graph ← (Codec.readGraph value Signature.codec parent.signature context.root.raw.head
    context.root.raw.lower context.root.raw.upper evidence).toOption
  let memo ← graph.validate? parent.sign parent.signature context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  context.readSignFact? original.value original.zero_iff original.one original.add original.sub
    original.mul original.nat original.sign original.neg original.inv p claimed memo graph.root

/-- The fallback is unobservable after successful packet acceptance. -/
@[expose] def key (value : ValueCodec parent.Value) (literal : Codec.Json) :=
  (Codec.readPoly value literal).toOption.getD 0

theorem fields (original : Model parent ℝ) (value : ValueCodec parent.Value)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (polynomial : Codec.Json) (claimed : Int) (evidence : Codec.Json)
    (fact : Algebraic.SignFact context)
    (accepted : read original value context polynomial claimed evidence = some fact) :
    fact.polynomial = key value polynomial ∧ fact.sign = claimed := by
  unfold read at accepted
  cases hp : Codec.readPoly value polynomial with
  | error message => simp [hp, bind, Option.bind, Except.toOption] at accepted
  | ok p =>
    simp only [hp, Except.toOption, bind, Option.bind] at accepted
    cases hg : Codec.readGraph value Signature.codec parent.signature context.root.raw.head
        context.root.raw.lower context.root.raw.upper evidence with
    | error message => simp [hg] at accepted
    | ok graph =>
      simp only [hg] at accepted
      cases hm : graph.validate? parent.sign parent.signature context.root.raw.head
          context.root.raw.lower context.root.raw.upper with
      | none => simp [hm] at accepted
      | some memo =>
        simp only [hm] at accepted
        have binding := context.readSignFact_fields original.value original.zero_iff original.one
          original.add original.sub original.mul original.nat original.sign original.neg original.inv
          p claimed memo graph.root fact accepted
        simpa only [key, hp, Except.toOption, Option.getD_some] using binding

/-- Restore literal fields using the already checked acceptance theorem. This
avoids reducing the graph again when looking up a fact's polynomial or sign. -/
@[expose, macro_inline] def restore (original : Model parent ℝ) (value : ValueCodec parent.Value)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (polynomial : Codec.Json) (claimed : Int) (evidence : Codec.Json)
    (accepted : (read original value context polynomial claimed evidence).isSome = true) :
    Algebraic.SignFact context :=
  let parsed := read original value context polynomial claimed evidence
  let fact := parsed.get accepted
  let binding := fields original value context polynomial claimed evidence fact
    (Option.some_get accepted).symm
  {polynomial := key value polynomial, sign := claimed, checked := by
    rw [← binding.1, ← binding.2]
    exact fact.checked}

private theorem fact_eq {context : Algebraic.Context parent.Value Signature parent.sign parent.signature}
    (left right : Algebraic.SignFact context)
    (polynomial : left.polynomial = right.polynomial) (sign : left.sign = right.sign) :
    left = right := by
  cases left
  cases right
  cases polynomial
  cases sign
  rfl

/-- Restoration retains the exact accepted optional-reader result. -/
theorem read_restore (original : Model parent ℝ) (value : ValueCodec parent.Value)
    (context : Algebraic.Context parent.Value Signature parent.sign parent.signature)
    (polynomial : Codec.Json) (claimed : Int) (evidence : Codec.Json)
    (accepted : (read original value context polynomial claimed evidence).isSome = true) :
    read original value context polynomial claimed evidence =
      some (restore original value context polynomial claimed evidence accepted) := by
  have parsed := (Option.some_get accepted).symm
  apply parsed.trans
  apply congrArg some
  apply fact_eq
  · exact (fields original value context polynomial claimed evidence _ parsed).1
  · exact (fields original value context polynomial claimed evidence _ parsed).2

end Hex.RCF.RealCoefficients.ScalarPacket
