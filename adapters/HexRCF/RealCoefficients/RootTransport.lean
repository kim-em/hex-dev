/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosureMathlib.TowerTransport
public import HexRCF.RealCoefficients.Replay
public import HexRealClosure.RootReplay
public import HexSignDet.DescriptorOperations
public section
namespace Hex.RCF.RealCoefficients.RootTransport
open Hex Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {source : Context registry}
/-- Assemble a converted root from its already checked literal binding. -/
def step (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor) :
    Conversion (source.adjoin descriptor).context :=
  Conversion.ofTransport
    (fun x => conversion.context.ofPoly converted
      (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value)))
    (Transport.adjoin conversion.checked descriptor converted binding)

/-- Retain the actual target context and complete packing closure. -/
theorem step_spec (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor) :
    (step conversion descriptor converted binding).context =
        (conversion.context.adjoin converted).context ∧
      HEq (step conversion descriptor converted binding).value
        (fun x => conversion.context.ofPoly converted
          (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value))) :=
  ⟨rfl, HEq.rfl⟩

private theorem conversion_eq (left right : Conversion source)
    (context : left.context = right.context) (value : HEq left.value right.value) : left = right := by
  cases left with
  | mk lc lv lp =>
    cases right with
    | mk rc rv rp =>
      dsimp only at context value
      cases context
      cases eq_of_heq value
      rfl

/-- Agreement with the owner's native result when it returns this exact
descriptor. Equivalent roots with different evidence need not have equal
context signatures. This agreement premise is not used by frozen replay. -/
theorem step_native (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (accepted : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    step conversion descriptor converted
      (SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp accepted)) =
        conversion.adjoinChecked descriptor converted accepted := by
  apply conversion_eq
  · exact (conversion.adjoinChecked_context descriptor converted accepted).symm
  · exact (conversion.adjoinChecked_value descriptor converted accepted).symm

/-- A checked target descriptor with the complete mapped source identity. -/
structure Checked (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (guards : List source.Value) where
  converted : SignDet.Descriptor conversion.context.Value Signature
    conversion.context.sign conversion.context.signature
  binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor
  nonzero : ∀ a ∈ guards, a ≠ 0

/-- Preflight supplied source divisors, restore the supplied target descriptor and check
its context, polynomial, endpoints and derivative word against the actual map.
A valid different subject yields `binding`; malformed evidence yields `evidence`. -/
@[expose] def read (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value)
    (guards : List source.Value) (subject graph : SignDet.Codec.Json) :
    Except Hex.RCF.RealCoefficients.Replay.Error (Checked conversion descriptor guards) := do
  if hguards : guards.all (fun a => Decidable.decide (a ≠ 0)) = true then
    let converted ← match Algebraic.RootReplay.readDescriptor value Signature.codec
        conversion.context.sign conversion.context.signature subject graph with
      | .error _ => .error .evidence
      | .ok root => .ok root
    let expected := source.mapDescriptor conversion.context conversion.value descriptor
    if binding : converted.raw = expected then
      return ⟨converted, binding, fun a member =>
        of_decide_eq_true ((List.all_eq_true.mp hguards) a member)⟩
    else throw .binding
  else throw .divisor

/-- Use equal supplied coefficient maps and operation dictionaries for frozen
replay, then retain the descriptor with canonical proof indices. The value
codec must independently restore its finite coefficient records. -/
@[expose] def readWith (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value)
    (mapped : source.Value → conversion.context.Value) (hmapped : mapped = conversion.value)
    (one : One conversion.context.Value) (add : Add conversion.context.Value)
    (sub : Sub conversion.context.Value) (mul : Mul conversion.context.Value)
    (nat : NatCast conversion.context.Value)
    (ho : one = Tower.instOneValue conversion.context)
    (ha : add = Tower.instAddValue conversion.context)
    (hs : sub = Tower.instSubValue conversion.context)
    (hm : mul = Tower.instMulValue conversion.context)
    (hn : nat = Tower.instNatCastValue conversion.context)
    (guards : List source.Value) (subject graph : SignDet.Codec.Json) :
    Except Hex.RCF.RealCoefficients.Replay.Error (Checked conversion descriptor guards) :=
  letI := one
  letI := add
  letI := sub
  letI := mul
  letI := nat
  do
    if hguards : guards.all (fun a => Decidable.decide (a ≠ 0)) = true then
      let restored ← match Algebraic.RootReplay.readDescriptor value Signature.codec
          conversion.context.sign conversion.context.signature subject graph with
        | .error _ => .error .evidence
        | .ok root => .ok root
      let expected := source.mapDescriptor conversion.context mapped descriptor
      if binding : restored.raw = expected then
        let converted := @SignDet.Descriptor.changeOps conversion.context.Value Signature
          (Tower.instZeroValue conversion.context) (Tower.instDecidableEqValue conversion.context)
          inferInstance (Tower.instOneValue conversion.context) (Tower.instAddValue conversion.context)
          (Tower.instSubValue conversion.context) (Tower.instMulValue conversion.context)
          (Tower.instNatCastValue conversion.context) one add sub mul nat ho ha hs hm hn
          conversion.context.sign conversion.context.signature restored
        return ⟨converted, by
          have literal := @SignDet.Descriptor.changeOps_raw conversion.context.Value Signature
            (Tower.instZeroValue conversion.context) (Tower.instDecidableEqValue conversion.context)
            inferInstance (Tower.instOneValue conversion.context) (Tower.instAddValue conversion.context)
            (Tower.instSubValue conversion.context) (Tower.instMulValue conversion.context)
            (Tower.instNatCastValue conversion.context) one add sub mul nat ho ha hs hm hn
            conversion.context.sign conversion.context.signature restored
          exact literal.trans (binding.trans
            (congrArg (fun f => source.mapDescriptor conversion.context f descriptor) hmapped)), fun a member =>
          of_decide_eq_true ((List.all_eq_true.mp hguards) a member)⟩
      else throw .binding
    else throw .divisor

/-- Supplied equal operations preserve every canonical result and error. -/
theorem readWith_eq (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value)
    (mapped : source.Value → conversion.context.Value) (hmapped : mapped = conversion.value)
    (one : One conversion.context.Value) (add : Add conversion.context.Value)
    (sub : Sub conversion.context.Value) (mul : Mul conversion.context.Value)
    (nat : NatCast conversion.context.Value)
    (ho : one = Tower.instOneValue conversion.context)
    (ha : add = Tower.instAddValue conversion.context)
    (hs : sub = Tower.instSubValue conversion.context)
    (hm : mul = Tower.instMulValue conversion.context)
    (hn : nat = Tower.instNatCastValue conversion.context)
    (guards : List source.Value) (subject graph : SignDet.Codec.Json) :
    readWith conversion descriptor value mapped hmapped one add sub mul nat ho ha hs hm hn
      guards subject graph = read conversion descriptor value guards subject graph := by
  cases hmapped
  cases ho
  cases ha
  cases hs
  cases hm
  cases hn
  unfold readWith read
  cases Algebraic.RootReplay.readDescriptor value Signature.codec
      conversion.context.sign conversion.context.signature subject graph <;>
    simp [bind, Except.bind, pure, Except.pure, SignDet.Descriptor.changeOps_self]

/-- The accepted result retains nonzero evidence for its exact source guard list. -/
theorem read_guards (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value) (guards : List source.Value)
    (subject graph : SignDet.Codec.Json) (checked : Checked conversion descriptor guards)
    (_accepted : read conversion descriptor value guards subject graph = .ok checked) :
    ∀ a ∈ guards, a ≠ 0 := checked.nonzero

/-- A zero source guard rejects before any mapped coefficient or graph work. -/
theorem read_zero (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value) (guards : List source.Value)
    (zero : (0 : source.Value) ∈ guards) (subject graph : SignDet.Codec.Json) :
    read conversion descriptor value guards subject graph = .error .divisor := by
  have invalid : guards.all (fun a => Decidable.decide (a ≠ 0)) = false := by
    cases h : guards.all (fun a => Decidable.decide (a ≠ 0)) with
    | false => rfl
    | true => have := of_decide_eq_true ((List.all_eq_true.mp h) 0 zero); contradiction
  unfold read
  simp only [invalid, Bool.false_eq_true, ↓reduceDIte, throw]
  rfl

/-- Invalid supplied evidence has an evidence outcome once source guards pass. -/
theorem read_evidence (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value) (guards : List source.Value)
    (valid : guards.all (fun a => Decidable.decide (a ≠ 0)) = true)
    (subject graph : SignDet.Codec.Json) (message : String)
    (rejected : Algebraic.RootReplay.readDescriptor value Signature.codec
      conversion.context.sign conversion.context.signature subject graph = .error message) :
    read conversion descriptor value guards subject graph = .error .evidence := by
  unfold read
  simp only [valid, ↓reduceDIte, bind, Except.bind, rejected]

/-- A valid descriptor with a different complete subject is a binding failure. -/
theorem read_binding (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value) (guards : List source.Value)
    (valid : guards.all (fun a => Decidable.decide (a ≠ 0)) = true)
    (subject graph : SignDet.Codec.Json)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (accepted : Algebraic.RootReplay.readDescriptor value Signature.codec
      conversion.context.sign conversion.context.signature subject graph = .ok converted)
    (different : converted.raw ≠ source.mapDescriptor conversion.context conversion.value descriptor) :
    read conversion descriptor value guards subject graph = .error .binding := by
  unfold read
  simp only [valid, ↓reduceDIte, bind, Except.bind, accepted, different, ↓reduceDIte]
  rfl

/-- The restored descriptor is the one accepted by the owner reader. -/
theorem read_fields (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value) (guards : List source.Value)
    (subject graph : SignDet.Codec.Json) (checked : Checked conversion descriptor guards)
    (accepted : read conversion descriptor value guards subject graph = .ok checked) :
    Algebraic.RootReplay.readDescriptor value Signature.codec conversion.context.sign
      conversion.context.signature subject graph = .ok checked.converted := by
  have valid := read_guards conversion descriptor value guards subject graph checked accepted
  have all : guards.all (fun a => Decidable.decide (a ≠ 0)) = true :=
    List.all_eq_true.mpr (fun a member => decide_eq_true (valid a member))
  unfold read at accepted
  simp only [all, ↓reduceDIte, bind, Except.bind, pure, Except.pure, throw] at accepted
  cases hr : Algebraic.RootReplay.readDescriptor value Signature.codec
      conversion.context.sign conversion.context.signature subject graph with
  | error message => simp only [hr] at accepted; contradiction
  | ok converted =>
    simp only [hr] at accepted
    split at accepted
    · have equal := Except.ok.inj accepted
      rw [← equal]
    · contradiction

/-- Acceptance retains every original decoded subject field. -/
theorem read_subject (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value) (guards : List source.Value)
    (subject graph : SignDet.Codec.Json) (checked : Checked conversion descriptor guards)
    (accepted : read conversion descriptor value guards subject graph = .ok checked) :
    Algebraic.SignRequests.readRoot value Signature.codec subject = .ok checked.converted.raw :=
  Algebraic.RootReplay.readDescriptor_subject _ _ _ _ _ _ _
    (read_fields conversion descriptor value guards subject graph checked accepted)

variable {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K]
omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- The retained source guard list is nonzero in its original interpretation. -/
theorem Checked.domains {conversion : Conversion source}
    {descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature}
    {guards : List source.Value} (checked : Checked conversion descriptor guards)
    (original : Model source K) : ∀ a ∈ guards, original.value a ≠ 0 := by
  intro a member zero
  exact checked.nonzero a member ((original.zero_iff a).mp zero)

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- Every retained guard stays nonzero after the actual coefficient conversion. -/
theorem Checked.transported {conversion : Conversion source} {original : Model source K}
    {descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature}
    {guards : List source.Value} (checked : Checked conversion descriptor guards)
    (interpretation : Conversion.Model conversion original) :
    ∀ a ∈ guards, conversion.value a ≠ 0 := by
  intro a member zero
  exact checked.nonzero a member ((interpretation.zero a).mp zero)

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- Acceptance retains source divisor evidence without needing to re-run parsing. -/
theorem read_domains (original : Model source K) (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (value : SignDet.ValueCodec conversion.context.Value) (guards : List source.Value)
    (subject graph : SignDet.Codec.Json) (checked : Checked conversion descriptor guards)
    (_accepted : read conversion descriptor value guards subject graph = .ok checked) :
    ∀ a ∈ guards, original.value a ≠ 0 := checked.domains original

/-- Preserve every old-context value using the owner's actual selected-root
transport theorem. This is a semantic law; later scalar packing still needs
its own finite checked assembly in ordinary kernel quotation. -/
noncomputable def model {conversion : Conversion source} {original : Model source K}
    (interpretation : Conversion.Model conversion original)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor) :
    Conversion.Model (step conversion descriptor converted binding) (original.adjoin descriptor) :=
  interpretation.adjoinWith descriptor converted binding
    (step conversion descriptor converted binding) rfl HEq.rfl
end Hex.RCF.RealCoefficients.RootTransport
