/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFrame
public meta import HexRealClosure.RootFrame

public section

namespace Hex.RealClosure.Tower.FrameTests
open Lean SignDet

private def registry : BaseContext.Registry := fun _ => none
private def rejected (result : Except String α) : Bool := result.toOption.isNone

private def sample : Option (Array Bool) :=
  let base := Context.base (BaseContext.rational registry)
  let two : base.Value := 1 + 1
  let raw : RawDescriptor base.Value Signature :=
    { context := base.signature, head := DensePoly.ofCoeffs #[-two, 0, 1],
      lower := .finite 1, upper := .finite two, indices := [], signs := [] }
  (Descriptor.validate base.sign base.signature raw).bind fun descriptor =>
  (base.adjoin? descriptor).bind fun original =>
  (base.readFrame original.frame).toOption.bind fun restored =>
  let raw₂ : RawDescriptor original.context.Value Signature :=
    { context := original.context.signature,
      head := DensePoly.ofCoeffs #[-original.generator, 0, 1],
      lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
  (Descriptor.validate original.context.sign original.context.signature raw₂).bind fun descriptor₂ =>
  (original.context.adjoin? descriptor₂).bind fun second =>
  (restored.extension.context.readFrame second.frame).toOption.bind fun restored₂ =>
  (original.frame.toJson.getArr?.toOption).bind fun fields =>
  (fields[6]!.getArr?.toOption).bind fun graph =>
  (graph[2]!.getArr?.toOption).bind fun entries =>
  (fromJson? (α := Nat) graph[1]!).toOption.bind fun rootIndex =>
  (entries[rootIndex]!.getArr?.toOption).bind fun rootEntry =>
  (rootEntry[0]!.getArr?.toOption).bind fun node =>
  (node[6]!.getArr?.toOption).bind fun system =>
  let stale := fields.set! 0 ((contextCodec base.signature).encode original.context.signature)
  let badVersion := fields.set! 6 (.arr (graph.set! 0 (toJson (2 : Nat))))
  let duplicate := fields.set! 6 (.arr (graph.set! 2 (.arr (entries.push entries[0]!))))
  let falseNode := node.set! 6 (.arr (system.set! 5 (toJson (0 : Int))))
  let falseEntries := entries.set! rootIndex (.arr (rootEntry.set! 0 (.arr falseNode)))
  let falseCertificate := fields.set! 6 (.arr (graph.set! 2 (.arr falseEntries)))
  (Literal.ofJson (.arr stale)).bind fun staleFrame =>
  (Literal.ofJson (.arr badVersion)).bind fun badFrame =>
  (Literal.ofJson (.arr duplicate)).bind fun duplicateFrame =>
  (Literal.ofJson (.arr falseCertificate)).bind fun falseFrame =>
  (Literal.ofJson (original.context.codec.encode original.generator)).bind fun oldValue =>
  (Literal.ofJson (restored.extension.context.codec.encode restored.extension.generator)).bind fun newValue =>
  let catalog := Catalog.empty registry
  (catalog.reconstruct second.context.signature).toOption.bind fun rebuilt =>
  (catalog.insert original.context).bind fun withPrefix =>
  (withPrefix.reconstruct second.context.signature).toOption.bind fun reused =>
  (rebuilt.val.read (second.context.write second.generator)).toOption.bind fun value =>
  (catalog.restoreElement (second.context.write second.generator)).toOption.bind fun readValue =>
  let polynomial : second.context.Poly := DensePoly.ofCoeffs #[0, 1]
  (withPrefix.restorePolynomial (second.context.writePoly polynomial)).toOption.bind fun readPolynomial =>
  some #[
    decide (restored.extension.context.signature = original.context.signature),
    decide (restored.extension.context.sign restored.extension.generator = 1),
    decide (restored₂.extension.context.signature = second.context.signature),
    decide (restored₂.extension.context.sign restored₂.extension.generator = 1),
    decide (oldValue = newValue),
    rejected (base.readFrame staleFrame), rejected (base.readFrame badFrame),
    (base.readDescriptor duplicateFrame.toJson).toOption.isSome,
    rejected (base.readFrame duplicateFrame),
    rejected (base.readFrame (.array .nil)),
    decide (rebuilt.val.signature = second.context.signature),
    decide (reused.val.signature = second.context.signature),
    decide (rebuilt.val.sign value = 1),
    rejected (catalog.reconstruct { second.context.signature with roots := [second.frame] }),
    rejected (catalog.reconstruct { second.context.signature with
      roots := [second.frame, original.frame] }),
    rejected (catalog.reconstruct { second.context.signature with
      roots := [original.frame, original.frame] }),
    rejected (withPrefix.reconstruct { second.context.signature with
      roots := [original.frame, original.frame] }),
    rejected (catalog.reconstruct { second.context.signature with roots := [badFrame] }),
    rejected (catalog.reconstruct { second.context.signature with
      base := ⟨[⟨"missing", 0⟩], 0⟩ }),
    (withPrefix.reconstruct original.context.signature).toOption.isSome,
    decide (readValue.context.signature = second.context.signature),
    decide (readValue.sign = 1),
    decide (readPolynomial.context.signature = second.context.signature),
    decide (readPolynomial.value.toArray.size = 2),
    rejected (base.readDescriptor falseFrame.toJson)]

/--
info: some #[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
  true, true, true, true, true, true]
-/
#guard_msgs in
#eval sample

end Hex.RealClosure.Tower.FrameTests
