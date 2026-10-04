/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerTransport

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- An existing target value satisfying every converted root constraint. -/
structure RootMatch (context : Context registry)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) where
  value : context.Value
  selected : descriptor.raw.constraints.map (fun p => context.sign (p.eval value)) =
    descriptor.raw.constraintSigns

/-- Search existing values by their defining equation, derivative signs and
strict interval bounds. Failed candidates do not change the context. -/
@[expose] def Context.findRoot? (context : Context registry)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    List context.Value → Option (RootMatch context descriptor)
  | [] => none
  | candidate :: rest =>
    if selected : descriptor.raw.constraints.map (fun p => context.sign (p.eval candidate)) =
        descriptor.raw.constraintSigns then some ⟨candidate, selected⟩
    else context.findRoot? descriptor rest

/-- Retrieve the actual last algebraic generator without reconstructing its
predecessors. A staged base has no algebraic generator. -/
@[expose] def Context.lastRoot? (context : Context registry) : Option context.Value := by
  cases context with
  | pack chain =>
    cases chain with
    | base original => exact none
    | root parent descriptor frame encoded =>
      exact some (Algebraic.Element.ofPoly (DensePoly.ofCoeffs #[0, 1]))

/-- Reuse a target value after checking the converted root constraints. -/
@[expose] def Conversion.reuseRoot {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor)
    (candidate : conversion.context.Value)
    (selected : converted.raw.constraints.map
      (fun p => conversion.context.sign (p.eval candidate)) = converted.raw.constraintSigns) :
    Conversion (source.adjoin descriptor).context :=
  ⟨conversion.context,
    fun x => (DensePoly.ofCoeffs
      ((source.polynomial descriptor x).toArray.map conversion.value)).eval candidate,
    .reuse conversion.checked descriptor converted binding candidate selected⟩

private theorem Conversion.reuseRoot_context_proof {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor)
    (candidate : conversion.context.Value)
    (selected : converted.raw.constraints.map
      (fun p => conversion.context.sign (p.eval candidate)) = converted.raw.constraintSigns) :
    (conversion.reuseRoot descriptor converted binding candidate selected).context =
      conversion.context := rfl

/-- Reuse keeps the target context exactly, without appending a root level. -/
theorem Conversion.reuseRoot_context {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor)
    (candidate : conversion.context.Value)
    (selected : converted.raw.constraints.map
      (fun p => conversion.context.sign (p.eval candidate)) = converted.raw.constraintSigns) :
    (conversion.reuseRoot descriptor converted binding candidate selected).context =
      conversion.context := conversion.reuseRoot_context_proof descriptor converted binding candidate selected

/-- Check an existing target value against all constraints of the converted
selected root, including its defining equation and strict interval bounds. -/
@[expose] def Conversion.reuseRoot? {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor)
    (candidate : conversion.context.Value) : Option (Conversion (source.adjoin descriptor).context) :=
  if selected : converted.raw.constraints.map
      (fun p => conversion.context.sign (p.eval candidate)) = converted.raw.constraintSigns then
    some (conversion.reuseRoot descriptor converted binding candidate selected)
  else none

end Hex.RealClosure.Tower
