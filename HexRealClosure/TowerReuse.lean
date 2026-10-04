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

/-- Prepared constraints for one descriptor, shared by all candidate checks. -/
structure RootConstraints (context : Context registry)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) where
  polynomials : List context.Poly
  signs : List Int
  polynomials_eq : polynomials = descriptor.raw.constraints
  signs_eq : signs = descriptor.raw.constraintSigns

/-- Compute the descriptor's derivative and endpoint queries once. -/
@[expose] def RootConstraints.prepare (context : Context registry)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    RootConstraints context descriptor :=
  ⟨descriptor.raw.constraints, descriptor.raw.constraintSigns, rfl, rfl⟩

/-- Compare constraint signs in order, stopping at the first mismatch. -/
@[expose] def Context.checkSigns (context : Context registry) (candidate : context.Value) :
    List context.Poly → List Int → Bool
  | [], [] => true
  | p :: ps, sign :: signs =>
    context.sign (p.eval candidate) == sign && context.checkSigns candidate ps signs
  | _, _ => false

/-- The short-circuit check accepts exactly the full original sign equation. -/
theorem Context.checkSigns_iff (context : Context registry) (candidate : context.Value)
    (ps : List context.Poly) (signs : List Int) :
    context.checkSigns candidate ps signs = true ↔
      ps.map (fun p => context.sign (p.eval candidate)) = signs := by
  induction ps generalizing signs with
  | nil => cases signs <;> simp [Context.checkSigns]
  | cons p ps ih => cases signs <;> simp [Context.checkSigns, ih]

/-- Check a candidate using the already prepared descriptor constraints. -/
@[expose] def RootConstraints.match? {context : Context registry}
    {descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature}
    (constraints : RootConstraints context descriptor)
    (candidate : context.Value) : Option (RootMatch context descriptor) :=
  if accepted : context.checkSigns candidate constraints.polynomials constraints.signs = true then
    some ⟨candidate, by
      have checked := (context.checkSigns_iff candidate _ _).mp accepted
      simpa only [constraints.polynomials_eq, constraints.signs_eq] using checked⟩
  else none

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
end Hex.RealClosure.Tower
