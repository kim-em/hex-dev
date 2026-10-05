/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.NumberField
public import HexRealClosure.TrivialTower
public import HexRealClosure.Sample

public section

namespace Hex.RealClosure.NumberField

/-- The rational predecessor used to retain an existing selected number field. -/
abbrev base (registry : BaseContext.Registry) :=
  Tower.Context.base (BaseContext.rational registry)

/-- The original minimal polynomial over the native rational predecessor. -/
@[expose] def defining (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) :
    (base registry).Poly := DensePoly.ofCoeffs
  (generator.toAlgebraic.p.toArray.map fun (z : Int) => ⟨(z : Rat)⟩)

/-- A native root context checked against the original selected real generator.
The generator check is executable; semantic agreement is proved separately. -/
structure Presentation (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) : Type 1 where
  private mk ::
  root : Tower.Root (base registry)
  checked : ((Trivial.Map.rational registry).root root == generator) = true

namespace Presentation

/-- Accept a native root only at the exact selected embedding of the generator. -/
def ofRoot? (generator : RealAlgebraicNumber) (registry : BaseContext.Registry)
    (root : Tower.Root (base registry)) : Option (Presentation generator registry) :=
  if checked : ((Trivial.Map.rational registry).root root == generator) = true then
    some ⟨root, checked⟩
  else none

/-- The native selected-generator check accepts exactly its literal Boolean test. -/
theorem ofRoot?_isSome (generator : RealAlgebraicNumber) (registry : BaseContext.Registry)
    (root : Tower.Root (base registry)) :
    (ofRoot? generator registry root).isSome = true ↔
      ((Trivial.Map.rational registry).root root == generator) = true := by
  simp [ofRoot?]

end Presentation

/-- Find the original selected generator among the complete native roots of
its minimal polynomial. No nonreal algebraic value enters this constructor. -/
@[expose] def present? (generator : RealAlgebraicNumber) (registry : BaseContext.Registry) :
    Option (Presentation generator registry) :=
  match (base registry).roots (defining generator registry) with
  | .all => none
  | .finite entries => entries.findSome? fun entry => Presentation.ofRoot? generator registry entry.root

namespace Presentation

variable {generator : RealAlgebraicNumber} {registry : BaseContext.Registry}

/-- The immutable native context owning this selected number field. -/
abbrev context (source : Presentation generator registry) : Tower.Context registry :=
  source.root.conversion.context

/-- Evaluate exact fixed-field coordinates at the retained native generator. -/
@[expose] def pack (source : Presentation generator registry)
    (a : QAdjoin generator.toAlgebraic) : source.context.Value :=
  DensePoly.evalCoeffList
    (a.coeffs.toArray.toList.map fun q => source.root.conversion.value ⟨q⟩)
    source.root.convertedValue

/-- Enter every original coefficient through the checked selected-field map. -/
@[expose] def polynomial (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) : source.context.Poly :=
  DensePoly.ofCoeffs (p.toArray.map source.pack)

/-- Complete native roots over original fixed-field coordinates. -/
@[expose] def roots (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) : Tower.RootSet source.context :=
  source.context.roots (source.polynomial p)

/-- The checked diagnostic producer for the same original coefficients. -/
@[expose] def roots? (source : Presentation generator registry)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) :=
  source.context.roots? (source.polynomial p)

/-- Use the shared section and sector family in the retained number-field context. -/
def family (source : Presentation generator registry)
    (polynomials : List (DensePoly (QAdjoin generator.toAlgebraic))) :
    Tower.Sample.Family source.context (polynomials.map source.polynomial) :=
  Tower.Sample.family source.context (polynomials.map source.polynomial)

end Presentation
end Hex.RealClosure.NumberField
