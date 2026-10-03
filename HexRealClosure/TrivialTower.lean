/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerSuffix
public import HexRealClosure.TowerRoots
public import HexRealAlgebraic.Roots

public section

namespace Hex.RealClosure.Trivial

variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Cached conversion of a rational algebraic tower's stored coefficients to
the existing canonical real-algebraic carrier. The companion proves agreement
for the rational factory and each actual selected-root extension. -/
structure Map (parent : Tower.Context registry) : Type 1 where
  private mk ::
  value : parent.Value → RealAlgebraicNumber

/-- Convert the native rational coefficients without changing their values. -/
def Map.rational (registry : BaseContext.Registry) :
    Map (Tower.Context.base (BaseContext.rational registry)) :=
  ⟨fun a => RealAlgebraicNumber.ofRat a.stored⟩

theorem Map.rational_value (registry : BaseContext.Registry)
    (a : (Tower.Context.base (BaseContext.rational registry)).Value) :
    (Map.rational registry).value a = RealAlgebraicNumber.ofRat a.stored := by
  simp [Map.rational]

/-- Convert all actual stored coefficients, using the existing polynomial
normalizer rather than structural equality in the tower. -/
@[expose] def Map.polynomial (source : Map parent) (p : DensePoly parent.Value) :
    RealAlgebraicPoly := RealAlgebraicPoly.ofArray (p.toArray.map source.value)

/-- Run canonical Horner arithmetic on the converted coefficient list. -/
@[expose] def Map.eval (source : Map parent) (p : DensePoly parent.Value)
    (x : RealAlgebraicNumber) : RealAlgebraicNumber :=
  DensePoly.evalCoeffList (p.toArray.toList.map source.value) x

/-- Test the exact open endpoints and ordered derivative signs. Root
membership itself is supplied by the independent backend's root list. -/
@[expose] def Map.matches (source : Map parent)
    (descriptor : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (x : RealAlgebraicNumber) : Bool :=
  (match descriptor.raw.lower with
    | .negInf => true
    | .finite a => decide (source.value a < x)
    | .posInf => false) &&
  (match descriptor.raw.upper with
    | .posInf => true
    | .finite b => decide (x < source.value b)
    | .negInf => false) &&
  decide (descriptor.raw.queries.map (fun q => (source.eval q x).sign) = descriptor.raw.signs)

/-- Find the selected root in the existing real-algebraic backend. Valid
converted descriptors have a nonzero head, so its universal case is excluded
by the companion's success theorem. -/
@[expose] def Map.canonical? (source : Map parent)
    (descriptor : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    Option RealAlgebraicNumber :=
  let lower := descriptor.raw.lower.map source.value
  let upper := descriptor.raw.upper.map source.value
  let queries := descriptor.raw.queries.map (fun q => q.toArray.toList.map source.value)
  (((source.polynomial descriptor.raw.head).roots.toArray.toList).find? fun entry =>
    (match lower with
      | .negInf => true
      | .finite a => decide (a < entry.root)
      | .posInf => false) &&
    (match upper with
      | .posInf => true
      | .finite b => decide (entry.root < b)
      | .negInf => false) &&
    decide (queries.map (fun q => (DensePoly.evalCoeffList q entry.root).sign) =
      descriptor.raw.signs)).map (·.root)

/-- Preparing the converted endpoints and query coefficients once changes
no selection predicate or root identity. -/
theorem Map.canonical?_eq (source : Map parent)
    (descriptor : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    source.canonical? descriptor =
      (((source.polynomial descriptor.raw.head).roots.toArray.toList).find?
        (fun entry => source.matches descriptor entry.root)).map (·.root) := by
  simp only [Map.canonical?, Map.matches, Map.eval, List.map_map, Function.comp_def]
  cases descriptor.raw.lower <;> cases descriptor.raw.upper <;> rfl

/-- The companion proves this selected-root search succeeds for the actual
rational-tower conversion; the diagnostic fallback is then unreachable. -/
@[expose] def Map.canonical (source : Map parent)
    (descriptor : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    RealAlgebraicNumber :=
  (source.canonical? descriptor).getD
    (Hex.panicWith 0 "Trivial.Map.canonical: selected root not found")

/-- Select the canonical generator once, retaining it in the conversion
closure used for every later coefficient. -/
def Map.adjoin (source : Map parent)
    (descriptor : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    Map (parent.adjoin descriptor).context :=
  let generator := source.canonical descriptor
  ⟨fun a => source.eval (parent.polynomial descriptor a) generator⟩

theorem Map.adjoin_value (source : Map parent)
    (descriptor : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (a : (parent.adjoin descriptor).context.Value) :
    (source.adjoin descriptor).value a =
      source.eval (parent.polynomial descriptor a) (source.canonical descriptor) := by
  simp [Map.adjoin]

/-- Convert a validated suffix in predecessor order, caching each selected
canonical generator in its coefficient-conversion closure. -/
@[expose] def Map.extend {context : Tower.Context registry}
    (source : Map context) (suffix : Tower.Suffix context) :
    Map suffix.context :=
  match suffix with
  | .nil => source
  | .root descriptor rest => (source.adjoin descriptor).extend rest

/-- The complete rational algebraic tower conversion. No real constants or
infinitesimals are substituted by a real part or an ordinary parameter. -/
@[expose] def Map.ofSuffix
    (suffix : Tower.Suffix (Tower.Context.base (BaseContext.rational registry))) :
    Map suffix.context := (Map.rational registry).extend suffix

/-- Convert an actual native root without changing its selected embedding. -/
@[expose] def Map.root (source : Map parent) : Tower.Root parent → RealAlgebraicNumber
  | .point a => source.value a
  | .selected descriptor _ _ => source.canonical descriptor

/-- Convert one actual native root entry, retaining its exact multiplicity. -/
@[expose] def Map.entry (source : Map parent) (entry : Tower.RootEntry parent) : RealRootCount :=
  ⟨source.root entry.root, entry.multiplicity, entry.positive⟩

/-- Retain the universal zero case, sorted roots and their exact positive
multiplicities when converting a native root result. -/
@[expose] def Map.output (source : Map parent) : Tower.RootSet parent → RealRootSet
  | .all => .all
  | .finite entries => .finite ((entries.map source.entry).toArray)

/-- The generic native route after canonical conversion, for exact agreement
and differential checks against the independent backend. -/
@[expose] def Map.roots (source : Map parent) (p : DensePoly parent.Value) : RealRootSet :=
  source.output (parent.roots p)

/-- Compare converted coefficients using the existing real-algebraic backend. -/
@[expose] def Map.compare (source : Map parent) (a b : parent.Value) : Ordering :=
  RealAlgebraicNumber.compare (source.value a) (source.value b)

/-- Compare roots that own distinct child contexts through their shared
coefficient context and the canonical selected values. -/
@[expose] def Map.compareRoots (source : Map parent) (a b : Tower.Root parent) : Ordering :=
  RealAlgebraicNumber.compare (source.root a) (source.root b)

end Hex.RealClosure.Trivial
