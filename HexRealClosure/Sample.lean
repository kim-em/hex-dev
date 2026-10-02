/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootCollection
public import HexRealClosure.TowerCatalog
public import HexRealClosure.TowerOrder

public section

namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Context registry}

/-- A section or an open sector, with boundaries owned by the sample context. -/
inductive Cell (context : Context registry) where
  | section (root : context.Value)
  | sector (lower upper : Endpoint context.Value)

/-- Check section equality or strict membership in both finite endpoints. -/
@[expose] def Cell.contains {context : Context registry} (cell : Cell context)
    (value : context.Value) : Bool :=
  match cell with
  | .section root => context.equal root value
  | .sector lower upper =>
    (match lower with
      | .negInf => true
      | .finite bound => decide (context.compare bound value = .lt)
      | .posInf => false) &&
    (match upper with
      | .posInf => true
      | .finite bound => decide (context.compare value bound = .lt)
      | .negInf => false)

/-- An ordinary native sample and the explicit inclusion of its coefficients. -/
structure Sample (parent : Context registry) : Type 1 where
  private mk ::
  input : Conversion parent
  value : input.context.Value
  cell : Cell input.context

/-- Evaluate all requested polynomials through the sample's actual inclusion. -/
@[expose] def Sample.signs (sample : Sample parent) (polynomials : List parent.Poly) : List Int :=
  polynomials.map fun p => sample.input.context.sign
    ((DensePoly.ofCoeffs (p.toArray.map sample.input.value)).eval sample.value)

/-- Use the actual cached root context and generator for a section. -/
def Sample.ofRoot (root : Root parent) : Sample parent :=
  Sample.mk root.conversion root.convertedValue (.section root.convertedValue)

/-- Construct a section from a validated descriptor over the input context. -/
def Sample.section (parent : Context registry)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature) : Sample parent :=
  Sample.ofRoot (Root.ofSelection parent (.selected descriptor))

namespace Sample

/-- All finite roots of the requested family; zero polynomials contribute no
boundary because their sign is identically zero. The original roots retain
multiplicities in `Context.roots`; cell boundaries need each distinct value once. -/
@[expose] def roots (parent : Context registry) (polynomials : List parent.Poly) : List (Root parent) :=
  polynomials.flatMap fun p => match parent.roots p with
    | .all => []
    | .finite entries => entries.map (·.root)

/-- Insert by native value comparison, retaining one representative of equal roots. -/
@[expose] def insert (context : Context registry) (value : context.Value) :
    List context.Value → List context.Value
  | [] => [value]
  | next :: rest => match context.compare value next with
    | .lt => value :: next :: rest
    | .eq => next :: rest
    | .gt => next :: insert context value rest

/-- Sort the collected boundaries and remove semantic duplicate roots. -/
@[expose] def boundaries (context : Context registry) (values : List context.Value) : List context.Value :=
  values.foldl (fun sorted value => insert context value sorted) []

/-- A complete polynomial family in one native arithmetic context. The erased
bindings retain the actual root producer, collection and boundary sorting. -/
structure Partition (parent : Context registry) (polynomials : List parent.Poly) : Type 1 where
  private mk ::
  collection : Collection parent
  collected : collection = parent.collect (roots parent polynomials)
  values : List collection.input.context.Value
  ordered : values = boundaries collection.input.context collection.values

/-- Construct every boundary from actual complete roots before selecting sectors. -/
def partition (parent : Context registry) (polynomials : List parent.Poly) :
    Partition parent polynomials :=
  let collection := parent.collect (roots parent polynomials)
  Partition.mk collection rfl (boundaries collection.input.context collection.values) rfl

private def bounded (context : Context registry) (lower upper : context.Value) : context.Value × Cell context :=
  (((lower + upper) / (1 + 1)), .sector (.finite lower) (.finite upper))

private def leftRay (context : Context registry) (upper : context.Value) : context.Value × Cell context :=
  (upper - 1, .sector .negInf (.finite upper))

private def rightRay (context : Context registry) (lower : context.Value) : context.Value × Cell context :=
  (lower + 1, .sector (.finite lower) .posInf)

private def between (context : Context registry) (lower : context.Value) :
    List context.Value → List (context.Value × Cell context)
  | [] => [rightRay context lower]
  | upper :: rest => bounded context lower upper :: between context upper rest

private def sectors (context : Context registry) :
    List context.Value → List (context.Value × Cell context)
  | [] => [(0, .sector .negInf .posInf)]
  | first :: rest => leftRay context first :: between context first rest

/-- Sections at each distinct boundary, using the single common context. -/
def Partition.sections {polynomials : List parent.Poly} (family : Partition parent polynomials) :
    List (Sample parent) :=
  family.values.map fun value =>
    Sample.mk family.collection.input value (.section value)

/-- Midpoints between adjacent complete boundaries and offsets on the two rays.
The root-free whole line uses zero. No rational separation of roots is assumed. -/
def Partition.sectors {polynomials : List parent.Poly} (family : Partition parent polynomials) :
    List (Sample parent) :=
  (Sample.sectors family.collection.input.context family.values).map fun (value, cell) =>
    Sample.mk family.collection.input value cell

/-- Request a sector by its position in the complete ordered family. An index
outside that list is rejected, rather than accepting incomplete boundaries. -/
def Partition.sector? {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (index : Nat) : Option (Sample parent) := family.sectors[index]?

end Sample
end Hex.RealClosure.Tower
