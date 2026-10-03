/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootCollection
public import HexRealClosure.RootList
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

/-- An ordinary native sample and the explicit inclusion of its coefficients.
Membership is a property of its producer, proved in the companion. -/
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
@[expose] def Sample.section (parent : Context registry)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature) : Sample parent :=
  Sample.ofRoot (Root.ofSelection parent (.selected descriptor))

/-- The public descriptor constructor uses the actual cached root section. -/
theorem Sample.section_eq (parent : Context registry)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature) :
    Sample.section parent descriptor = Sample.ofRoot (Root.ofSelection parent (.selected descriptor)) := rfl

/-- Keep a sample's actual input ownership together with its cell. -/
@[expose] def Sample.cellView (sample : Sample parent) :
    (input : Conversion parent) × Cell input.context := ⟨sample.input, sample.cell⟩

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
  values.reverse.foldl (fun sorted value => insert context value sorted) []

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
@[expose] def Partition.sector? {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (index : Nat) : Option (Sample parent) := family.sectors[index]?

/-- The actual section and sector cells in the common coefficient context. -/
def Partition.cells {polynomials : List parent.Poly} (family : Partition parent polynomials) :
    List (Cell family.collection.input.context) :=
  family.values.map Cell.section ++
    (Sample.sectors family.collection.input.context family.values).map Prod.snd

/-- The cell partition is exactly the cells of the returned samples, with
their common coefficient conversion retained in each dependent pair. -/
theorem Partition.cells_eq {polynomials : List parent.Poly} (family : Partition parent polynomials) :
    (family.sections ++ family.sectors).map Tower.Sample.cellView =
      family.cells.map (fun cell => ⟨family.collection.input, cell⟩) := by
  simp only [Partition.sections, Partition.sectors, Partition.cells, Tower.Sample.cellView,
    List.map_append, List.map_map, Function.comp_def]

private def sameEndpoint (context : Context registry) : Endpoint context.Value → Endpoint context.Value → Bool
  | .negInf, .negInf | .posInf, .posInf => true
  | .finite a, .finite b => context.equal a b
  | _, _ => false

private def requested (context : Context registry) (lower upper : Endpoint context.Value)
    (point : context.Value × Cell context) : Bool :=
  match point.2 with
  | .section _ => false
  | .sector a b => sameEndpoint context lower a && sameEndpoint context upper b

/-- Check requested boundaries against the complete adjacent sector family.
Finite boundaries are compared by value; non-adjacent requests are rejected. -/
def Partition.sectorBetween? {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (lower upper : Endpoint family.collection.input.context.Value) : Option (Tower.Sample parent) :=
  ((Sample.sectors family.collection.input.context family.values).find?
    (requested family.collection.input.context lower upper)).map fun point =>
      Tower.Sample.mk family.collection.input point.1 point.2

private theorem between_length (context : Context registry) (lower : context.Value)
    (rest : List context.Value) : (between context lower rest).length = rest.length + 1 := by
  induction rest generalizing lower with
  | nil => rfl
  | cons upper rest ih => simp [between, ih, Nat.add_comm, Nat.add_left_comm]

/-- There is one section per distinct boundary. -/
theorem Partition.sections_length {polynomials : List parent.Poly} (family : Partition parent polynomials) :
    family.sections.length = family.values.length := by
  simp only [Partition.sections, List.length_map]

/-- Every finite ordered boundary list has both exterior sectors. -/
theorem Partition.sectors_length {polynomials : List parent.Poly} (family : Partition parent polynomials) :
    family.sectors.length = family.values.length + 1 := by
  simp only [Partition.sectors, List.length_map]
  cases family.values with
  | nil => rfl
  | cons first rest =>
    simpa only [Sample.sectors, List.length_cons] using
      congrArg (fun n => n + 1) (between_length family.collection.input.context first rest)

/-- A root-free partition contains the whole-line sector. -/
theorem Partition.wholeLine_mem {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (empty : family.values = []) : Cell.sector .negInf .posInf ∈ family.cells := by
  simp [Partition.cells, empty, Sample.sectors]

/-- The first boundary of a nonempty partition has its exterior left ray. -/
theorem Partition.leftRay_mem {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (first : family.collection.input.context.Value) (rest : List family.collection.input.context.Value)
    (values : family.values = first :: rest) :
    Cell.sector .negInf (.finite first) ∈ family.cells := by
  simp [Partition.cells, values, Sample.sectors, leftRay]

/-- The final boundary of a nonempty partition has its exterior right ray. -/
theorem Partition.rightRay_mem {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (before : List family.collection.input.context.Value) (last : family.collection.input.context.Value)
    (values : family.values = before ++ [last]) :
    Cell.sector (.finite last) .posInf ∈ family.cells := by
  have tail : ∀ first earlier, Cell.sector (.finite last) .posInf ∈
      (between family.collection.input.context first (earlier ++ [last])).map Prod.snd := by
    intro first earlier
    induction earlier generalizing first with
    | nil => simp [between, rightRay]
    | cons next rest ih =>
      simp only [List.cons_append, between, List.map_cons]
      exact List.mem_cons_of_mem _ (ih next)
  cases before with
  | nil => simp [Partition.cells, values, Sample.sectors, between, rightRay]
  | cons first rest =>
    simp only [Partition.cells, values, List.cons_append, Sample.sectors, List.map_cons]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (tail first rest)))

/-- Consecutive boundaries in the complete list define an actual bounded sector. -/
theorem Partition.bounded_mem {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (before after : List family.collection.input.context.Value)
    (lower upper : family.collection.input.context.Value)
    (values : family.values = before ++ lower :: upper :: after) :
    Cell.sector (.finite lower) (.finite upper) ∈ family.cells := by
  have tail : ∀ first earlier, Cell.sector (.finite lower) (.finite upper) ∈
      (between family.collection.input.context first (earlier ++ lower :: upper :: after)).map Prod.snd := by
    intro first earlier
    induction earlier generalizing first with
    | nil => simp [between, bounded]
    | cons next rest ih =>
      simp only [List.cons_append, between, List.map_cons]
      exact List.mem_cons_of_mem _ (ih next)
  cases before with
  | nil => simp [Partition.cells, values, Sample.sectors, between, bounded]
  | cons first rest =>
    simp only [Partition.cells, values, List.cons_append, Sample.sectors, List.map_cons]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (tail first rest)))

/-- Every returned section retains the same actual coefficient conversion. -/
theorem Partition.sections_input {polynomials : List parent.Poly} (family : Partition parent polynomials)
    {sample : Sample parent} (present : sample ∈ family.sections) :
    sample.input = family.collection.input := by
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp present
  rfl

/-- Every returned sector retains the same actual coefficient conversion. -/
theorem Partition.sectors_input {polynomials : List parent.Poly} (family : Partition parent polynomials)
    {sample : Sample parent} (present : sample ∈ family.sectors) :
    sample.input = family.collection.input := by
  obtain ⟨point, _, rfl⟩ := List.mem_map.mp present
  rfl

/-- Every sector position from zero through the final exterior ray succeeds. -/
theorem Partition.sector?_success {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (index : Nat) (valid : index ≤ family.values.length) :
    ∃ sample, family.sector? index = some sample := by
  have bounds : index < family.sectors.length := by
    rw [family.sectors_length]
    exact Nat.lt_succ_iff.mpr valid
  exact ⟨family.sectors[index]'bounds, List.getElem?_eq_some_iff.mpr ⟨bounds, rfl⟩⟩

/-- Only positions beyond the complete sector family are rejected. -/
theorem Partition.sector?_none {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (index : Nat) : family.sector? index = none ↔ family.values.length < index := by
  rw [Partition.sector?, List.getElem?_eq_none_iff, family.sectors_length]
  omega

/-- Indexed sector results belong to the actual complete sample list. -/
theorem Partition.sector?_mem {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (index : Nat) (sample : Tower.Sample parent) (returned : family.sector? index = some sample) :
    sample ∈ family.sectors := by
  obtain ⟨bounds, equal⟩ := List.getElem?_eq_some_iff.mp returned
  exact equal ▸ List.getElem_mem bounds

/-- A successful boundary request returns an actual sector of the complete family. -/
theorem Partition.sectorBetween?_mem {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (lower upper : Endpoint family.collection.input.context.Value) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? lower upper = some sample) : sample ∈ family.sectors := by
  cases found : (Sample.sectors family.collection.input.context family.values).find?
      (requested family.collection.input.context lower upper) with
  | none => simp [Partition.sectorBetween?, found] at returned
  | some point =>
    simp only [Partition.sectorBetween?, found, Option.map_some, Option.some.injEq] at returned
    subst sample
    exact List.mem_map.mpr ⟨point, List.mem_of_find?_eq_some found, rfl⟩


/-- A section or sector retaining root handles in their original contexts.
Only the finite boundaries of a requested cell enter its arithmetic context. -/
inductive Region (parent : Context registry) : Type 1 where
  | section (root : Root parent)
  | whole
  | left (upper : Root parent)
  | right (lower : Root parent)
  | between (lower upper : Root parent)

/-- A sector's original finite boundary handles; sections have no open interval. -/
@[expose] def Region.endpoints? : Region parent → Option (Endpoint (Root parent) × Endpoint (Root parent))
  | .section _ => none
  | .whole => some (.negInf, .posInf)
  | .left upper => some (.negInf, .finite upper)
  | .right lower => some (.finite lower, .posInf)
  | .between lower upper => some (.finite lower, .finite upper)

/-- Construct the ordinary native value for one cell. Sections reuse the cached
root child; rays use one root; bounded sectors collect exactly two roots.
Membership of a bounded midpoint requires the lower root to precede the upper. -/
def Region.sample : Region parent → Tower.Sample parent
  | .section root => Tower.Sample.ofRoot root
  | .whole => Tower.Sample.mk (Conversion.identity parent) 0 (.sector .negInf .posInf)
  | .left root => Tower.Sample.mk root.conversion (root.convertedValue - 1)
      (.sector .negInf (.finite root.convertedValue))
  | .right root => Tower.Sample.mk root.conversion (root.convertedValue + 1)
      (.sector (.finite root.convertedValue) .posInf)
  | .between lower upper =>
      let pair := parent.collect [lower, upper]
      let a := pair.values.headD 0
      let b := (pair.values.drop 1).headD 0
      Tower.Sample.mk pair.input ((a + b) / (1 + 1)) (.sector (.finite a) (.finite b))

/-- A complete family ordered and deduplicated before any shared arithmetic
context is constructed. Each returned sample has its own immutable context. -/
structure Family (parent : Context registry) (polynomials : List parent.Poly) : Type 1 where
  private mk ::
  boundaries : List (Root parent)
  produced : boundaries = Root.sort (roots parent polynomials)

/-- Find complete roots and retain one native root handle per distinct value. -/
def family (parent : Context registry) (polynomials : List parent.Poly) : Family parent polynomials :=
  Family.mk (Root.sort (roots parent polynomials)) rfl

@[expose] def afterRegions (lower : Root parent) : List (Root parent) → List (Region parent)
  | [] => [.right lower]
  | upper :: rest => .between lower upper :: afterRegions upper rest

/-- The complete sector list described by original root handles. -/
@[expose] def Family.regions {polynomials : List parent.Poly} (family : Family parent polynomials) :
    List (Region parent) :=
  match family.boundaries with
  | [] => [.whole]
  | first :: rest => .left first :: afterRegions first rest

/-- One section per distinct root, with its cached root context. -/
def Family.sections {polynomials : List parent.Poly} (family : Family parent polynomials) :
    List (Tower.Sample parent) := family.boundaries.map Tower.Sample.ofRoot

/-- Construct each sector using only its own finite boundaries. -/
def Family.sectors {polynomials : List parent.Poly} (family : Family parent polynomials) :
    List (Tower.Sample parent) := family.regions.map Region.sample

/-- All sections and sectors, described independently of their local contexts. -/
def Family.cells {polynomials : List parent.Poly} (family : Family parent polynomials) :
    List (Region parent) := family.boundaries.map Region.section ++ family.regions

/-- A section's local sample is the original cached selected-root sample. -/
theorem Region.sample_section (root : Root parent) :
    (Region.section root).sample = Tower.Sample.ofRoot root := by simp [Region.sample]

/-- Public cell membership retains the original boundary or sector label. -/
theorem Family.mem_cells {polynomials : List parent.Poly} (family : Family parent polynomials)
    (region : Region parent) : region ∈ family.cells ↔
      (∃ root ∈ family.boundaries, region = .section root) ∨ region ∈ family.regions := by
  simp only [Family.cells, List.mem_append, List.mem_map, eq_comm]

/-- The complete cell list describes exactly the returned ordinary samples. -/
theorem Family.cells_eq {polynomials : List parent.Poly} (family : Family parent polynomials) :
    family.sections ++ family.sectors = family.cells.map Region.sample := by
  simp [Family.sections, Family.sectors, Family.cells, Region.sample, List.map_append,
    List.map_map, Function.comp_def]

/-- Select the region before constructing its sample. Requesting one sector
constructs neither other midpoints nor a common context for all roots. -/
def Family.sector? {polynomials : List parent.Poly} (family : Family parent polynomials)
    (index : Nat) : Option (Tower.Sample parent) := family.regions[index]?.map Region.sample

/-- An indexed request samples exactly the original region at that position. -/
theorem Family.sector?_eq {polynomials : List parent.Poly} (family : Family parent polynomials)
    (index : Nat) : family.sector? index = family.regions[index]?.map Region.sample := by
  simp [Family.sector?]

private def sameRoot (a b : Root parent) : Bool := decide (a.compare b = .eq)

private def matchesRegion (lower upper : Endpoint (Root parent)) : Region parent → Bool
  | .whole => match lower, upper with | .negInf, .posInf => true | _, _ => false
  | .left b => match lower, upper with | .negInf, .finite a => sameRoot a b | _, _ => false
  | .right a => match lower, upper with | .finite b, .posInf => sameRoot a b | _, _ => false
  | .between a b => match lower, upper with
      | .finite c, .finite d => sameRoot c a && sameRoot d b
      | _, _ => false
  | .section _ => false

/-- Check semantic endpoint equality against adjacent complete root handles,
then construct just the accepted sector. Non-adjacent requests are rejected. -/
def Family.sectorBetween? {polynomials : List parent.Poly} (family : Family parent polynomials)
    (lower upper : Endpoint (Root parent)) : Option (Tower.Sample parent) :=
  (family.regions.find? (matchesRegion lower upper)).map Region.sample

private theorem afterRegions_length (lower : Root parent) (rest : List (Root parent)) :
    (afterRegions lower rest).length = rest.length + 1 := by
  induction rest generalizing lower with
  | nil => rfl
  | cons upper rest ih => simp [afterRegions, ih, Nat.add_comm, Nat.add_left_comm]

/-- There is one section for each distinct boundary. -/
theorem Family.sections_length {polynomials : List parent.Poly} (family : Family parent polynomials) :
    family.sections.length = family.boundaries.length := by simp [Family.sections]

/-- The complete family has one more sector than finite boundaries. -/
theorem Family.sectors_length {polynomials : List parent.Poly} (family : Family parent polynomials) :
    family.sectors.length = family.boundaries.length + 1 := by
  simp only [Family.sectors, List.length_map]
  cases boundaries : family.boundaries with
  | nil => simp [Family.regions, boundaries]
  | cons first rest =>
    simpa only [Family.regions, boundaries, List.length_cons] using
      congrArg (fun n => n + 1) (afterRegions_length first rest)

/-- A root-free family has the whole-line sector. -/
theorem Family.wholeLine_mem {polynomials : List parent.Poly} (family : Family parent polynomials)
    (empty : family.boundaries = []) : Region.whole ∈ family.regions := by
  simp [Family.regions, empty]

/-- The first root has its exterior left ray. -/
theorem Family.leftRay_mem {polynomials : List parent.Poly} (family : Family parent polynomials)
    (first : Root parent) (rest : List (Root parent)) (boundaries : family.boundaries = first :: rest) :
    Region.left first ∈ family.regions := by simp [Family.regions, boundaries]

/-- The last root has its exterior right ray. -/
theorem Family.rightRay_mem {polynomials : List parent.Poly} (family : Family parent polynomials)
    (before : List (Root parent)) (last : Root parent) (boundaries : family.boundaries = before ++ [last]) :
    Region.right last ∈ family.regions := by
  have tail : ∀ first earlier, Region.right last ∈ afterRegions first (earlier ++ [last]) := by
    intro first earlier
    induction earlier generalizing first with
    | nil => simp [afterRegions]
    | cons next rest ih =>
      simp only [List.cons_append, afterRegions, List.mem_cons]
      exact Or.inr (ih next)
  cases before with
  | nil => simp [Family.regions, boundaries, afterRegions]
  | cons first rest =>
    simp only [Family.regions, boundaries, List.cons_append, List.mem_cons]
    exact Or.inr (tail first rest)

/-- Adjacent roots of the complete family define an actual bounded sector. -/
theorem Family.bounded_mem {polynomials : List parent.Poly} (family : Family parent polynomials)
    (before after : List (Root parent)) (lower upper : Root parent)
    (boundaries : family.boundaries = before ++ lower :: upper :: after) :
    Region.between lower upper ∈ family.regions := by
  have tail : ∀ first earlier, Region.between lower upper ∈
      afterRegions first (earlier ++ lower :: upper :: after) := by
    intro first earlier
    induction earlier generalizing first with
    | nil => simp [afterRegions]
    | cons next rest ih =>
      simp only [List.cons_append, afterRegions, List.mem_cons]
      exact Or.inr (ih next)
  cases before with
  | nil => simp [Family.regions, boundaries, afterRegions]
  | cons first rest =>
    simp only [Family.regions, boundaries, List.cons_append, List.mem_cons]
    exact Or.inr (tail first rest)

/-- Every sector position from zero through the final ray succeeds. -/
theorem Family.sector?_success {polynomials : List parent.Poly} (family : Family parent polynomials)
    (index : Nat) (valid : index ≤ family.boundaries.length) :
    ∃ sample, family.sector? index = some sample := by
  have bounds : index < family.regions.length := by
    have count := family.sectors_length
    simp only [Family.sectors, List.length_map] at count
    rw [count]
    omega
  refine ⟨(family.regions[index]'bounds).sample, ?_⟩
  simp only [Family.sector?, List.getElem?_eq_getElem bounds, Option.map_some]

/-- Only positions beyond the complete sector family are rejected. -/
theorem Family.sector?_none {polynomials : List parent.Poly} (family : Family parent polynomials)
    (index : Nat) : family.sector? index = none ↔ family.boundaries.length < index := by
  have count := family.sectors_length
  simp only [Family.sectors, List.length_map] at count
  rw [Family.sector?, Option.map_eq_none_iff, List.getElem?_eq_none_iff, count]
  omega

/-- The selected sector is one of the actual complete family samples. -/
theorem Family.sector?_mem {polynomials : List parent.Poly} (family : Family parent polynomials)
    (index : Nat) (sample : Tower.Sample parent) (returned : family.sector? index = some sample) :
    sample ∈ family.sectors := by
  cases found : family.regions[index]? with
  | none => simp [Family.sector?, found] at returned
  | some region =>
    simp only [Family.sector?, found, Option.map_some, Option.some.injEq] at returned
    subst sample
    exact List.mem_map.mpr ⟨region, List.mem_of_getElem? found, rfl⟩

/-- Successful endpoint requests select one of the actual complete sectors. -/
theorem Family.sectorBetween?_mem {polynomials : List parent.Poly} (family : Family parent polynomials)
    (lower upper : Endpoint (Root parent)) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? lower upper = some sample) : sample ∈ family.sectors := by
  cases found : family.regions.find? (matchesRegion lower upper) with
  | none => simp [Family.sectorBetween?, found] at returned
  | some region =>
    simp only [Family.sectorBetween?, found, Option.map_some, Option.some.injEq] at returned
    subst sample
    exact List.mem_map.mpr ⟨region, List.mem_of_find?_eq_some found, rfl⟩

end Sample
end Hex.RealClosure.Tower
