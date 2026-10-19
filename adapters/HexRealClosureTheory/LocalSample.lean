/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Sample
public import HexRealClosureTheory.RootList
import all HexRealClosure.Sample
import all HexRealClosureTheory.Sample

public section

namespace Hex.RealClosure.Tower.Sample
variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Interpret a cell's original boundary handles in one common ambient field. -/
@[expose] def Region.Mem (original : Model parent K) : Region parent → K → Prop
  | .section root, x => root.denote original = x
  | .whole, _ => True
  | .left upper, x => x < upper.denote original
  | .right lower, x => lower.denote original < x
  | .between lower upper, x => lower.denote original < x ∧ x < upper.denote original

/-- A bounded sector must have strictly ordered boundaries. -/
@[expose] def Region.Ordered (original : Model parent K) : Region parent → Prop
  | .between lower upper => lower.denote original < upper.denote original
  | _ => True

private theorem pair_values (original : Model parent K) (a b : Root parent)
    (model : Collection.Model (parent.collect [a, b]) original) :
    model.input.target.value ((parent.collect [a, b]).values.headD 0) = a.denote original ∧
    model.input.target.value (((parent.collect [a, b]).values.drop 1).headD 0) = b.denote original := by
  have values := model.values
  rw [Context.collect_sources original] at values
  simp only [List.map_cons, List.map_nil] at values
  have zero : model.input.target.value 0 = 0 := (model.input.target.zero_iff 0).mpr rfl
  constructor
  · have head := congrArg (fun xs : List K => xs.headD 0) values
    simpa only [← zero, List.headD_map, List.headD_cons] using head
  · have head := congrArg (fun xs : List K => (xs.drop 1).headD 0) values
    simpa only [← zero, ← List.map_drop, List.headD_map,
      List.drop_succ_cons, List.drop_zero, List.headD_cons] using head

/-- Each sample's actual local context preserves the original coefficients and
has exactly the interpreted section or sector specified by its root handles. -/
theorem Region.sample_correct (original : Model parent K) (region : Region parent)
    (ordered : region.Ordered original) :
    ∃ realization : Conversion.Model region.sample.input original,
      region.sample.cell.contains region.sample.value = true ∧
      ∀ x, region.sample.cell.Mem realization.target x ↔ region.Mem original x := by
  cases region with
  | «section» root =>
    obtain ⟨realization, inside, _, value⟩ := ofRoot_correct root original
    refine ⟨realization, inside, ?_⟩
    intro x
    change realization.target.value (Tower.Sample.ofRoot root).value = x ↔ root.denote original = x
    rw [value]
  | whole =>
    refine ⟨Conversion.Model.identity original, ?_, ?_⟩
    · rfl
    · intro x; simp [Region.sample, Cell.Mem, Region.Mem]
  | left root =>
    let realization := root.conversionModel original
    refine ⟨realization, ?_, ?_⟩
    · apply (Cell.contains_correct realization.target _ _).mpr
      change True ∧ realization.target.value (root.convertedValue - 1) <
        realization.target.value root.convertedValue
      rw [realization.target.sub, realization.target.one]
      exact ⟨trivial, sub_one_lt _⟩
    · intro x
      change (True ∧ x < realization.target.value root.convertedValue) ↔ x < root.denote original
      rw [root.convertedValue_value original]
      simp
  | right root =>
    let realization := root.conversionModel original
    refine ⟨realization, ?_, ?_⟩
    · apply (Cell.contains_correct realization.target _ _).mpr
      change realization.target.value root.convertedValue <
        realization.target.value (root.convertedValue + 1) ∧ True
      rw [realization.target.add, realization.target.one]
      exact ⟨lt_add_one _, trivial⟩
    · intro x
      change (realization.target.value root.convertedValue < x ∧ True) ↔ root.denote original < x
      rw [root.convertedValue_value original]
      simp
  | between a b =>
    obtain ⟨model⟩ := (Context.collect_success original [a, b]).2
    obtain ⟨lower, upper⟩ := pair_values original a b model
    refine ⟨model.input, ?_, ?_⟩
    · apply (Cell.contains_correct model.input.target _ _).mpr
      change model.input.target.value ((parent.collect [a, b]).values.headD 0) <
          model.input.target.value
            ((((parent.collect [a, b]).values.headD 0 +
              ((parent.collect [a, b]).values.drop 1).headD 0) / (1 + 1))) ∧
        model.input.target.value
            ((((parent.collect [a, b]).values.headD 0 +
              ((parent.collect [a, b]).values.drop 1).headD 0) / (1 + 1))) <
          model.input.target.value (((parent.collect [a, b]).values.drop 1).headD 0)
      rw [model.input.target.div, model.input.target.add, model.input.target.add,
        model.input.target.one, lower, upper]
      change a.denote original < b.denote original at ordered
      constructor <;> linarith
    · intro x
      change (_ < x ∧ x < _) ↔ a.denote original < x ∧ x < b.denote original
      rw [lower, upper]

/-- Boundary handles are strictly ordered in every compatible ambient model. -/
theorem Family.sorted {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) :
    family.boundaries.Pairwise (fun a b => a.denote original < b.denote original) := by
  rw [family.produced]
  exact Root.sort_sorted original _

/-- Sorting before context construction retains exactly the complete roots. -/
theorem Family.coverage {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (x : K) :
    x ∈ family.boundaries.map (fun root => root.denote original) ↔
      ∃ p ∈ polynomials, HexPolyTheory.Interpret.interpret original.value original.zero_iff p ≠ 0 ∧
        (HexPolyTheory.Interpret.interpret original.value original.zero_iff p).IsRoot x := by
  rw [family.produced, Root.sort_mem]
  exact roots_mem original polynomials x


private theorem afterRegions_correct (original : Model parent K) (lower : Root parent)
    (rest : List (Root parent))
    (ordered : (lower :: rest).Pairwise (fun a b => a.denote original < b.denote original))
    (region : Region parent) (present : region ∈ afterRegions lower rest) :
    region.Ordered original ∧ ∀ x, region.Mem original x →
      lower.denote original < x ∧ ∀ root ∈ lower :: rest, root.denote original ≠ x := by
  induction rest generalizing lower region with
  | nil =>
    simp only [afterRegions, List.mem_singleton] at present
    subst region
    refine ⟨trivial, ?_⟩
    intro x inside
    exact ⟨inside, fun root member => by
      simp only [List.mem_singleton] at member
      subst root
      exact ne_of_lt inside⟩
  | cons upper rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    have less := before upper (List.mem_cons_self ..)
    simp only [afterRegions, List.mem_cons] at present
    rcases present with rfl | later
    · refine ⟨less, ?_⟩
      intro x inside
      obtain ⟨left, right⟩ := inside
      refine ⟨left, ?_⟩
      intro root member
      rcases List.mem_cons.mp member with rfl | afterLower
      · exact ne_of_lt left
      · rcases List.mem_cons.mp afterLower with rfl | afterUpper
        · exact ne_of_gt right
        · exact ne_of_gt (right.trans ((List.pairwise_cons.mp tail).1 root afterUpper))
    · obtain ⟨valid, property⟩ := ih upper tail region later
      refine ⟨valid, ?_⟩
      intro x inside
      obtain ⟨above, excluded⟩ := property x inside
      refine ⟨less.trans above, ?_⟩
      intro root member
      rcases List.mem_cons.mp member with rfl | afterLower
      · exact ne_of_lt (less.trans above)
      · exact excluded root afterLower

/-- Every actual sector is ordered and contains no finite boundary of the
complete family, irrespective of which local arithmetic context it uses. -/
theorem Family.regions_correct {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (region : Region parent) (present : region ∈ family.regions) :
    region.Ordered original ∧ ∀ x, region.Mem original x →
      ∀ root ∈ family.boundaries, root.denote original ≠ x := by
  have ordered := family.sorted original
  cases boundaries : family.boundaries with
  | nil =>
    simp only [Family.regions, boundaries, List.mem_singleton] at present
    subst region
    exact ⟨trivial, fun _ _ root member => False.elim (by simpa [boundaries] using member)⟩
  | cons first rest =>
    rw [boundaries] at ordered
    simp only [Family.regions, boundaries, List.mem_cons] at present
    rcases present with rfl | later
    · refine ⟨trivial, ?_⟩
      intro x inside root member
      rcases List.mem_cons.mp member with rfl | afterFirst
      · exact ne_of_gt inside
      · exact ne_of_gt (inside.trans ((List.pairwise_cons.mp ordered).1 root afterFirst))
    · obtain ⟨valid, property⟩ := afterRegions_correct original first rest ordered region later
      exact ⟨valid, fun x inside root member => (property x inside).2 root member⟩

/-- One actual local sector interpretation supplies both the original interval
and its constant computed sign vector. -/
theorem Family.region_signs {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (region : Region parent) (present : region ∈ family.regions) :
    ∃ realization : Conversion.Model region.sample.input original,
      region.sample.cell.contains region.sample.value = true ∧
      (∀ x, region.sample.cell.Mem realization.target x ↔ region.Mem original x) ∧
      ∀ x, region.Mem original x →
        region.sample.signs polynomials = polynomials.map (fun p => (SignType.sign
          ((HexPolyTheory.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  obtain ⟨ordered, excludes⟩ := family.regions_correct original region present
  obtain ⟨realization, checked, cell⟩ := region.sample_correct original ordered
  refine ⟨realization, checked, cell, ?_⟩
  have inside := (Cell.contains_correct realization.target _ _).mp checked
  intro x contained
  rw [signs_correct region.sample original realization polynomials]
  apply List.map_congr_left
  intro p polynomial
  by_cases zero : HexPolyTheory.Interpret.interpret original.value original.zero_iff p = 0
  · simp only [zero, Polynomial.eval_zero]
  · apply congrArg (fun s : SignType => (s : Int))
    apply region.sample.cell.sign_eq realization.target _ inside ((cell x).mpr contained)
    intro y hy vanishes
    have root := (family.coverage original y).mpr ⟨p, polynomial, zero, vanishes⟩
    obtain ⟨boundary, present, value⟩ := List.mem_map.mp root
    exact excludes y ((cell y).mp hy) boundary present value

/-- Each returned sector has one compatible local interpretation for membership
and sign evaluation. -/
theorem Family.sector_signs {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (sample : Tower.Sample parent) (present : sample ∈ family.sectors) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.contains sample.value = true ∧ ∀ x, sample.cell.Mem realization.target x →
        sample.signs polynomials = polynomials.map (fun p => (SignType.sign
          ((HexPolyTheory.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  obtain ⟨region, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨realization, checked, cell, signs⟩ := family.region_signs original region member
  exact ⟨realization, checked, fun x inside => signs x ((cell x).mp inside)⟩

/-- Every actual section retains its original selected boundary and computes
the input signs at that boundary. -/
theorem Family.sections_correct {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (sample : Tower.Sample parent) (present : sample ∈ family.sections) :
    ∃ root ∈ family.boundaries, sample = Tower.Sample.ofRoot root ∧
      sample.cell.contains sample.value = true ∧
      sample.signs polynomials = polynomials.map (fun p => (SignType.sign
        ((HexPolyTheory.Interpret.interpret original.value original.zero_iff p).eval
          (root.denote original)) : Int)) := by
  obtain ⟨root, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨realization, checked, _, value⟩ := ofRoot_correct root original
  refine ⟨root, member, rfl, checked, ?_⟩
  rw [signs_correct _ original realization polynomials, value]

/-- Every cell sample is a member of its native cell and computes the input
signs at every original-model point belonging to that cell. -/
theorem Family.cell_signs {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (region : Region parent) (present : region ∈ family.cells) :
    region.sample.cell.contains region.sample.value = true ∧
      ∀ x, region.Mem original x → region.sample.signs polynomials = polynomials.map (fun p =>
        (SignType.sign ((HexPolyTheory.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  rcases List.mem_append.mp present with sectionMember | sectorMember
  · obtain ⟨root, member, rfl⟩ := List.mem_map.mp sectionMember
    obtain ⟨realization, checked, _, value⟩ := ofRoot_correct root original
    refine ⟨checked, ?_⟩
    intro x inside
    change root.denote original = x at inside
    change (Tower.Sample.ofRoot root).signs polynomials = _
    rw [signs_correct _ original realization polynomials, value, inside]
  · obtain ⟨realization, checked, _, signs⟩ := family.region_signs original region sectorMember
    exact ⟨checked, signs⟩

private def afterRootCells (lower : Root parent) (rest : List (Root parent)) : List (Region parent) :=
  rest.map Region.section ++ afterRegions lower rest

private theorem afterRootCells_cons (lower upper : Root parent) (rest : List (Root parent))
    (region : Region parent) :
    region ∈ afterRootCells lower (upper :: rest) ↔
      region = .between lower upper ∨ region = .section upper ∨
        region ∈ afterRootCells upper rest := by
  simp only [afterRootCells, afterRegions, List.map_cons, List.mem_append, List.mem_cons]
  tauto

private theorem afterRootCells_above (original : Model parent K) (lower : Root parent)
    (rest : List (Root parent))
    (ordered : (lower :: rest).Pairwise (fun a b => a.denote original < b.denote original))
    (region : Region parent) (member : region ∈ afterRootCells lower rest)
    (x : K) (inside : region.Mem original x) : lower.denote original < x := by
  rcases List.mem_append.mp member with sectionMember | sectorMember
  · obtain ⟨boundary, present, rfl⟩ := List.mem_map.mp sectionMember
    exact inside ▸ (List.pairwise_cons.mp ordered).1 boundary present
  · exact ((afterRegions_correct original lower rest ordered region sectorMember).2 x inside).1

private theorem afterRootCells_unique (original : Model parent K) (lower : Root parent)
    (rest : List (Root parent))
    (ordered : (lower :: rest).Pairwise (fun a b => a.denote original < b.denote original))
    (x : K) (above : lower.denote original < x) :
    ∃! region, region ∈ afterRootCells lower rest ∧ region.Mem original x := by
  induction rest generalizing lower with
  | nil =>
    simp only [afterRootCells, afterRegions, List.map_nil, List.nil_append, List.mem_singleton]
    exact ⟨.right lower, ⟨rfl, above⟩, fun _ h => h.1⟩
  | cons upper rest ih =>
    have tail := (List.pairwise_cons.mp ordered).2
    by_cases less : x < upper.denote original
    · refine ⟨.between lower upper,
        ⟨(afterRootCells_cons lower upper rest _).mpr (Or.inl rfl), above, less⟩, ?_⟩
      rintro other ⟨member, inside⟩
      rcases (afterRootCells_cons lower upper rest other).mp member with same | same | later
      · exact same
      · subst other
        change upper.denote original = x at inside
        exact False.elim ((lt_irrefl _) (inside ▸ less))
      · exact False.elim ((not_lt_of_ge less.le)
          (afterRootCells_above original upper rest tail other later x inside))
    · by_cases equal : x = upper.denote original
      · refine ⟨.section upper,
          ⟨(afterRootCells_cons lower upper rest _).mpr (Or.inr (Or.inl rfl)), equal.symm⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (afterRootCells_cons lower upper rest other).mp member with same | same | later
        · subst other
          exact False.elim ((lt_irrefl _) (equal ▸ inside.2))
        · exact same
        · exact False.elim ((lt_irrefl _) (equal ▸
            afterRootCells_above original upper rest tail other later x inside))
      · have greater : upper.denote original < x := by order
        obtain ⟨region, member, unique⟩ := ih upper tail greater
        refine ⟨region, ⟨(afterRootCells_cons lower upper rest _).mpr (Or.inr (Or.inr member.1)),
          member.2⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (afterRootCells_cons lower upper rest other).mp member with same | same | later
        · subst other
          exact False.elim ((not_lt_of_ge greater.le) inside.2)
        · subst other
          exact False.elim (equal inside.symm)
        · exact unique other ⟨later, inside⟩

/-- Every ambient point belongs to exactly one actual section or sector,
with no shared arithmetic context needed for all roots. -/
theorem Family.cells_unique {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (x : K) :
    ∃! region, region ∈ family.cells ∧ region.Mem original x := by
  cases boundaries : family.boundaries with
  | nil =>
    simp only [Family.cells, boundaries, List.map_nil, List.nil_append, Family.regions,
      boundaries, List.mem_singleton]
    exact ⟨.whole, ⟨rfl, trivial⟩, fun _ h => h.1⟩
  | cons first rest =>
    have ordered : (first :: rest).Pairwise (fun a b => a.denote original < b.denote original) := by
      simpa only [boundaries] using family.sorted original
    have membership (region : Region parent) : region ∈ family.cells ↔
        region = .left first ∨ region = .section first ∨ region ∈ afterRootCells first rest := by
      simp only [Family.cells, boundaries, Family.regions, boundaries, List.map_cons,
        List.mem_append, List.mem_cons, afterRootCells]
      tauto
    by_cases less : x < first.denote original
    · refine ⟨.left first, ⟨(membership _).mpr (Or.inl rfl), less⟩, ?_⟩
      rintro other ⟨member, inside⟩
      rcases (membership other).mp member with same | same | later
      · exact same
      · subst other
        exact False.elim ((lt_irrefl _) (inside ▸ less))
      · exact False.elim ((not_lt_of_ge less.le)
          (afterRootCells_above original first rest ordered other later x inside))
    · by_cases equal : x = first.denote original
      · refine ⟨.section first, ⟨(membership _).mpr (Or.inr (Or.inl rfl)), equal.symm⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (membership other).mp member with same | same | later
        · subst other
          exact False.elim ((lt_irrefl _) (equal ▸ inside))
        · exact same
        · exact False.elim ((lt_irrefl _) (equal ▸
            afterRootCells_above original first rest ordered other later x inside))
      · have greater : first.denote original < x := by order
        obtain ⟨region, member, unique⟩ := afterRootCells_unique original first rest ordered x greater
        refine ⟨region, ⟨(membership _).mpr (Or.inr (Or.inr member.1)), member.2⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (membership other).mp member with same | same | later
        · subst other
          exact False.elim ((not_lt_of_ge greater.le) inside)
        · subst other
          exact False.elim (equal inside.symm)
        · exact unique other ⟨later, inside⟩


/-- The requested open interval, interpreting each endpoint in its original root context. -/
@[expose] def Requested (original : Model parent K) (lower upper : Endpoint (Root parent)) (x : K) : Prop :=
  (match lower with
    | .negInf => True
    | .finite root => root.denote original < x
    | .posInf => False) ∧
  (match upper with
    | .posInf => True
    | .finite root => x < root.denote original
    | .negInf => False)

private theorem matchesRegion_correct (original : Model parent K)
    (lower upper : Endpoint (Root parent)) (region : Region parent) (x : K)
    (accepted : matchesRegion lower upper region = true) :
    region.Mem original x ↔ Requested original lower upper x := by
  have equal (a b : Root parent) : sameRoot a b = true ↔ a.denote original = b.denote original := by
    simp only [sameRoot, decide_eq_true_eq, a.compare_correct b original, compare_eq_iff_eq]
  cases region <;> cases lower <;> cases upper <;>
    simp_all [matchesRegion, equal, Region.Mem, Requested]

/-- Accepted endpoint requests retain the exact requested interval and original
coefficient map in the actual local context of the returned sample. -/
theorem Family.sectorBetween?_correct {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (lower upper : Endpoint (Root parent)) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? lower upper = some sample) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.contains sample.value = true ∧
      ∀ x, sample.cell.Mem realization.target x ↔ Requested original lower upper x := by
  cases found : family.regions.find? (matchesRegion lower upper) with
  | none => simp [Family.sectorBetween?, found] at returned
  | some region =>
    simp only [Family.sectorBetween?, found, Option.map_some, Option.some.injEq] at returned
    subst sample
    have present := List.mem_of_find?_eq_some found
    have accepted := List.find?_some found
    obtain ⟨ordered, _⟩ := family.regions_correct original region present
    obtain ⟨realization, checked, same⟩ := region.sample_correct original ordered
    exact ⟨realization, checked, fun x => (same x).trans
      (matchesRegion_correct original lower upper region x accepted)⟩

/-- An accepted request computes the input signs at every point of the exact
requested original-model interval, without combining unrelated witnesses. -/
theorem Family.sectorBetween?_signs {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (lower upper : Endpoint (Root parent)) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? lower upper = some sample) (x : K)
    (inside : Requested original lower upper x) :
    sample.signs polynomials = polynomials.map (fun p => (SignType.sign
      ((HexPolyTheory.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  cases found : family.regions.find? (matchesRegion lower upper) with
  | none => simp [Family.sectorBetween?, found] at returned
  | some region =>
    simp only [Family.sectorBetween?, found, Option.map_some, Option.some.injEq] at returned
    subst sample
    obtain ⟨realization, checked, cell, signs⟩ :=
      family.region_signs original region (List.mem_of_find?_eq_some found)
    exact signs x ((matchesRegion_correct original lower upper region x
      (List.find?_some found)).mpr inside)

private theorem matchesRegion_eq (original : Model parent K) (lower upper : Endpoint (Root parent))
    (region : Region parent) (a b : Endpoint (Root parent))
    (coordinates : region.endpoints? = some (a, b))
    (left : lower.map (fun root => root.denote original) = a.map (fun root => root.denote original))
    (right : upper.map (fun root => root.denote original) = b.map (fun root => root.denote original)) :
    matchesRegion lower upper region = true := by
  have equal (c d : Root parent) : sameRoot c d = true ↔ c.denote original = d.denote original := by
    simp only [sameRoot, decide_eq_true_eq, c.compare_correct d original, compare_eq_iff_eq]
  cases region <;> simp [Region.endpoints?] at coordinates
  all_goals rcases coordinates with ⟨rfl, rfl⟩
  all_goals cases lower <;> cases upper <;> simp_all [matchesRegion, Endpoint.map, equal]

/-- Any actual adjacent sector succeeds when requested with roots denoting the
same endpoints, even if those roots use different valid defining polynomials. -/
theorem Family.sectorBetween?_success {polynomials : List parent.Poly} (family : Family parent polynomials)
    (original : Model parent K) (region : Region parent) (present : region ∈ family.regions)
    (lower upper a b : Endpoint (Root parent)) (coordinates : region.endpoints? = some (a, b))
    (left : lower.map (fun root => root.denote original) = a.map (fun root => root.denote original))
    (right : upper.map (fun root => root.denote original) = b.map (fun root => root.denote original)) :
    ∃ sample, family.sectorBetween? lower upper = some sample := by
  have accepted := matchesRegion_eq original lower upper region a b coordinates left right
  have foundSome := List.find?_isSome.mpr ⟨region, present, accepted⟩
  cases found : family.regions.find? (matchesRegion lower upper) with
  | none => simp [found] at foundSome
  | some region => exact ⟨region.sample, by simp [Family.sectorBetween?, found]⟩

end Hex.RealClosure.Tower.Sample

/-- info: 'Hex.RealClosure.Tower.Sample.Region.sample_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Region.sample_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Family.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.coverage

/-- info: 'Hex.RealClosure.Tower.Sample.Family.sector_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.sector_signs

/-- info: 'Hex.RealClosure.Tower.Sample.Family.region_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.region_signs

/-- info: 'Hex.RealClosure.Tower.Sample.Family.cell_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.cell_signs

/-- info: 'Hex.RealClosure.Tower.Sample.Family.sections_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.sections_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Family.sectorBetween?_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.sectorBetween?_signs

/-- info: 'Hex.RealClosure.Tower.Sample.Family.cells_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.cells_unique

/-- info: 'Hex.RealClosure.Tower.Sample.Family.sectorBetween?_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.sectorBetween?_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Family.sectorBetween?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Family.sectorBetween?_success
