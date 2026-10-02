/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Sample
public import HexRealClosureMathlib.RootCollection
import all HexRealClosure.Sample

public section

namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {context parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K]

/-- Membership in the interpreted section or open sector. -/
def Cell.Mem (model : Model context K) (cell : Cell context) (x : K) : Prop :=
  match cell with
  | .section root => model.value root = x
  | .sector lower upper =>
    (match lower with
      | .negInf => True
      | .finite bound => model.value bound < x
      | .posInf => False) ∧
    (match upper with
      | .posInf => True
      | .finite bound => x < model.value bound
      | .negInf => False)

private theorem compare_lt (model : Model context K) (a b : context.Value) :
    context.compare a b = .lt ↔ model.value a < model.value b := by
  rw [model.compare_spec]
  split_ifs <;> simp_all

private theorem compare_eq (model : Model context K) (a b : context.Value) :
    context.compare a b = .eq ↔ model.value a = model.value b := by
  rw [model.compare_spec]
  split_ifs <;> simp_all
  order

private theorem compare_gt (model : Model context K) (a b : context.Value) :
    context.compare a b = .gt ↔ model.value b < model.value a := by
  rw [model.compare_spec]
  split_ifs <;> simp_all <;> order

/-- The actual native membership check uses the interpreted strict boundaries. -/
theorem Cell.contains_correct (model : Model context K) (cell : Cell context) (a : context.Value) :
    cell.contains a = true ↔ cell.Mem model (model.value a) := by
  cases cell with
  | «section» root => simp [Cell.contains, Cell.Mem, model.equal_spec]
  | sector lower upper =>
    cases lower <;> cases upper <;>
      simp [Cell.contains, Cell.Mem, compare_lt model]

namespace Sample

/-- Removing equal boundaries loses no interpreted root value. -/
theorem insert_mem (model : Model context K) (a : context.Value) (values : List context.Value) (x : K) :
    x ∈ (insert context a values).map model.value ↔
      x = model.value a ∨ x ∈ values.map model.value := by
  induction values with
  | nil => simp [insert]
  | cons b rest ih =>
    cases order : context.compare a b with
    | lt => simp [insert, order, eq_comm]
    | eq =>
      have equal := (compare_eq model a b).mp order
      simp [insert, order, equal, eq_comm]
    | gt => simp only [insert, order, List.map_cons, List.mem_cons, ih]; tauto

/-- Native insertion preserves strict order of interpreted, distinct boundaries. -/
theorem insert_sorted (model : Model context K) (a : context.Value) (values : List context.Value)
    (ordered : values.Pairwise (fun a b => model.value a < model.value b)) :
    (insert context a values).Pairwise (fun a b => model.value a < model.value b) := by
  induction values with
  | nil => simp [insert]
  | cons b rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    cases order : context.compare a b with
    | lt =>
      have less := (compare_lt model a b).mp order
      simp only [insert, order, List.pairwise_cons]
      exact ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | present
        · exact less
        · exact less.trans (before x present), before, tail⟩
    | eq => simpa [insert, order] using ordered
    | gt =>
      have greater := (compare_gt model a b).mp order
      simp only [insert, order, List.pairwise_cons]
      refine ⟨?_, ih tail⟩
      intro x present
      have hx : model.value x ∈ (insert context a rest).map model.value := List.mem_map.mpr ⟨x, present, rfl⟩
      rcases (insert_mem model a rest _).mp hx with equal | old
      · exact equal ▸ greater
      · obtain ⟨y, member, same⟩ := List.mem_map.mp old
        exact same ▸ before y member

private theorem fold_mem (model : Model context K) (values sorted : List context.Value) (x : K) :
    x ∈ (values.foldl (fun acc a => insert context a acc) sorted).map model.value ↔
      x ∈ sorted.map model.value ∨ x ∈ values.map model.value := by
  induction values generalizing sorted with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.mem_cons]
    rw [insert_mem model]
    tauto

/-- Boundary sorting retains precisely the same interpreted root values. -/
theorem boundaries_mem (model : Model context K) (values : List context.Value) (x : K) :
    x ∈ (boundaries context values).map model.value ↔ x ∈ values.map model.value := by
  simpa only [boundaries, List.map_nil, List.not_mem_nil, false_or] using fold_mem model values [] x

private theorem fold_sorted (model : Model context K) (values sorted : List context.Value)
    (ordered : sorted.Pairwise (fun a b => model.value a < model.value b)) :
    (values.foldl (fun acc a => insert context a acc) sorted).Pairwise
      (fun a b => model.value a < model.value b) := by
  induction values generalizing sorted with
  | nil => exact ordered
  | cons a rest ih => exact ih _ (insert_sorted model a sorted ordered)

/-- Every boundary occurs once in strict interpreted order. -/
theorem boundaries_sorted (model : Model context K) (values : List context.Value) :
    (boundaries context values).Pairwise (fun a b => model.value a < model.value b) :=
  fold_sorted model values [] (by simp)

omit [DecidableEq K] in
private theorem bounded_mem (model : Model context K) (a b : context.Value)
    (less : model.value a < model.value b) :
    (bounded context a b).2.Mem model (model.value (bounded context a b).1) := by
  simp only [bounded, Cell.Mem, model.div, model.add, model.one]
  norm_num only [show (1 : K) + 1 = 2 by norm_num]
  exact ⟨left_lt_add_div_two.mpr less, add_div_two_lt_right.mpr less⟩

omit [DecidableEq K] in
private theorem between_correct (model : Model context K) (lower : context.Value)
    (rest : List context.Value)
    (ordered : (lower :: rest).Pairwise (fun a b => model.value a < model.value b)) :
    ∀ point ∈ between context lower rest,
      point.2.Mem model (model.value point.1) ∧
      (∀ x, point.2.Mem model x → model.value lower < x) ∧
      (∀ boundary ∈ lower :: rest, ¬ point.2.Mem model (model.value boundary)) := by
  induction rest generalizing lower with
  | nil =>
    intro point member
    simp only [between, List.mem_singleton] at member
    subst point
    simp only [rightRay, Cell.Mem, model.add, model.one, and_true]
    refine ⟨lt_add_one _, fun _ h => h, ?_⟩
    intro boundary member
    simp only [List.mem_singleton] at member
    subst boundary
    exact lt_irrefl _
  | cons upper rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    have less := before upper (by simp)
    intro point member
    rcases List.mem_cons.mp member with rfl | later
    · refine ⟨bounded_mem model lower upper less, fun _ h => h.1, ?_⟩
      intro boundary member contained
      rcases List.mem_cons.mp member with rfl | member
      · exact (lt_irrefl _ contained.1)
      · rcases List.mem_cons.mp member with rfl | member
        · exact (lt_irrefl _ contained.2)
        · have upperLess := (List.pairwise_cons.mp tail).1 boundary member
          exact (not_lt_of_ge upperLess.le) contained.2
    · obtain ⟨valid, above, excluded⟩ := ih upper tail point later
      refine ⟨valid, fun x h => less.trans (above x h), ?_⟩
      intro boundary member contained
      rcases List.mem_cons.mp member with rfl | member
      · exact (not_lt_of_ge less.le) (above _ contained)
      · exact excluded boundary member contained

omit [DecidableEq K] in
private theorem sector_coordinates_correct (model : Model context K) (values : List context.Value)
    (ordered : values.Pairwise (fun a b => model.value a < model.value b)) :
    ∀ point ∈ sectors context values,
      point.2.Mem model (model.value point.1) ∧
      (∀ boundary ∈ values, ¬ point.2.Mem model (model.value boundary)) := by
  cases values with
  | nil => simp [sectors, Cell.Mem]
  | cons first rest =>
    intro point member
    rcases List.mem_cons.mp member with rfl | later
    · refine ⟨?_, ?_⟩
      · simp [leftRay, Cell.Mem, model.sub, model.one]
      · intro boundary member contained
        have before : model.value first ≤ model.value boundary := by
          rcases List.mem_cons.mp member with rfl | member
          · exact le_rfl
          · exact ((List.pairwise_cons.mp ordered).1 boundary member).le
        exact (not_lt_of_ge before) contained.2
    · obtain ⟨valid, _, excluded⟩ := between_correct model first rest ordered point later
      exact ⟨valid, excluded⟩

omit [IsStrictOrderedRing K] in
/-- Sample sign evaluation preserves the requested coefficient inclusion. -/
theorem signs_correct (sample : Tower.Sample parent) (original : Model parent K)
    (model : Conversion.Model sample.input original) (polynomials : List parent.Poly) :
    sample.signs polynomials = polynomials.map (fun p => (SignType.sign
      ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval
        (model.target.value sample.value)) : Int)) := by
  apply List.map_congr_left
  intro p member
  rw [model.target.sign,
    ← HexPolyMathlib.Interpret.eval_interpret model.target.value model.target.zero_iff
      model.target.add model.target.mul]
  congr 2
  apply congrArg (Polynomial.eval (model.target.value sample.value))
  apply Polynomial.ext
  intro i
  rw [HexPolyMathlib.Interpret.coeff_interpret, HexPolyMathlib.Interpret.coeff_interpret]
  have coefficient := Transport.polynomial_coeff sample.input.value
    ((model.target.zero_iff _).mp (by
      rw [model.value]
      exact (original.zero_iff 0).mpr rfl)) p i
  change model.target.value ((Transport.polynomial sample.input.value p).coeff i) =
    original.value (p.coeff i)
  rw [coefficient, model.value]

variable [IsRealClosed K]

/-- A section carries the selected root through its actual cached conversion. -/
theorem ofRoot_correct (root : Root parent) (original : Model parent K) :
    ∃ realization : Conversion.Model (Tower.Sample.ofRoot root).input original,
      (Tower.Sample.ofRoot root).cell.contains (Tower.Sample.ofRoot root).value = true ∧
      (Tower.Sample.ofRoot root).cell.Mem realization.target
        (realization.target.value (Tower.Sample.ofRoot root).value) ∧
      realization.target.value (Tower.Sample.ofRoot root).value = root.denote original := by
  refine ⟨root.conversionModel original, ?_, rfl, root.convertedValue_value original⟩
  exact (Cell.contains_correct (root.conversionModel original).target _ _).mpr rfl

/-- The actual family producer contains exactly the roots of its nonzero members. -/
theorem roots_mem (original : Model parent K) (polynomials : List parent.Poly) (x : K) :
    x ∈ (roots parent polynomials).map (fun root => root.denote original) ↔
      ∃ p ∈ polynomials, HexPolyMathlib.Interpret.interpret original.value original.zero_iff p ≠ 0 ∧
        (HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).IsRoot x := by
  constructor
  · intro present
    obtain ⟨root, member, value⟩ := List.mem_map.mp present
    obtain ⟨p, polynomial, produced⟩ := List.mem_flatMap.mp member
    cases returned : parent.roots p with
    | all => simp [returned] at produced
    | finite entries =>
      simp only [returned] at produced
      obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp produced
      refine ⟨p, polynomial, ?_, ?_⟩
      · intro zero
        have universal := (Context.roots_all original p).mpr zero
        rw [returned] at universal
        cases universal
      · exact ((Context.roots_spec original p returned x entry.multiplicity).mp
          ⟨entry, entryMember, value, rfl⟩).1
  · rintro ⟨p, polynomial, nonzero, root⟩
    obtain ⟨entries, returned, entry, member, value⟩ := original.root_exists p nonzero x root
    apply List.mem_map.mpr
    refine ⟨entry.root, List.mem_flatMap.mpr ⟨p, polynomial, ?_⟩, value⟩
    simp only [returned]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩

/-- The ordinary partition carries an actual compatible shared model. -/
theorem Partition.model {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) : Nonempty (Collection.Model family.collection original) := by
  rw [family.collected]
  exact (Context.collect_success original (roots parent polynomials)).2

/-- The returned boundary values have strict order in every compatible collection model. -/
theorem Partition.sorted {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original) :
    family.values.Pairwise (fun a b => model.input.target.value a < model.input.target.value b) := by
  rw [family.ordered]
  exact boundaries_sorted model.input.target _

/-- Sorting and semantic deduplication preserve the complete family of roots. -/
theorem Partition.coverage {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original) (x : K) :
    x ∈ family.values.map model.input.target.value ↔
      ∃ p ∈ polynomials, HexPolyMathlib.Interpret.interpret original.value original.zero_iff p ≠ 0 ∧
        (HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).IsRoot x := by
  have sources : family.collection.sources = roots parent polynomials := by
    rw [family.collected]
    exact Context.collect_sources original _
  rw [family.ordered, boundaries_mem, model.values, sources]
  exact roots_mem original polynomials x

/-- Every returned sector has an actual compatible interpretation, passes native
strict membership, and contains no root of any nonzero input polynomial. -/
theorem Partition.sectors_correct {polynomials : List parent.Poly}
    (family : Partition parent polynomials) (original : Model parent K)
    (model : Collection.Model family.collection original) (sample : Tower.Sample parent)
    (present : sample ∈ family.sectors) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.contains sample.value = true ∧
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      ∀ x, sample.cell.Mem realization.target x → ∀ p ∈ polynomials,
        HexPolyMathlib.Interpret.interpret original.value original.zero_iff p ≠ 0 →
        ¬ (HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).IsRoot x := by
  obtain ⟨point, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨inside, excluded⟩ := sector_coordinates_correct model.input.target family.values
    (family.sorted original model) point member
  refine ⟨model.input, (Cell.contains_correct model.input.target _ _).mpr inside, inside, ?_⟩
  intro x contained p polynomial nonzero root
  have boundary := (family.coverage original model x).mpr ⟨p, polynomial, nonzero, root⟩
  obtain ⟨value, present, equal⟩ := List.mem_map.mp boundary
  apply excluded value present
  simpa only [equal] using contained

/-- Returned sections use the actual shared collection model and selected value. -/
theorem Partition.sections_correct {polynomials : List parent.Poly}
    (family : Partition parent polynomials) (original : Model parent K)
    (model : Collection.Model family.collection original) (sample : Tower.Sample parent)
    (present : sample ∈ family.sections) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.contains sample.value = true ∧
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      ∃ p ∈ polynomials,
        HexPolyMathlib.Interpret.interpret original.value original.zero_iff p ≠ 0 ∧
        (HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).IsRoot
          (realization.target.value sample.value) := by
  obtain ⟨value, member, rfl⟩ := List.mem_map.mp present
  refine ⟨model.input, ?_, rfl, ?_⟩
  · exact (Cell.contains_correct model.input.target _ _).mpr rfl
  · exact (family.coverage original model _).mp (List.mem_map.mpr ⟨value, member, rfl⟩)


end Sample
end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Cell.contains_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Cell.contains_correct

/-- info: 'Hex.RealClosure.Tower.Sample.signs_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.signs_correct

/-- info: 'Hex.RealClosure.Tower.Sample.ofRoot_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.ofRoot_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.coverage

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.sectors_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.sectors_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.sections_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.sections_correct
