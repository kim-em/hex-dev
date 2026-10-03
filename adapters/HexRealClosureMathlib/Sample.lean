/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Sample
public import HexRealClosureMathlib.RootCollection
public import TauCeti.FieldTheory.RealClosure.IVT
import all HexRealClosure.Sample

public section

namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {context parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K]

/-- Membership in the interpreted section or open sector. -/
@[expose] def Cell.Mem (model : Model context K) (cell : Cell context) (x : K) : Prop :=
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

omit [DecidableEq K] [IsStrictOrderedRing K] in
/-- Every interpreted section or sector contains the interval between its points. -/
theorem Cell.interval_mem (model : Model context K) (cell : Cell context) {a b x : K}
    (left : cell.Mem model a) (right : cell.Mem model b) (bounds : a ≤ x ∧ x ≤ b) :
    cell.Mem model x := by
  cases cell with
  | «section» root => simp only [Cell.Mem] at *; order
  | sector lower upper =>
    cases lower <;> cases upper <;> simp_all [Cell.Mem] <;>
      first | order | (constructor <;> order)

omit [DecidableEq K] in
/-- A root-free polynomial has one sign throughout an interpreted cell, over
any real closed ordered field, including a non-Archimedean field. -/
theorem Cell.sign_eq [IsRealClosed K] (model : Model context K) (cell : Cell context)
    (p : Polynomial K) {a b : K} (left : cell.Mem model a) (right : cell.Mem model b)
    (rootFree : ∀ x, cell.Mem model x → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
  have positive : 0 < p.eval a * p.eval b := by
    rcases le_total a b with before | before
    · exact p.eval_mul_pos_of_no_roots before
        (fun x hx => rootFree x (cell.interval_mem model left right hx))
    · simpa only [mul_comm] using p.eval_mul_pos_of_no_roots before
        (fun x hx => rootFree x (cell.interval_mem model right left hx))
  rcases mul_pos_iff.mp positive with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [sign_eq_one_iff.mpr ha, sign_eq_one_iff.mpr hb]
  · rw [sign_eq_neg_one_iff.mpr ha, sign_eq_neg_one_iff.mpr hb]

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
  simpa only [boundaries, List.map_nil, List.not_mem_nil, false_or, List.map_reverse,
    List.mem_reverse] using fold_mem model values.reverse [] x

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
  fold_sorted model values.reverse [] (by simp)

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

private def afterCells (context : Context registry) (lower : context.Value)
    (rest : List context.Value) : List (Cell context) :=
  rest.map Cell.section ++ (between context lower rest).map Prod.snd

private theorem afterCells_cons (lower upper : context.Value) (rest : List context.Value)
    (cell : Cell context) :
    cell ∈ afterCells context lower (upper :: rest) ↔
      cell = (bounded context lower upper).2 ∨ cell = .section upper ∨
        cell ∈ afterCells context upper rest := by
  simp only [afterCells, between, List.map_cons, List.mem_append, List.mem_cons]
  tauto

omit [DecidableEq K] in
private theorem afterCells_above (model : Model context K) (lower : context.Value)
    (rest : List context.Value)
    (ordered : (lower :: rest).Pairwise (fun a b => model.value a < model.value b))
    (cell : Cell context) (member : cell ∈ afterCells context lower rest)
    (x : K) (inside : cell.Mem model x) : model.value lower < x := by
  rcases List.mem_append.mp member with sectionMember | sectorMember
  · obtain ⟨boundary, present, rfl⟩ := List.mem_map.mp sectionMember
    exact inside ▸ (List.pairwise_cons.mp ordered).1 boundary present
  · obtain ⟨point, present, equal⟩ := List.mem_map.mp sectorMember
    rw [← equal] at inside
    exact (between_correct model lower rest ordered point present).2.1 x inside

private theorem afterCells_unique (model : Model context K) (lower : context.Value)
    (rest : List context.Value)
    (ordered : (lower :: rest).Pairwise (fun a b => model.value a < model.value b))
    (x : K) (above : model.value lower < x) :
    ∃! cell, cell ∈ afterCells context lower rest ∧ cell.Mem model x := by
  induction rest generalizing lower with
  | nil =>
    simp only [afterCells, between, List.map_nil, List.nil_append, List.map_cons,
      List.mem_singleton]
    refine ⟨(rightRay context lower).2, ⟨rfl, ?_⟩, fun _ h => h.1⟩
    simpa only [rightRay, Cell.Mem, and_true] using above
  | cons upper rest ih =>
    have tail := (List.pairwise_cons.mp ordered).2
    by_cases less : x < model.value upper
    · refine ⟨(bounded context lower upper).2,
        ⟨(afterCells_cons lower upper rest _).mpr (Or.inl rfl), ⟨above, less⟩⟩, ?_⟩
      rintro other ⟨member, inside⟩
      rcases (afterCells_cons lower upper rest other).mp member with same | same | later
      · exact same
      · subst other
        change model.value upper = x at inside
        exact False.elim ((lt_irrefl _) (inside ▸ less))
      · exact False.elim ((not_lt_of_ge less.le)
          (afterCells_above model upper rest tail other later x inside))
    · by_cases equal : x = model.value upper
      · refine ⟨.section upper,
          ⟨(afterCells_cons lower upper rest _).mpr (Or.inr (Or.inl rfl)), equal.symm⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (afterCells_cons lower upper rest other).mp member with same | same | later
        · subst other
          exact False.elim ((lt_irrefl _) (equal ▸ inside.2))
        · exact same
        · exact False.elim ((lt_irrefl _) (equal ▸
            afterCells_above model upper rest tail other later x inside))
      · have greater : model.value upper < x := by order
        obtain ⟨cell, member, unique⟩ := ih upper tail greater
        refine ⟨cell, ⟨(afterCells_cons lower upper rest _).mpr (Or.inr (Or.inr member.1)),
          member.2⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (afterCells_cons lower upper rest other).mp member with same | same | later
        · subst other
          exact False.elim ((not_lt_of_ge greater.le) inside.2)
        · subst other
          exact False.elim (equal inside.symm)
        · exact unique other ⟨later, inside⟩

omit [IsStrictOrderedRing K] in
private theorem sector_mem_eq (model : Model context K)
    (lower upper a b : Endpoint context.Value)
    (lowerSame : sameEndpoint context lower a = true)
    (upperSame : sameEndpoint context upper b = true) (x : K) :
    (Cell.sector lower upper).Mem model x ↔ (Cell.sector a b).Mem model x := by
  cases lower <;> cases a <;> cases upper <;> cases b <;>
    simp_all [sameEndpoint, Cell.Mem, model.equal_spec]

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

/-- The public section constructor carries exactly the descriptor's selected root. -/
theorem section_correct (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (original : Model parent K) :
    ∃ realization : Conversion.Model (Tower.Sample.section parent descriptor).input original,
      (Tower.Sample.section parent descriptor).cell.contains (Tower.Sample.section parent descriptor).value = true ∧
      (Tower.Sample.section parent descriptor).cell.Mem realization.target
        (realization.target.value (Tower.Sample.section parent descriptor).value) ∧
      realization.target.value (Tower.Sample.section parent descriptor).value =
        descriptor.root original.value original.zero_iff original.one original.add original.sub
          original.mul original.nat original.sign := by
  rw [Tower.Sample.section_eq]
  obtain ⟨realization, checked, inside, value⟩ :=
    ofRoot_correct (Root.ofSelection parent (.selected descriptor)) original
  refine ⟨realization, checked, inside, value.trans ?_⟩
  rw [Root.denote_selection, Root.selection_ofSelection]
  rfl

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

/-- The actual returned sections and sectors partition the common ambient field:
every point belongs to exactly one cell, including both exterior rays. -/
theorem Partition.cells_unique {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original) (x : K) :
    ∃! cell, cell ∈ family.cells ∧ cell.Mem model.input.target x := by
  let context := family.collection.input.context
  let target := model.input.target
  cases values : family.values with
  | nil =>
    simp only [Partition.cells, values, List.map_nil, List.nil_append, Sample.sectors,
      List.map_cons, List.mem_singleton]
    exact ⟨.sector .negInf .posInf, ⟨rfl, trivial, trivial⟩, fun _ h => h.1⟩
  | cons first rest =>
    have ordered : (first :: rest).Pairwise (fun a b => target.value a < target.value b) := by
      simpa only [values] using family.sorted original model
    have membership (cell : Cell context) : cell ∈ family.cells ↔
        cell = (leftRay context first).2 ∨ cell = .section first ∨
          cell ∈ afterCells context first rest := by
      simp only [Partition.cells, values, Sample.sectors, List.map_cons,
        List.mem_append, List.mem_cons, afterCells]
      tauto
    by_cases less : x < target.value first
    · refine ⟨(leftRay context first).2, ⟨(membership _).mpr (Or.inl rfl), trivial, less⟩, ?_⟩
      rintro other ⟨member, inside⟩
      rcases (membership other).mp member with same | same | later
      · exact same
      · subst other
        exact False.elim ((lt_irrefl _) (inside ▸ less))
      · exact False.elim ((not_lt_of_ge less.le)
          (afterCells_above target first rest ordered other later x inside))
    · by_cases equal : x = target.value first
      · refine ⟨.section first, ⟨(membership _).mpr (Or.inr (Or.inl rfl)), equal.symm⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (membership other).mp member with same | same | later
        · subst other
          exact False.elim ((lt_irrefl _) (equal ▸ inside.2))
        · exact same
        · exact False.elim ((lt_irrefl _) (equal ▸
            afterCells_above target first rest ordered other later x inside))
      · have greater : target.value first < x := by order
        obtain ⟨cell, member, unique⟩ := afterCells_unique target first rest ordered x greater
        refine ⟨cell, ⟨(membership _).mpr (Or.inr (Or.inr member.1)), member.2⟩, ?_⟩
        rintro other ⟨member, inside⟩
        rcases (membership other).mp member with same | same | later
        · subst other
          exact False.elim ((not_lt_of_ge greater.le) inside.2)
        · subst other
          exact False.elim (equal inside.symm)
        · exact unique other ⟨later, inside⟩

/-- Every returned sector has an actual compatible interpretation, passes native
strict membership, and contains no root of any nonzero input polynomial. -/
theorem Partition.sectors_correct {polynomials : List parent.Poly}
    (family : Partition parent polynomials) (original : Model parent K)
    (model : Collection.Model family.collection original) (sample : Tower.Sample parent)
    (present : sample ∈ family.sectors) :
    ∃ realization : Conversion.Model sample.input original,
      HEq realization model.input ∧
      sample.cell.contains sample.value = true ∧
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      ∀ x, sample.cell.Mem realization.target x → ∀ p ∈ polynomials,
        HexPolyMathlib.Interpret.interpret original.value original.zero_iff p ≠ 0 →
        ¬ (HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).IsRoot x := by
  obtain ⟨point, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨inside, excluded⟩ := sector_coordinates_correct model.input.target family.values
    (family.sorted original model) point member
  refine ⟨model.input, HEq.rfl, (Cell.contains_correct model.input.target _ _).mpr inside, inside, ?_⟩
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
      HEq realization model.input ∧
      sample.cell.contains sample.value = true ∧
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      ∃ p ∈ polynomials,
        HexPolyMathlib.Interpret.interpret original.value original.zero_iff p ≠ 0 ∧
        (HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).IsRoot
          (realization.target.value sample.value) := by
  obtain ⟨value, member, rfl⟩ := List.mem_map.mp present
  refine ⟨model.input, HEq.rfl, ?_, rfl, ?_⟩
  · exact (Cell.contains_correct model.input.target _ _).mpr rfl
  · exact (family.coverage original model _).mp (List.mem_map.mpr ⟨value, member, rfl⟩)

/-- Every adjacent sector in the complete cell partition is accepted by the
boundary request API, including both rays and the root-free whole line.
The requested endpoints may use different representatives of the same values. -/
theorem Partition.sectorBetween?_success {polynomials : List parent.Poly}
    (family : Partition parent polynomials) (original : Model parent K)
    (model : Collection.Model family.collection original)
    (lower upper a b : Endpoint family.collection.input.context.Value)
    (adjacent : Cell.sector a b ∈ family.cells)
    (lowerEqual : lower.map model.input.target.value = a.map model.input.target.value)
    (upperEqual : upper.map model.input.target.value = b.map model.input.target.value) :
    ∃ sample, family.sectorBetween? lower upper = some sample := by
  have present : ∃ point ∈ Sample.sectors family.collection.input.context family.values,
      point.2 = Cell.sector a b := by
    rcases List.mem_append.mp adjacent with atRoot | sector
    · obtain ⟨root, _, impossible⟩ := List.mem_map.mp atRoot
      cases impossible
    · exact List.mem_map.mp sector
  obtain ⟨point, member, cell⟩ := present
  have accepted : requested family.collection.input.context lower upper point = true := by
    simp only [requested, cell]
    have same : ∀ first second : Endpoint family.collection.input.context.Value,
        first.map model.input.target.value = second.map model.input.target.value →
        sameEndpoint family.collection.input.context first second = true := by
      intro first second equal
      cases first <;> cases second <;>
        simp_all [sameEndpoint, Endpoint.map, model.input.target.equal_spec]
    rw [same lower a lowerEqual, same upper b upperEqual]
    rfl
  cases found : (Sample.sectors family.collection.input.context family.values).find?
      (requested family.collection.input.context lower upper) with
  | none =>
    have rejected := List.find?_eq_none.mp found point member
    exact False.elim (rejected accepted)
  | some chosen =>
    exact ⟨Tower.Sample.mk family.collection.input chosen.1 chosen.2, by
      simp [Partition.sectorBetween?, found]⟩

/-- A checked boundary request denotes exactly the requested open sector,
under the same actual model as the complete family. -/
theorem Partition.sectorBetween?_correct {polynomials : List parent.Poly}
    (family : Partition parent polynomials) (original : Model parent K)
    (model : Collection.Model family.collection original)
    (lower upper : Endpoint family.collection.input.context.Value) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? lower upper = some sample) :
    ∃ realization : Conversion.Model sample.input original,
      HEq realization model.input ∧ sample.cell.contains sample.value = true ∧
      ∀ x, sample.cell.Mem realization.target x ↔
        (Cell.sector lower upper).Mem model.input.target x := by
  have member := family.sectorBetween?_mem lower upper sample returned
  cases found : (Sample.sectors family.collection.input.context family.values).find?
      (requested family.collection.input.context lower upper) with
  | none => simp [Partition.sectorBetween?, found] at returned
  | some point =>
    simp only [Partition.sectorBetween?, found, Option.map_some, Option.some.injEq] at returned
    subst sample
    have accepted := List.find?_some found
    cases cell : point.2 with
    | «section» root => simp [requested, cell] at accepted
    | sector a b =>
      have bounds : sameEndpoint family.collection.input.context lower a = true ∧
          sameEndpoint family.collection.input.context upper b = true := by
        simpa only [requested, cell, Bool.and_eq_true] using accepted
      obtain ⟨realization, aligned, checked, _, _⟩ := family.sectors_correct original model _ member
      have same : realization = model.input := eq_of_heq aligned
      subst realization
      refine ⟨model.input, HEq.rfl, ?_, ?_⟩
      · simpa only [cell] using checked
      · intro x
        exact (sector_mem_eq model.input.target lower upper a b bounds.1 bounds.2 x).symm

/-- The computed sign vector applies to every point of the returned sector,
including zero polynomials, in any real closed ordered field. -/
theorem Partition.sector_signs {polynomials : List parent.Poly}
    (family : Partition parent polynomials) (original : Model parent K)
    (model : Collection.Model family.collection original) (sample : Tower.Sample parent)
    (present : sample ∈ family.sectors) :
    ∃ realization : Conversion.Model sample.input original,
      HEq realization model.input ∧ ∀ x, sample.cell.Mem realization.target x →
        sample.signs polynomials = polynomials.map (fun p => (SignType.sign
          ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  obtain ⟨realization, aligned, _, inside, rootFree⟩ := family.sectors_correct original model sample present
  refine ⟨realization, aligned, ?_⟩
  intro x contained
  rw [signs_correct sample original realization polynomials]
  apply List.map_congr_left
  intro p member
  by_cases zero : HexPolyMathlib.Interpret.interpret original.value original.zero_iff p = 0
  · simp only [zero, Polynomial.eval_zero]
  · apply congrArg (fun s : SignType => (s : Int))
    exact sample.cell.sign_eq realization.target _ inside contained
      (fun y hy => rootFree y hy p member zero)


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

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.cells_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.cells_unique

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.sectors_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.sectors_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.sections_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.sections_correct

/-- info: 'Hex.RealClosure.Tower.Cell.interval_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Cell.interval_mem

/-- info: 'Hex.RealClosure.Tower.Cell.sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Cell.sign_eq

/-- info: 'Hex.RealClosure.Tower.Sample.section_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.section_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.sectorBetween?_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.sectorBetween?_correct

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.sector_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.sector_signs

/-- info: 'Hex.RealClosure.Tower.Sample.Partition.sectorBetween?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Sample.Partition.sectorBetween?_success
