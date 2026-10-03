/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TrivialTower
public import HexRealClosureMathlib.TowerTransport
public import HexRealClosureMathlib.TowerRoots
public import HexRealClosureMathlib.Trivial
public import HexRealClosureMathlib.SelectedRoot
public import HexRealAlgebraicMathlib.Field
public import HexRealAlgebraicMathlib.Roots

public section

namespace Hex.RealClosure.Trivial
open HexPolyMathlib.Interpret

variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- The cached native conversion retains the exact selected real embedding
of its original context. The rational and suffix factories discharge this
relation; it is not an executable constructor argument. -/
@[expose] def Map.Model (source : Map parent) (original : Tower.Model parent ℝ) : Prop :=
  ∀ a, (source.value a).toReal = original.value a

variable {source : Map parent} {original : Tower.Model parent ℝ}

/-- Canonical conversion reflects the native canonical zero. -/
theorem Map.Model.zero (model : source.Model original) (a : parent.Value) :
    source.value a = 0 ↔ a = 0 := by
  constructor
  · intro zero
    apply (original.zero_iff a).mp
    rw [← model a, zero, RealAlgebraicNumber.zero_toReal]
  · intro zero
    apply RealAlgebraicNumber.toReal_injective
    rw [model a, (original.zero_iff a).mpr zero, RealAlgebraicNumber.zero_toReal]

/-- The independent backend sees exactly the original interpreted polynomial. -/
theorem Map.Model.polynomial (model : source.Model original) (p : DensePoly parent.Value) :
    (source.polynomial p).toPolynomial = interpret original.value original.zero_iff p := by
  ext i
  rw [Map.polynomial, RealAlgebraicPoly.coeff_ofArray, coeff_interpret]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, DensePoly.coeff, DensePoly.toArray]
  cases h : p.coeffs[i]? with
  | some a => simpa only [h, Option.map_some, Option.getD_some] using model a
  | none =>
    simp only [h, Option.map_none, Option.getD_none, RealAlgebraicNumber.zero_toReal]
    exact ((original.zero_iff 0).mpr rfl).symm

/-- Actual canonical Horner arithmetic preserves the selected real value. -/
theorem Map.Model.eval (model : source.Model original) (p : DensePoly parent.Value)
    (x : RealAlgebraicNumber) :
    (source.eval p x).toReal = (interpret original.value original.zero_iff p).eval x.toReal := by
  classical
  let mapped := DensePoly.Interpret.map source.value model.zero p
  have heval : source.eval p x = mapped.eval x := by
    simp [Map.eval, DensePoly.eval, mapped, DensePoly.toList]
  have hpoly : (HexPolyMathlib.toPolynomial mapped).map RealAlgebraicNumber.toRealHom =
      interpret original.value original.zero_iff p := by
    ext i
    dsimp only [mapped]
    simp only [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
      DensePoly.Interpret.map_coeff, coeff_interpret]
    exact model (p.coeff i)
  rw [heval, ← HexPolyMathlib.eval_toPolynomial, ← hpoly]
  exact (Polynomial.eval_map_apply RealAlgebraicNumber.toRealHom x).symm

/-- Canonical signs agree with evaluation in the original selected embedding. -/
theorem Map.Model.eval_sign (model : source.Model original) (p : DensePoly parent.Value)
    (x : RealAlgebraicNumber) :
    (source.eval p x).sign =
      (SignType.sign ((interpret original.value original.zero_iff p).eval x.toReal) : Int) := by
  rw [RealAlgebraicNumber.sign_eq, model.eval]
  by_cases hn : (interpret original.value original.zero_iff p).eval x.toReal < 0
  · simp [hn, sign_eq_neg_one_iff.mpr hn]
  · by_cases hz : (interpret original.value original.zero_iff p).eval x.toReal = 0
    · simp [hz]
    · have hp : 0 < (interpret original.value original.zero_iff p).eval x.toReal :=
        lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hn, hz, sign_eq_one_iff.mpr hp]

/-- The executable filter checks the original descriptor's interval and signs. -/
theorem Map.Model.matches_iff (model : source.Model original)
    (d : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (x : RealAlgebraicNumber) :
    source.matches d x = true ↔
      HexRealRootsMathlib.Tarski.InInterval
        (d.raw.lower.map original.value) (d.raw.upper.map original.value) x.toReal ∧
      SignDet.signsAt original.value original.zero_iff d.raw.queries x.toReal = d.raw.signs := by
  have hsign : d.raw.queries.map (fun q => (source.eval q x).sign) =
      SignDet.signsAt original.value original.zero_iff d.raw.queries x.toReal := by
    simp [SignDet.signsAt, model.eval_sign]
  rw [HexRealRootsMathlib.Tarski.inInterval_iff]
  simp only [Map.matches, Bool.and_eq_true, decide_eq_true_eq, hsign]
  have hvalue (a : parent.Value) : (source.value a).toReal = original.value a := model a
  cases d.raw.lower <;> cases d.raw.upper <;>
    simp [Endpoint.map, RealAlgebraicNumber.lt_iff, hvalue]

/-- Finite independent backend entries are exactly the real roots of the
original head; a validated descriptor rules out the universal case. -/
theorem Map.Model.mem_roots_iff (model : source.Model original)
    (d : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (x : ℝ) :
    (∃ e ∈ (source.polynomial d.raw.head).roots.toArray.toList, e.root.toReal = x) ↔
      (interpret original.value original.zero_iff d.raw.head).eval x = 0 := by
  have hne := d.head_ne_zero original.value original.zero_iff
  have hnot : (source.polynomial d.raw.head).roots ≠ .all := by
    intro h
    exact hne ((model.polynomial d.raw.head).symm.trans
      ((RealAlgebraicPoly.roots_all_iff _).mp h))
  have hc := RealAlgebraicPoly.contains_roots_iff (source.polynomial d.raw.head) x
  rw [model.polynomial] at hc
  cases hroots : (source.polynomial d.raw.head).roots with
  | all => exact False.elim (hnot hroots)
  | finite entries =>
    simpa [hroots, RealRootSet.Contains, RealRootSet.toArray, RealRootSet.finite?] using hc

/-- A returned canonical root retains the actual validated selected embedding. -/
theorem Map.Model.canonical?_sound (model : source.Model original)
    (d : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature)
    (x : RealAlgebraicNumber) (h : source.canonical? d = some x) :
    x.toReal = d.root original.value original.zero_iff original.one original.add
      original.sub original.mul original.nat original.sign := by
  rw [Map.canonical?_eq] at h
  obtain ⟨e, he, hx⟩ := Option.map_eq_some_iff.mp h
  have hfind : ((source.polynomial d.raw.head).roots.toArray.toList).find?
      (fun e => source.matches d e.root) = some e := he
  have hmem := List.mem_of_find?_eq_some hfind
  have hmatch := List.find?_some hfind
  obtain ⟨hint, hs⟩ := (model.matches_iff d e.root).mp hmatch
  have hroot := (model.mem_roots_iff d e.root.toReal).mp ⟨e, hmem, rfl⟩
  have hne := d.head_ne_zero original.value original.zero_iff
  have hrootIn := (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ hne _ _ _).mpr
    ⟨hroot, hint⟩
  subst x
  exact d.root_unique original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign e.root.toReal hrootIn hs

/-- Independent root enumeration always contains a match for the actual
validated descriptor, including reducible algebraic-coefficient heads. -/
theorem Map.Model.canonical?_isSome (model : source.Model original)
    (d : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    (source.canonical? d).isSome := by
  let x := d.root original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign
  have hs := d.root_spec original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign
  have hne := d.head_ne_zero original.value original.zero_iff
  have hroot := (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ hne _ _ _).mp hs.1
  obtain ⟨e, he, hx⟩ := (model.mem_roots_iff d x).mpr hroot.1
  have hfind : (((source.polynomial d.raw.head).roots.toArray.toList).find?
      (fun e => source.matches d e.root)).isSome := by
    apply List.find?_isSome.mpr
    refine ⟨e, he, (model.matches_iff d e.root).mpr ?_⟩
    rw [hx]
    exact ⟨hroot.2, hs.2⟩
  simpa only [Map.canonical?_eq, Option.isSome_map] using hfind

/-- The total cached converter never uses its diagnostic fallback. -/
theorem Map.Model.canonical_real (model : source.Model original)
    (d : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    (source.canonical d).toReal =
      d.root original.value original.zero_iff original.one original.add
        original.sub original.mul original.nat original.sign := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (model.canonical?_isSome d)
  simpa [Map.canonical, hx] using model.canonical?_sound d x hx

/-- The rational factory has the canonical rational embedding, with no
coefficient-agreement premise. -/
theorem Map.rational_model (registry : BaseContext.Registry) :
    (Map.rational registry).Model
      (Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign) := by
  intro a
  calc
    ((Map.rational registry).value a).toReal =
        (RealAlgebraicNumber.ofRat a.stored).toReal :=
      congrArg RealAlgebraicNumber.toReal (Map.rational_value registry a)
    _ = (a.stored : ℝ) := RealAlgebraicNumber.ofRat_toReal a.stored
    _ = _ := (Tower.Model.base_value (BaseContext.rational registry)
      (Rat.castHom ℝ) ratSign a).symm

/-- Caching the independently selected canonical generator preserves the
actual native child model. -/
theorem Map.Model.adjoin (model : source.Model original)
    (d : SignDet.Descriptor parent.Value Tower.Signature parent.sign parent.signature) :
    (source.adjoin d).Model (original.adjoin d) := by
  intro a
  rw [Map.adjoin_value, model.eval, model.canonical_real,
    original.adjoin_value d a, original.adjoin_generator]

/-- Every actual validated root in the suffix discharges its conversion
relation in predecessor order. -/
theorem Map.Model.extend {context : Tower.Context registry} {source : Map context}
    {original : Tower.Model context ℝ} (model : source.Model original)
    (suffix : Tower.Suffix context) :
    (source.extend suffix).Model (original.extend suffix) := by
  induction suffix with
  | nil => exact model
  | root d rest ih => exact ih (model.adjoin d)

/-- The full rational-tower factory derives agreement from its actual
validated contexts, without caller-supplied semantic maps or alignments. -/
theorem Map.ofSuffix_model
    (suffix : Tower.Suffix (Tower.Context.base (BaseContext.rational registry))) :
    (Map.ofSuffix suffix).Model
      ((Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign).extend suffix) :=
  (Map.rational_model registry).extend suffix

/-- Actual native root handles convert to their selected real values. -/
theorem Map.Model.root (model : source.Model original) (root : Tower.Root parent) :
    (source.root root).toReal = root.denote original := by
  cases root with
  | point a => exact model a
  | selected d extension built =>
    cases built
    exact (model.canonical_real d).trans (original.adjoin_generator d).symm

/-- Actual canonical comparison agrees with native comparison. -/
theorem Map.Model.compare (model : source.Model original) (a b : parent.Value) :
    source.compare a b = parent.compare a b := by
  rw [Map.compare, RealAlgebraicNumber.compare_eq, model a, model b, original.compare_spec]
  simp only [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]

/-- Equality of converted canonical values is native semantic equality. -/
theorem Map.Model.equal (model : source.Model original) (a b : parent.Value) :
    parent.equal a b = true ↔ source.value a = source.value b := by
  rw [original.equal_spec, ← RealAlgebraicNumber.toReal_injective.eq_iff, model a, model b]
  simp only [decide_eq_true_eq]

/-- Conversion preserves canonical zero and every executable field operation. -/
theorem Map.Model.value_zero (model : source.Model original) : source.value 0 = 0 :=
  (model.zero 0).mpr rfl

theorem Map.Model.value_one (model : source.Model original) : source.value 1 = 1 := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model 1, original.one, RealAlgebraicNumber.one_toReal]

theorem Map.Model.value_add (model : source.Model original) (a b : parent.Value) :
    source.value (a + b) = source.value a + source.value b := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model (a + b), RealAlgebraicNumber.add_toReal, model a, model b, original.add]

theorem Map.Model.value_sub (model : source.Model original) (a b : parent.Value) :
    source.value (a - b) = source.value a - source.value b := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model (a - b), RealAlgebraicNumber.sub_toReal, model a, model b, original.sub]

theorem Map.Model.value_mul (model : source.Model original) (a b : parent.Value) :
    source.value (a * b) = source.value a * source.value b := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model (a * b), RealAlgebraicNumber.mul_toReal, model a, model b, original.mul]

theorem Map.Model.value_neg (model : source.Model original) (a : parent.Value) :
    source.value (-a) = -source.value a := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model (-a), RealAlgebraicNumber.neg_toReal, model a, original.neg]

theorem Map.Model.value_inv (model : source.Model original) (a : parent.Value) :
    source.value a⁻¹ = (source.value a)⁻¹ := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model a⁻¹, RealAlgebraicNumber.inv_toReal, model a, original.inv]

theorem Map.Model.value_div (model : source.Model original) (a b : parent.Value) :
    source.value (a / b) = source.value a / source.value b := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model (a / b), RealAlgebraicNumber.div_toReal, model a, model b, original.div]

theorem Map.Model.value_nat (model : source.Model original) (n : Nat) :
    source.value (n : parent.Value) = (n : RealAlgebraicNumber) := by
  apply RealAlgebraicNumber.toReal_injective
  rw [model (n : parent.Value), original.nat]
  exact (map_natCast RealAlgebraicNumber.toRealHom n).symm

/-- Every actual stored coefficient has the same sign in both backends. -/
theorem Map.Model.sign (model : source.Model original) (a : parent.Value) :
    (source.value a).sign = parent.sign a := by
  rw [RealAlgebraicNumber.sign_eq, model a, original.sign]
  by_cases hn : original.value a < 0
  · simp [hn, sign_eq_neg_one_iff.mpr hn]
  · by_cases hz : original.value a = 0
    · simp [hz]
    · have hp : 0 < original.value a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hn, hz, sign_eq_one_iff.mpr hp]

private theorem count_ext (a b : RealRootCount) (root : a.root = b.root)
    (multiplicity : a.multiplicity = b.multiplicity) : a = b := by
  cases a
  cases b
  cases root
  cases multiplicity
  rfl

/-- Converted native entries retain their actual selected value. -/
theorem Map.Model.entry (model : source.Model original) (e : Tower.RootEntry parent) :
    (source.entry e).root.toReal = e.denote original := model.root e.root

private theorem entries_spec (model : source.Model original) (p : DensePoly parent.Value)
    {out : List (Tower.RootEntry parent)} (returned : parent.roots p = .finite out)
    (s : RealRootCount) :
    s ∈ out.map source.entry ↔
      (interpret original.value original.zero_iff p).IsRoot s.root.toReal ∧
      s.multiplicity = (interpret original.value original.zero_iff p).rootMultiplicity s.root.toReal := by
  have spec := Tower.Context.roots_spec original p returned s.root.toReal s.multiplicity
  rw [← spec]
  constructor
  · intro member
    obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
    exact ⟨e, present, (model.entry e).symm, rfl⟩
  · rintro ⟨e, present, value, multiplicity⟩
    apply List.mem_map.mpr
    exact ⟨e, present, count_ext _ _
      (RealAlgebraicNumber.toReal_injective ((model.entry e).trans value)) multiplicity⟩

private theorem entries_sorted (model : source.Model original) (p : DensePoly parent.Value)
    {out : List (Tower.RootEntry parent)} (returned : parent.roots p = .finite out) :
    (out.map source.entry).Pairwise (fun a b => a.root.toReal < b.root.toReal) := by
  have ordered := Tower.Context.roots_sorted original p returned
  rw [List.pairwise_map] at ordered ⊢
  apply ordered.imp
  intro a b less
  simpa only [model.entry] using less

private theorem backend_spec (model : source.Model original) (p : DensePoly parent.Value)
    {out : Array RealRootCount} (returned : (source.polynomial p).roots = .finite out)
    (s : RealRootCount) :
    s ∈ out.toList ↔ (interpret original.value original.zero_iff p).IsRoot s.root.toReal ∧
      s.multiplicity = (interpret original.value original.zero_iff p).rootMultiplicity s.root.toReal := by
  have member (e : RealRootCount) (present : e ∈ out.toList) :
      e ∈ (source.polynomial p).roots.toArray := by
    simpa [returned, RealRootSet.toArray, RealRootSet.finite?] using present
  constructor
  · intro present
    have root := (RealAlgebraicPoly.contains_roots_iff (source.polynomial p) s.root.toReal).mp
      (by rw [returned]; exact ⟨s, present, rfl⟩)
    rw [model.polynomial] at root
    have multiplicity := RealAlgebraicPoly.roots_multiplicity (source.polynomial p) s (member s present)
    rw [model.polynomial] at multiplicity
    exact ⟨root, multiplicity⟩
  · rintro ⟨root, multiplicity⟩
    have contains := (RealAlgebraicPoly.contains_roots_iff (source.polynomial p) s.root.toReal).mpr
      (by rw [model.polynomial]; exact root)
    rw [returned, RealRootSet.Contains] at contains
    obtain ⟨e, present, value⟩ := contains
    have actual := RealAlgebraicPoly.roots_multiplicity (source.polynomial p) e (member e present)
    rw [model.polynomial, value] at actual
    have same := count_ext e s (RealAlgebraicNumber.toReal_injective value)
      (actual.trans multiplicity.symm)
    exact same ▸ present

/-- Exact agreement with the independent canonical real-algebraic root API
for arbitrary native algebraic coefficients: universal zero, sorted selected
roots and every positive multiplicity. -/
theorem Map.Model.roots_eq (model : source.Model original) (p : DensePoly parent.Value) :
    source.roots p = (source.polynomial p).roots := by
  have all := Tower.Context.roots_all original p
  cases generic : parent.roots p with
  | all =>
    have zero := all.mp generic
    have backend := (RealAlgebraicPoly.roots_all_iff (source.polynomial p)).mpr
      ((model.polynomial p).trans zero)
    simp only [Map.roots, generic, Map.output, backend]
  | finite entries =>
    cases backend : (source.polynomial p).roots with
    | all =>
      have zero := (model.polynomial p).symm.trans
        ((RealAlgebraicPoly.roots_all_iff (source.polynomial p)).mp backend)
      have impossible := all.mpr zero
      rw [generic] at impossible
      cases impossible
    | finite existing =>
      have backend_order := RealAlgebraicPoly.roots_sorted (source.polynomial p)
      simp only [backend, RealRootSet.toArray, RealRootSet.finite?, Option.getD_some] at backend_order
      have ordered := backend_order.imp (fun h => (RealAlgebraicNumber.lt_iff _ _).mp h)
      let relation := fun a b : RealRootCount => a.root.toReal < b.root.toReal
      let : Std.Antisymm relation := ⟨fun _ _ less greater => False.elim ((lt_asymm less) greater)⟩
      let : Std.Irrefl relation := ⟨fun _ => lt_irrefl _⟩
      have same : entries.map source.entry = existing.toList :=
        List.Pairwise.eq_of_mem_iff (r := relation) (entries_sorted model p generic) ordered
          (fun s => (entries_spec model p generic s).trans (backend_spec model p backend s).symm)
      simp only [Map.roots, generic, Map.output]
      rw [same, Array.toArray_toList]

/-- Full rational-tower agreement uses the actual cached factory, requiring
no coefficient interpretation or selected-root alignment from its caller. -/
theorem Map.ofSuffix_roots
    (suffix : Tower.Suffix (Tower.Context.base (BaseContext.rational registry)))
    (p : DensePoly suffix.context.Value) :
    (Map.ofSuffix suffix).roots p = ((Map.ofSuffix suffix).polynomial p).roots :=
  (Map.ofSuffix_model suffix).roots_eq p

/-- Independent comparison agrees for root handles with different child
contexts as well as for stored values in one context. -/
theorem Map.Model.compareRoots (model : source.Model original) (a b : Tower.Root parent) :
    source.compareRoots a b = a.compare b := by
  rw [Map.compareRoots, RealAlgebraicNumber.compare_eq, model.root a, model.root b,
    a.compare_correct b original]

/-- Actual rational-tower comparison needs no external coefficient agreement. -/
theorem compare_eq
    (suffix : Tower.Suffix (Tower.Context.base (BaseContext.rational registry)))
    (a b : suffix.context.Value) :
    (Map.ofSuffix suffix).compare a b = suffix.context.compare a b :=
  (Map.ofSuffix_model suffix).compare a b

/-- The full algebraic-coefficient trivial-fragment root contract. -/
theorem roots_eq
    (suffix : Tower.Suffix (Tower.Context.base (BaseContext.rational registry)))
    (p : DensePoly suffix.context.Value) :
    (Map.ofSuffix suffix).roots p = ((Map.ofSuffix suffix).polynomial p).roots :=
  Map.ofSuffix_roots suffix p

end Hex.RealClosure.Trivial
