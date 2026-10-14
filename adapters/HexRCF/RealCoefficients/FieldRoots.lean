/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldBuild
public import HexRCF.RealCoefficients.IsolationProgress
public import HexNumberFieldTheory.ComponentRoots

public section

/-! Complete real root proposals in the existing selected field presentation. -/
namespace Hex.RCF.RealCoefficients.FieldBuild

open HexPolyTheory.Interpret
variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- The complex owner polynomial is the map of the fixed real interpretation. -/
theorem polynomial_complex (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (head : DensePoly (PolyQuot p root)) :
    (interpret (Field.value rep) (Field.value_eq_zero rep hrep real) head).map
      Complex.ofRealHom = PolyQuot.toPolynomialAt head rep hrep := by
  ext i
  rw [Polynomial.coeff_map, coeff_interpret, PolyQuot.coeff_toPolynomialAt]
  exact Field.value_complex rep hrep real (head.coeff i)

/-- Real membership in the actual fixed-field output is source-polynomial vanishing. -/
theorem roots_meaning (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (head : DensePoly (PolyQuot p root)) (x : ℝ) :
    (RealAlgebraicPoly.realRoots (PolyQuot.roots head rep hrep)).Contains x ↔
      (interpret (Field.value rep) (Field.value_eq_zero rep hrep real) head).IsRoot x := by
  rw [RealAlgebraicPoly.contains_realRoots, PolyQuot.contains_roots_iff,
    ← polynomial_complex rep hrep real head, Polynomial.eval_map]
  change Polynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom x) _ = 0 ↔ _
  rw [Polynomial.eval₂_at_apply]
  exact Complex.ofReal_eq_zero

/-- The retained real roots are distinct and sorted by their exact real values. -/
theorem roots_sorted (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (head : DensePoly (PolyQuot p root)) :
    (RealAlgebraicPoly.realRoots (PolyQuot.roots head rep hrep)).toArray.toList.Pairwise
      (fun a b => a.root < b.root) := by
  exact ((RealAlgebraicPoly.realRoots_sorted (PolyQuot.roots head rep hrep)).and
    (RealAlgebraicPoly.realRoots_noDuplicates _
      (PolyQuot.roots_noDuplicates head rep hrep))).imp
        (fun h => lt_of_le_of_ne h.1 h.2)

/-- Every nonzero head produces a finite real list in its existing selected field. -/
theorem roots_finite (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0) :
    ∃ entries, roots? rep hrep head = some entries := by
  unfold roots?
  rw [PolyQuot.roots?_eq_roots]
  cases produced : PolyQuot.roots head rep hrep with
  | all =>
    have polynomial := (PolyQuot.roots_all_iff head rep hrep).mp produced
    have zero := (PolyQuot.poly_isZero_iff head rep hrep).mpr polynomial
    exact False.elim (nonzero ((DensePoly.size_eq_zero_iff head).mp
      ((DensePoly.isZero_eq_true_iff head).mp zero)))
  | finite entries => exact ⟨_, rfl⟩

/-- Successful finite extraction retains exactly the owner's real root set. -/
theorem roots_binding (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (head : DensePoly (PolyQuot p root)) (entries : Array RealRootCount)
    (produced : roots? rep hrep head = some entries) :
    RealAlgebraicPoly.realRoots (PolyQuot.roots head rep hrep) = .finite entries := by
  have finite : (RealAlgebraicPoly.realRoots (PolyQuot.roots head rep hrep)).finite? =
      some entries := by
    simpa only [roots?, PolyQuot.roots?_eq_roots, Option.bind_some] using produced
  cases actual : RealAlgebraicPoly.realRoots (PolyQuot.roots head rep hrep) with
  | all => simp [actual, RealRootSet.finite?] at finite
  | finite result =>
    have same : result = entries := by
      simpa only [actual, RealRootSet.finite?, Option.some.injEq] using finite
    subst entries
    rfl

/-- Cofinal precision schedules eventually separate the complete selected-field root list. -/
theorem proposeRoots_progress (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (schedule : Nat → Nat) (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ cert : IsolationCert,
      proposeRoots rep hrep head (schedule k) = some cert ∧ cert.checkGaps = true := by
  classical
  obtain ⟨entries, produced⟩ := roots_finite rep hrep head nonzero
  have pairwise : entries.toList.Pairwise (fun a b => a.root < b.root) := by
    simpa only [roots_binding rep hrep head entries produced,
      RealRootSet.toArray, RealRootSet.finite?, Option.getD_some] using
      roots_sorted rep hrep head
  let values := entries.map RealRootCount.root
  have ordered : StrictMono (fun i : Fin values.size => values[i.val].toReal) := by
    intro i j hij
    have hi : i.val < entries.size := by simpa [values] using i.isLt
    have hj : j.val < entries.size := by simpa [values] using j.isLt
    have hlt := pairwise.rel_get_of_lt
      (a := ⟨i.val, by simpa using hi⟩) (b := ⟨j.val, by simpa using hj⟩)
      (by change i.val < j.val; exact hij)
    have native : entries[i.val].root < entries[j.val].root := by
      simpa only [List.get_eq_getElem, Array.getElem_toList] using hlt
    simpa [values] using (RealAlgebraicNumber.lt_iff _ _).mp native
  obtain ⟨K, hK⟩ := rootArray_separated values ordered schedule progress
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨cert, generated, gaps⟩ := hK k hk
  have original : entries.mapM (fun r => rootInterval r.root (schedule k)) =
      some cert.intervals := by
    simpa only [values, Array.mapM_map, Function.comp_def] using generated
  refine ⟨cert, ?_, gaps⟩
  simp only [proposeRoots, produced, bind, Option.bind_some, original]
  rfl

/-- Every finite proposal strictly encloses the complete original real root set. -/
theorem proposeRoots_spec (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (head : DensePoly (PolyQuot p root))
    (precision : Nat) (isolations : IsolationCert)
    (produced : proposeRoots rep hrep head precision = some isolations) :
    ∃ root : Fin isolations.intervals.size → ℝ,
      (∀ i, HexRealRootsTheory.Dyadic.toReal isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsTheory.Dyadic.toReal isolations.intervals[i].upper) ∧
      (∀ x, (interpret (Field.value rep) (Field.value_eq_zero rep hrep real) head).IsRoot x ↔
        ∃ i, root i = x) := by
  classical
  cases finite : roots? rep hrep head with
  | none => simp [proposeRoots, finite] at produced
  | some entries =>
    let interval (r : RealRootCount) := (rootInterval_spec r.root precision).choose
    have intervalProduced : (fun r : RealRootCount => rootInterval r.root precision) =
        (fun r => (pure (interval r) : Option DyadicInterval)) := by
      funext r
      exact (rootInterval_spec r.root precision).choose_spec.1
    have mapped : entries.mapM (fun r => rootInterval r.root precision) =
        some (entries.map interval) := by
      rw [intervalProduced]
      exact Array.mapM_pure
    have certEq : IsolationCert.mk (entries.map interval) = isolations := by
      have output : some (IsolationCert.mk (entries.map interval)) = some isolations := by
        simpa only [proposeRoots, finite, bind, Option.bind_some, mapped, Option.pure_def] using produced
      exact Option.some.inj output
    subst isolations
    let selected (i : Fin (entries.map interval).size) := entries[i.val].root.toReal
    refine ⟨selected, ?_, ?_⟩
    · intro i
      have enclosed := (rootInterval_spec entries[i.val].root precision).choose_spec
      change HexRealRootsTheory.Dyadic.toReal (entries.map interval)[i.val].lower <
        entries[i.val].root.toReal ∧ entries[i.val].root.toReal <
          HexRealRootsTheory.Dyadic.toReal (entries.map interval)[i.val].upper
      simpa only [Array.getElem_map, interval] using And.intro enclosed.2.1 enclosed.2.2.1
    · intro x
      rw [← roots_meaning rep hrep real head x, roots_binding rep hrep head entries finite]
      simp only [RealRootSet.Contains, Array.mem_toList_iff]
      constructor
      · rintro ⟨r, membership, value⟩
        obtain ⟨i, hi, entry⟩ := Array.mem_iff_getElem.mp membership
        exact ⟨⟨i, by simpa using hi⟩, by simpa only [selected, entry] using value⟩
      · rintro ⟨i, value⟩
        exact ⟨entries[i.val], Array.getElem_mem _, value⟩

/-- Separated proposals pass the actual replay builder over the original field.
All domain, endpoint and count conclusions are derived from complete roots. -/
theorem proposeRoots_accepted {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (sign : PolyQuot p root → Int)
    (meaning : ∀ a, sign a = (SignType.sign (Field.value rep a) : Int))
    (context : Ctx) (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (squarefree : Squarefree (interpret (Field.value rep) (Field.value_eq_zero rep hrep real) head))
    (precision : Nat) (isolations : IsolationCert)
    (produced : proposeRoots rep hrep head precision = some isolations)
    (gaps : isolations.checkGaps = true) :
    ∃ cert, IsolationReplay.build sign FieldDecision.point context head isolations = some cert := by
  obtain ⟨values, bounds, complete⟩ := proposeRoots_spec rep hrep real head precision isolations produced
  have polynomialNe : interpret (Field.value rep) (Field.value_eq_zero rep hrep real) head ≠ 0 :=
    fun zero => nonzero ((interpret_eq_zero (Field.value rep)
      (Field.value_eq_zero rep hrep real) head).mp zero)
  apply IsolationReplay.build_fromRoots (Field.value rep) (Field.value_eq_zero rep hrep real)
    (Field.value_one rep hrep real) (Field.value_add rep hrep real)
    (Field.value_sub rep hrep real) (Field.value_mul rep hrep real)
    (Field.value_neg rep hrep real) (Field.value_inv rep hrep real)
    (Field.value_natCast rep hrep real) sign meaning
    FieldDecision.point ?_ context head polynomialNe squarefree isolations gaps values bounds complete
  intro d
  simpa only [FieldDecision.point, HexRealRootsTheory.toReal_eq_cast_toRat] using
    FieldSpecialize.value_ofRat rep hrep real d.toRat

end Hex.RCF.RealCoefficients.FieldBuild
