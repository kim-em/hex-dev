/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.IsolationSemantics
public import HexRCF.RealCoefficients.IsolationAssembly

public section

namespace Hex.RCF.RealCoefficients

open HexPolyMathlib.Interpret

/-- Strict ordinary enclosures of two distinct roots eventually separate
along every precision schedule tending to infinity. -/
theorem rootInterval_separated (left right : RealAlgebraicNumber)
    (ordered : left.toReal < right.toReal) (schedule : Nat → Nat)
    (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ lower upper,
      rootInterval left (schedule k) = some lower ∧
      rootInterval right (schedule k) = some upper ∧ lower.upper < upper.lower := by
  let epsilon := (right.toReal - left.toReal) / 3
  have positive : 0 < epsilon := by dsimp [epsilon]; linarith
  obtain ⟨L, hL⟩ := rootInterval_progress left schedule progress epsilon positive
  obtain ⟨R, hR⟩ := rootInterval_progress right schedule progress epsilon positive
  refine ⟨max L R, fun k hk => ?_⟩
  obtain ⟨lower, hlo, hll, hlu, hlw⟩ := hL k (le_trans (le_max_left L R) hk)
  obtain ⟨upper, hhi, hul, huu, huw⟩ := hR k (le_trans (le_max_right L R) hk)
  refine ⟨lower, upper, hlo, hhi, ?_⟩
  have gap : HexRealRootsMathlib.Dyadic.toReal lower.upper <
      HexRealRootsMathlib.Dyadic.toReal upper.lower := by
    dsimp [epsilon] at hlw huw
    linarith
  apply HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mp
  simpa only [HexRealRootsMathlib.toReal_eq_cast_toRat,
    HexRootsMathlib.Dyadic.toReal] using gap

/-- A finite strictly ordered root array eventually has disjoint strict
enclosures; no minimum separation or precision bound is assumed. -/
theorem rootArray_separated (roots : Array RealAlgebraicNumber)
    (ordered : StrictMono (fun i : Fin roots.size => roots[i.val].toReal))
    (schedule : Nat → Nat)
    (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ cert : IsolationCert,
      roots.mapM (fun root => rootInterval root (schedule k)) = some cert.intervals ∧
      cert.checkGaps = true := by
  classical
  let interval (root : RealAlgebraicNumber) (k : Nat) :=
    (rootInterval_spec root (schedule k)).choose
  have produced (root : RealAlgebraicNumber) (k : Nat) :
      rootInterval root (schedule k) = some (interval root k) :=
    (rootInterval_spec root (schedule k)).choose_spec.1
  have pair (i j : Fin roots.size) : ∀ᶠ k in Filter.atTop,
      i < j → (interval roots[i.val] k).upper < (interval roots[j.val] k).lower := by
    by_cases h : i < j
    · obtain ⟨K, hK⟩ := rootInterval_separated roots[i.val] roots[j.val]
        (ordered h) schedule progress
      apply Filter.eventually_atTop.mpr
      refine ⟨K, fun k hk _ => ?_⟩
      obtain ⟨lower, upper, hlo, hhi, gap⟩ := hK k hk
      have heqlo := Option.some.inj (hlo.symm.trans (produced roots[i.val] k))
      have heqhi := Option.some.inj (hhi.symm.trans (produced roots[j.val] k))
      simpa only [heqlo, heqhi] using gap
    · exact Filter.Eventually.of_forall (fun _ hk => False.elim (h hk))
  have all : ∀ᶠ k in Filter.atTop, ∀ i j : Fin roots.size,
      i < j → (interval roots[i.val] k).upper < (interval roots[j.val] k).lower :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (pair i))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp all
  refine ⟨K, fun k hk => ?_⟩
  let cert : IsolationCert := ⟨roots.map (fun root => interval root k)⟩
  refine ⟨cert, ?_, ?_⟩
  · have functions : (fun root => rootInterval root (schedule k)) =
        (fun root => (pure (interval root k) : Option DyadicInterval)) := by
      funext root
      exact produced root k
    rw [functions]
    exact Array.mapM_pure
  · apply List.all_eq_true.mpr
    intro i hi
    have hi' : i < roots.size - 1 := by simpa [IsolationCert.checkGaps, cert] using hi
    have hi1 : i + 1 < roots.size := by omega
    have gap := hK k hk ⟨i, by omega⟩ ⟨i + 1, hi1⟩ (by change i < i + 1; omega)
    simpa [IsolationCert.checkGaps, cert, hi1] using gap

/-- The owner's complete sorted root producer and strict enclosure laws
make nonzero canonical polynomial proposals eventually pass the gap checker. -/
theorem solverIntervals_progress (solver : RealAlgebraicPoly) (nonzero : solver.toPolynomial ≠ 0)
    (schedule : Nat → Nat)
    (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ cert : IsolationCert,
      solverIntervals solver (schedule k) = some cert ∧ cert.checkGaps = true := by
  classical
  cases produced : solver.roots with
  | all => exact False.elim (nonzero ((RealAlgebraicPoly.roots_all_iff solver).mp produced))
  | finite roots =>
    have pairwise : roots.toList.Pairwise (fun a b => a.root < b.root) := by
      simpa [produced, RealRootSet.toArray, RealRootSet.finite?] using solver.roots_sorted
    let values := roots.map RealRootCount.root
    have ordered : StrictMono (fun i : Fin values.size => values[i.val].toReal) := by
      intro i j hij
      have hi : i.val < roots.size := by simpa [values] using i.isLt
      have hj : j.val < roots.size := by simpa [values] using j.isLt
      have hlt := pairwise.rel_get_of_lt
        (a := ⟨i.val, by simpa using hi⟩) (b := ⟨j.val, by simpa using hj⟩)
        (by change i.val < j.val; exact hij)
      have hnative : roots[i.val].root < roots[j.val].root := by
        simpa only [List.get_eq_getElem, Array.getElem_toList] using hlt
      simpa [values] using (RealAlgebraicNumber.lt_iff _ _).mp hnative
    obtain ⟨K, hK⟩ := rootArray_separated values ordered schedule progress
    refine ⟨K, fun k hk => ?_⟩
    obtain ⟨cert, generated, gaps⟩ := hK k hk
    refine ⟨cert, ?_, gaps⟩
    have original : roots.mapM (fun r => rootInterval r.root (schedule k)) =
        some cert.intervals := by simpa only [values, Array.mapM_map, Function.comp_def] using generated
    change ((solver.roots.finite?).bind fun roots =>
      (roots.mapM fun r => rootInterval r.root (schedule k)).bind fun intervals =>
        some (IsolationCert.mk intervals)) = some cert
    simp only [produced, RealRootSet.finite?, Option.bind_some, original]

/-- Every nonzero canonical head eventually proposes strictly separated
isolations under an explicitly cofinal precision schedule. -/
theorem proposeIsolations_separated [RealAlgebraicNumber.Laws]
    (head : DensePoly RealAlgebraicNumber) (nonzero : head ≠ 0)
    (schedule : Nat → Nat) (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ cert : IsolationCert,
      proposeIsolations head (schedule k) = some cert ∧ cert.checkGaps = true := by
  have polynomialNe : (RealAlgebraicPoly.ofArray head.toArray).toPolynomial ≠ 0 := by
    rw [solver_polynomial]
    exact fun h => nonzero ((HexPolyMathlib.Interpret.interpret_eq_zero
      RealAlgebraicNumber.toReal algebraic_zero head).mp h)
  exact solverIntervals_progress (RealAlgebraicPoly.ofArray head.toArray) polynomialNe schedule progress

/-- The actual canonical proposal carries all real roots and strictly
encloses each root at its matching index, using the owner's root correspondence. -/
theorem solverIntervals_spec (solver : RealAlgebraicPoly) (precision : Nat) (isolations : IsolationCert)
    (produced : solverIntervals solver precision = some isolations) :
    ∃ root : Fin isolations.intervals.size → ℝ,
      (∀ i, HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper) ∧
      (∀ x, solver.toPolynomial.IsRoot x ↔ ∃ i, root i = x) := by
  classical
  cases rootsEq : solver.roots with
  | all => simp [solverIntervals, rootsEq, RealRootSet.finite?] at produced
  | finite roots =>
    let interval (r : RealRootCount) := (rootInterval_spec r.root precision).choose
    have intervalProduced : (fun r : RealRootCount => rootInterval r.root precision) =
        (fun r => (pure (interval r) : Option DyadicInterval)) := by
      funext r
      exact (rootInterval_spec r.root precision).choose_spec.1
    have mapped : roots.mapM (fun r => rootInterval r.root precision) = some (roots.map interval) := by
      rw [intervalProduced]; exact Array.mapM_pure
    have certEq : IsolationCert.mk (roots.map interval) = isolations := by
      change ((solver.roots.finite?).bind fun entries =>
        (entries.mapM fun r => rootInterval r.root precision).bind fun intervals =>
          some (IsolationCert.mk intervals)) = some isolations at produced
      have output : some (IsolationCert.mk (roots.map interval)) = some isolations := by
        simpa only [rootsEq, RealRootSet.finite?, Option.bind_some, mapped] using produced
      exact Option.some.inj output
    subst isolations
    let root (i : Fin (roots.map interval).size) := roots[i.val].root.toReal
    refine ⟨root, ?_, ?_⟩
    · intro i
      have enclosed := (rootInterval_spec roots[i.val].root precision).choose_spec
      change HexRealRootsMathlib.Dyadic.toReal (roots.map interval)[i.val].lower < roots[i.val].root.toReal ∧
        roots[i.val].root.toReal < HexRealRootsMathlib.Dyadic.toReal (roots.map interval)[i.val].upper
      simpa only [Array.getElem_map, interval] using And.intro enclosed.2.1 enclosed.2.2.1
    · intro x
      change solver.toPolynomial.eval x = 0 ↔ _
      rw [← RealAlgebraicPoly.contains_roots_iff solver x, rootsEq]
      simp only [RealRootSet.Contains, Array.mem_toList_iff]
      constructor
      · rintro ⟨r, membership, value⟩
        obtain ⟨i, hi, entry⟩ := Array.mem_iff_getElem.mp membership
        exact ⟨⟨i, by simpa using hi⟩, by simpa only [root, entry] using value⟩
      · rintro ⟨i, value⟩
        exact ⟨roots[i.val], Array.getElem_mem _, value⟩

/-- Canonical proposals enclose a complete root list for the original
interpreted coefficient polynomial. -/
theorem proposeIsolations_spec [RealAlgebraicNumber.Laws]
    (head : DensePoly RealAlgebraicNumber) (precision : Nat) (isolations : IsolationCert)
    (produced : proposeIsolations head precision = some isolations) :
    ∃ root : Fin isolations.intervals.size → ℝ,
      (∀ i, HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsMathlib.Dyadic.toReal isolations.intervals[i].upper) ∧
      (∀ x, (interpret RealAlgebraicNumber.toReal algebraic_zero head).IsRoot x ↔ ∃ i, root i = x) := by
  simpa only [solver_polynomial] using
    solverIntervals_spec (RealAlgebraicPoly.ofArray head.toArray) precision isolations produced

/-- Separated proposals for a genuinely squarefree head are accepted
by the actual isolation builder, with domain and root counts derived. -/
theorem proposeIsolations_accepted [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber)
    (squarefree : Squarefree (interpret RealAlgebraicNumber.toReal algebraic_zero head))
    (precision : Nat) (isolations : IsolationCert)
    (produced : proposeIsolations head precision = some isolations)
    (gaps : isolations.checkGaps = true) :
    ∃ cert, IsolationReplay.build RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context head isolations = some cert := by
  have headNe : head ≠ 0 := (proposeIsolations_isSome_iff head precision).mp
    (by rw [produced]; rfl)
  have nonzero : interpret RealAlgebraicNumber.toReal algebraic_zero head ≠ 0 := fun h =>
    headNe ((interpret_eq_zero RealAlgebraicNumber.toReal algebraic_zero head).mp h)
  obtain ⟨root, bounds, complete⟩ := proposeIsolations_spec head precision isolations produced
  apply IsolationReplay.build_fromRoots RealAlgebraicNumber.toReal algebraic_zero
    RealAlgebraicNumber.one_toReal RealAlgebraicNumber.add_toReal
    RealAlgebraicNumber.sub_toReal RealAlgebraicNumber.mul_toReal
    RealAlgebraicNumber.neg_toReal RealAlgebraicNumber.inv_toReal
    (fun n => by change RealAlgebraicNumber.toRealHom (n : RealAlgebraicNumber) = (n : ℝ); simp)
    RealAlgebraicNumber.sign algebraic_sign
    (fun d => RealAlgebraicNumber.ofRat d.toRat)
    (fun d => by simp [HexRealRootsMathlib.toReal_eq_cast_toRat])
    context head nonzero squarefree isolations gaps root bounds complete

/-- Every nonzero squarefree canonical head eventually yields accepted
isolation evidence. This is isolation progress, not full tactic completeness. -/
theorem isolateAt_progress [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber) (nonzero : head ≠ 0)
    (squarefree : Squarefree (interpret RealAlgebraicNumber.toReal algebraic_zero head))
    (schedule : Nat → Nat) (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ cert, isolateAt context head (schedule k) = some cert := by
  obtain ⟨K, hK⟩ := proposeIsolations_separated head nonzero schedule progress
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨isolations, produced, gaps⟩ := hK k hk
  obtain ⟨cert, accepted⟩ := proposeIsolations_accepted context head squarefree (schedule k)
    isolations produced gaps
  exact ⟨cert, by unfold isolateAt; rw [produced]; exact accepted⟩

/-- Search successive precisions until the actual isolation checker accepts.
The preceding progress theorem proves termination for a nonzero squarefree
head. Root solving runs once; `Nat.find` refines only intervals and replay.
The returned proof checks the literal evidence, without a search-fuel premise.
This is a compiled producer: quotation must emit its literal certificate and
recheck that certificate in the ordinary kernel. It does not change the
tactic's bounded attempt. -/
def isolate [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber) (nonzero : head ≠ 0)
    (squarefree : Squarefree (HexPolyMathlib.Interpret.interpret
      RealAlgebraicNumber.toReal algebraic_zero head)) :
    {cert : IsolationReplay RealAlgebraicNumber Ctx //
      cert.check RealAlgebraicNumber.sign (fun d => RealAlgebraicNumber.ofRat d.toRat)
        context head = true ∧
      ∃ isolations, IsolationReplay.build RealAlgebraicNumber.sign
        (fun d => RealAlgebraicNumber.ofRat d.toRat) context head isolations = some cert} := by
  -- Root solving is independent of interval precision and runs once.
  let roots := (RealAlgebraicPoly.ofArray head.toArray).roots.finite?
  let proposal (precision : Nat) : Option IsolationCert := do
    let roots ← roots
    let intervals ← roots.mapM fun r => rootInterval r.root precision
    return ⟨intervals⟩
  let attempt (precision : Nat) : Option (IsolationReplay RealAlgebraicNumber Ctx) :=
    match proposal precision with
    | none => none
    | some isolations => IsolationReplay.build RealAlgebraicNumber.sign
        (fun d => RealAlgebraicNumber.ofRat d.toRat) context head isolations
  have attempt_eq (precision : Nat) : attempt precision = isolateAt context head precision := rfl
  have available : ∃ precision, (attempt precision).isSome = true := by
    obtain ⟨K, progress⟩ := isolateAt_progress context head nonzero squarefree id Filter.tendsto_id
    obtain ⟨cert, produced⟩ := progress K le_rfl
    change isolateAt context head K = some cert at produced
    exact ⟨K, by rw [attempt_eq, produced]; rfl⟩
  let precision := Nat.find available
  have produced := Nat.find_spec available
  let cert := (attempt precision).get produced
  have result : isolateAt context head precision = some cert := by
    rw [← attempt_eq]; exact Option.eq_some_of_isSome produced
  exact ⟨cert, isolateAt_checked context head precision cert result,
    isolateAt_build context head precision cert result⟩

end Hex.RCF.RealCoefficients
