/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldBuild
public import HexRCF.RealCoefficients.RadicalProgress
public import HexRCF.RealCoefficients.FieldRootSignsProgress
public import HexRCF.RealCoefficients.IsolationProgress
public import HexRCF.RealCoefficients.IsolationSemantics
public import HexNumberFieldMathlib.Exact
public section
namespace Hex.RCF.RealCoefficients.FieldBuild
variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- Every coordinate over the checked selected real root has a canonical
real-algebraic search value. -/
theorem canonical_isSome (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (a : PolyQuot p root) :
    (canonical? rep hrep a).isSome = true := by
  have available := PolyQuot.toAlgebraicNumber?_isSome a rep hrep
  cases produced : a.toAlgebraicNumber? rep hrep with
  | none => simp [produced] at available
  | some algebraic =>
    have value := PolyQuot.toAlgebraicNumber?_sound a rep hrep produced
    have reality : algebraic.isReal = true := by
      rw [AlgebraicNumber.isReal_iff, value, ← Field.value_complex rep hrep real]
      rfl
    simp only [canonical?, produced, bind, Option.bind, RealAlgebraicNumber.ofAlgebraic?_isSome, reality]

/-- Canonical conversion preserves the selected embedding of the original
fixed-field coordinate. -/
theorem canonical_value (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (a : PolyQuot p root) (b : RealAlgebraicNumber)
    (produced : canonical? rep hrep a = some b) : b.toReal = Field.value rep a := by
  obtain ⟨algebraic, conversion, reality⟩ := Option.bind_eq_some_iff.mp produced
  have value := PolyQuot.toAlgebraicNumber?_sound a rep hrep conversion
  have same := (RealAlgebraicNumber.ofAlgebraic?_eq_some algebraic b).mp reality
  apply Complex.ofReal_injective
  rw [RealAlgebraicNumber.ofReal_toReal, ← same, value, Field.value_complex rep hrep real]

/-- The search-only sign oracle has the exact real sign at the selected
embedding; its zero fallback is unreachable for a checked real root. -/
theorem proposalSign_spec (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (a : PolyQuot p root) :
    proposalSign rep hrep a = (SignType.sign (Field.value rep a) : Int) := by
  have available := canonical_isSome rep hrep real a
  cases produced : canonical? rep hrep a with
  | none => simp [produced] at available
  | some b =>
    simp only [proposalSign, produced, Option.map_some, Option.getD_some]
    rw [algebraic_sign, canonical_value rep hrep real a b produced]

/-- Converting the native coefficient array preserves the exact interpreted
polynomial, including zero padding and leading cancellation. -/
theorem canonical_polynomial (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (head : DensePoly (PolyQuot p root)) :
    ∃ coefficients, head.toArray.mapM (canonical? rep hrep) = some coefficients ∧
      (RealAlgebraicPoly.ofArray coefficients).toPolynomial =
        HexPolyMathlib.Interpret.interpret (Field.value rep) (Field.value_eq_zero rep hrep real) head := by
  let convert (a : PolyQuot p root) :=
    (canonical? rep hrep a).get (canonical_isSome rep hrep real a)
  have produced (a : PolyQuot p root) : canonical? rep hrep a = some (convert a) :=
    Option.eq_some_of_isSome _
  have value (a : PolyQuot p root) : (convert a).toReal = Field.value rep a :=
    canonical_value rep hrep real a _ (produced a)
  refine ⟨head.toArray.map convert, ?_, ?_⟩
  · have funEq : canonical? rep hrep = (fun a => (pure (convert a) : Option RealAlgebraicNumber)) :=
      funext produced
    rw [funEq]; exact Array.mapM_pure
  · ext i
    rw [RealAlgebraicPoly.coeff_ofArray, HexPolyMathlib.Interpret.coeff_interpret]
    rw [← DensePoly.toArray_getD head i]
    by_cases inside : i < head.toArray.size
    · have mapped : i < (head.toArray.map convert).size := by simpa only [Array.size_map] using inside
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside,
        Array.getElem?_eq_getElem mapped, Option.getD_some, Array.getElem_map]
      exact value _
    · have outside : head.toArray.size ≤ i := Nat.le_of_not_gt inside
      have mapped : (head.toArray.map convert).size ≤ i := by simpa only [Array.size_map] using outside
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none outside,
        Array.getElem?_eq_none mapped, Option.getD_none, RealAlgebraicNumber.zero_toReal]
      exact (Field.value_zero rep hrep real).symm

/-- The actual canonical fallback eventually produces separated intervals
for every nonzero fixed-field head along a cofinal precision schedule. -/
theorem proposeCanonical_progress [RealAlgebraicNumber.Laws]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (schedule : Nat → Nat) (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ cert : IsolationCert,
      proposeCanonical rep hrep head (schedule k) = some cert ∧ cert.checkGaps = true := by
  obtain ⟨coefficients, converted, polynomial⟩ := canonical_polynomial rep hrep real head
  let solver := RealAlgebraicPoly.ofArray coefficients
  have polynomialNe : solver.toPolynomial ≠ 0 := by
    rw [polynomial]
    exact fun h => nonzero ((HexPolyMathlib.Interpret.interpret_eq_zero
      (Field.value rep) (Field.value_eq_zero rep hrep real) head).mp h)
  obtain ⟨K, hK⟩ := solverIntervals_progress solver polynomialNe schedule progress
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨cert, generated, gaps⟩ := hK k hk
  refine ⟨cert, ?_, gaps⟩
  change (head.toArray.mapM (canonical? rep hrep)).bind
    (fun coefficients => solverIntervals (RealAlgebraicPoly.ofArray coefficients) (schedule k)) = some cert
  rw [converted]; exact generated

/-- A separated canonical proposal is accepted over the original field
coordinates when their interpreted head is nonzero and squarefree. -/
theorem proposeCanonical_accepted [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (squarefree : Squarefree (HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) head))
    (precision : Nat) (isolations : IsolationCert)
    (produced : proposeCanonical rep hrep head precision = some isolations)
    (gaps : isolations.checkGaps = true) :
    ∃ cert, IsolationReplay.build (proposalSign rep hrep) FieldDecision.point context head isolations = some cert := by
  obtain ⟨coefficients, converted, polynomial⟩ := canonical_polynomial rep hrep real head
  let solver := RealAlgebraicPoly.ofArray coefficients
  have generated : solverIntervals solver precision = some isolations := by
    change (head.toArray.mapM (canonical? rep hrep)).bind
      (fun coefficients => solverIntervals (RealAlgebraicPoly.ofArray coefficients) precision) = some isolations at produced
    simpa only [converted, Option.bind_some] using produced
  obtain ⟨values, bounds, complete⟩ := solverIntervals_spec solver precision isolations generated
  have complete' : ∀ x, (HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) head).IsRoot x ↔ ∃ i, values i = x := by
    simpa only [solver, polynomial] using complete
  have polynomialNe : HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) head ≠ 0 := fun h =>
    nonzero ((HexPolyMathlib.Interpret.interpret_eq_zero
      (Field.value rep) (Field.value_eq_zero rep hrep real) head).mp h)
  apply IsolationReplay.build_fromRoots (Field.value rep) (Field.value_eq_zero rep hrep real)
    (Field.value_one rep hrep real) (Field.value_add rep hrep real)
    (Field.value_sub rep hrep real) (Field.value_mul rep hrep real)
    (Field.value_neg rep hrep real) (Field.value_inv rep hrep real)
    (Field.value_natCast rep hrep real) (proposalSign rep hrep) (proposalSign_spec rep hrep real)
    FieldDecision.point ?_ context head polynomialNe squarefree isolations gaps values bounds complete'
  intro d
  simpa only [FieldDecision.point, HexRealRootsMathlib.toReal_eq_cast_toRat] using
    FieldSpecialize.value_ofRat rep hrep real d.toRat

/-- The preferred bounded search or its canonical fallback eventually
yields accepted fixed-field isolation evidence for a nonzero squarefree head.
The statement does not assert full certificate construction or tactic totality. -/
theorem isolateAt_progress [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (squarefree : Squarefree (HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) head))
    (schedule : Nat → Nat) (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ cert, isolateAt rep hrep context head (schedule k) = some cert := by
  cases direct : buildProposed (proposalSign rep hrep) context head
      (FieldIsolate.propose? (proposalSign rep hrep) FieldDecision.point head) with
  | some cert =>
    exact ⟨0, fun k _ => ⟨cert, by simp only [isolateAt, direct]⟩⟩
  | none =>
    obtain ⟨K, hK⟩ := proposeCanonical_progress rep hrep real head nonzero schedule progress
    refine ⟨K, fun k hk => ?_⟩
    obtain ⟨isolations, produced, gaps⟩ := hK k hk
    obtain ⟨cert, accepted⟩ := proposeCanonical_accepted rep hrep real context head nonzero
      squarefree (schedule k) isolations produced gaps
    refine ⟨cert, ?_⟩
    simp only [isolateAt, direct]
    simp only [buildProposed, produced]
    exact accepted

/-- Construct accepted isolation evidence over the original selected field
by searching successive precisions. Canonical conversion and progress prove
termination; the returned certificate still passes the fixed-coordinate checker.
The preferred search, head conversion and root solving each run once.
Refinement checks only interval gaps; the accepted replay is built once.
Quotation must emit the literal certificate and recheck it in the ordinary
kernel; kernel reduction of this compiled search is not required. This does
not assert termination of the full formula certificate producer. -/
def isolate [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (squarefree : Squarefree (HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) head)) :
    {cert : IsolationReplay (PolyQuot p root) Ctx //
      cert.check (proposalSign rep hrep) FieldDecision.point context head = true ∧
      ∃ isolations, IsolationReplay.build (proposalSign rep hrep) FieldDecision.point
        context head isolations = some cert} := by
  -- The preferred search runs once. Only its failure starts canonical search.
  cases direct : buildProposed (proposalSign rep hrep) context head
      (FieldIsolate.propose? (proposalSign rep hrep) FieldDecision.point head) with
  | some cert =>
    have result : isolateAt rep hrep context head 0 = some cert := by
      simp only [isolateAt, direct]
    exact ⟨cert, isolateAt_checked rep hrep context head 0 cert result,
      isolateAt_build rep hrep context head 0 cert result⟩
  | none =>
    -- Conversion and complete root solving are shared across all precisions.
    let roots := (head.toArray.mapM (canonical? rep hrep)).bind fun coefficients =>
      (RealAlgebraicPoly.ofArray coefficients).roots.finite?
    let proposal (precision : Nat) : Option IsolationCert := do
      let roots ← roots
      let intervals ← roots.mapM fun r => rootInterval r.root precision
      return ⟨intervals⟩
    let separated (precision : Nat) := (proposal precision).filter IsolationCert.checkGaps
    have proposal_eq (precision : Nat) :
        proposal precision = proposeCanonical rep hrep head precision := by
      simp only [proposal, roots, proposeCanonical, solverIntervals, bind, Option.bind_assoc]
    have available : ∃ precision, (separated precision).isSome = true := by
      obtain ⟨K, progress⟩ := proposeCanonical_progress rep hrep real head nonzero
        id Filter.tendsto_id
      obtain ⟨isolations, produced, gaps⟩ := progress K le_rfl
      change proposeCanonical rep hrep head K = some isolations at produced
      exact ⟨K, by simp only [separated, proposal_eq, produced, Option.filter_some,
        gaps, ↓reduceIte]; rfl⟩
    let precision := Nat.find available
    have found := Nat.find_spec available
    let isolations := (separated precision).get found
    have filtered : separated precision = some isolations := Option.eq_some_of_isSome found
    have inputs := Option.filter_eq_some_iff.mp filtered
    have produced : proposeCanonical rep hrep head precision = some isolations :=
      (proposal_eq precision).symm.trans inputs.1
    have accepted : (IsolationReplay.build (proposalSign rep hrep) FieldDecision.point
        context head isolations).isSome = true := by
      obtain ⟨cert, built⟩ := proposeCanonical_accepted rep hrep real context head nonzero
        squarefree precision isolations produced inputs.2
      rw [built]; rfl
    let cert := (IsolationReplay.build (proposalSign rep hrep) FieldDecision.point
      context head isolations).get accepted
    have built : IsolationReplay.build (proposalSign rep hrep) FieldDecision.point
        context head isolations = some cert := Option.eq_some_of_isSome accepted
    exact ⟨cert, (IsolationReplay.build_checked _ _ _ _ _ _ built).2, ⟨isolations, built⟩⟩

/-- Produce the complete shared carrier's radical and accepted root isolations.
Repeated and common atom roots are reduced by the actual checked gcd quotient;
squarefreeness is a proved producer conclusion. The formula retains its guard
atoms. This constructs the root envelope, not the full sign-table/decision
certificate or a quoted theorem of the source goal. -/
def isolateFormula [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (values : Fin n → PolyQuot p root) (formula : RealFormula.QF (n + 1)) :
    Σ radical : {cert : RadicalCert (PolyQuot p root) Ctx //
      RadicalCert.build context (FieldCarrier.product values formula) = some cert ∧
        cert.check context (FieldCarrier.product values formula) = true},
      {cert : IsolationReplay (PolyQuot p root) Ctx //
        cert.check (proposalSign rep hrep) FieldDecision.point context radical.val.core = true ∧
          ∃ isolations, IsolationReplay.build (proposalSign rep hrep) FieldDecision.point
            context radical.val.core isolations = some cert} := by
  let product := FieldCarrier.product values formula
  let radical := RadicalCert.reduce context product
    (RadicalCert.build_success_real (Field.value rep) (Field.value_eq_zero rep hrep real)
      (Field.value_one rep hrep real) (Field.value_add rep hrep real)
      (Field.value_sub rep hrep real) (Field.value_mul rep hrep real)
      (Field.value_div rep hrep real) (Field.value_natCast rep hrep real)
      context product (FieldCarrier.product_ne_zero values formula))
  have squarefree := RadicalCert.build_squarefree (Field.value rep)
    (Field.value_eq_zero rep hrep real) (Field.value_sub rep hrep real)
    (Field.value_mul rep hrep real) (Field.value_div rep hrep real)
    (Field.value_natCast rep hrep real) context product radical.val radical.property.1
  exact ⟨radical, isolate rep hrep real context radical.val.core
    (RadicalCert.core_ne_zero context product radical.val radical.property.2) squarefree⟩

/-- The total formula root producer carries the exact binding consumed by
atom-query production, so every root query is built and checked at that same
selected embedding, carrier core and isolation interval. -/
theorem isolateFormula_queries [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (values : Fin n → PolyQuot p root) (formula : RealFormula.QF (n + 1)) :
    let data := isolateFormula rep hrep real context values formula
    ∃ table, FieldRootSigns.Table.build (proposalSign rep hrep) FieldDecision.point
      context data.fst.val.core data.snd.val
      (FieldSpecialize.literalPolynomial values) formula = some table := by
  let data := isolateFormula rep hrep real context values formula
  obtain ⟨isolations, produced⟩ := data.snd.property.2
  exact FieldRootSigns.Table.build_success (Field.value rep) (Field.value_eq_zero rep hrep real)
    (Field.value_one rep hrep real) (Field.value_add rep hrep real) (Field.value_sub rep hrep real)
    (Field.value_mul rep hrep real) (Field.value_neg rep hrep real) (Field.value_inv rep hrep real)
    (Field.value_natCast rep hrep real) (proposalSign rep hrep) (proposalSign_spec rep hrep real)
    FieldDecision.point context data.fst.val.core isolations data.snd.val produced
    (FieldSpecialize.literalPolynomial values) formula

end Hex.RCF.RealCoefficients.FieldBuild
