/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldBuild
public import HexRCF.RealCoefficients.FieldRoots
public import HexRCF.RealCoefficients.FieldSignProgress
public import HexRCF.RealCoefficients.RadicalProgress
public import HexRCF.RealCoefficients.FieldRootSignsProgress
public import HexRCF.RealCoefficients.IsolationProgress
public import HexRCF.RealCoefficients.IsolationSemantics
public import HexNumberFieldMathlib.Exact
public section
namespace Hex.RCF.RealCoefficients.FieldBuild
variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- The normalized radical proposal used by the bounded frontend succeeds for
every shared carrier at the actual selected real field embedding. This is
radical production, not progress of the bounded isolation search. -/
theorem monic_progress {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (values : Fin n → PolyQuot p root) (formula : RealFormula.QF (n + 1)) :
    ∃ cert, RadicalCert.buildMonic context (FieldCarrier.product values formula) = some cert := by
  exact RadicalCert.buildMonic_success_real (Field.value rep)
    (Field.value_eq_zero rep hrep real) (Field.value_one rep hrep real)
    (Field.value_add rep hrep real) (Field.value_sub rep hrep real)
    (Field.value_mul rep hrep real) (Field.value_div rep hrep real)
    (Field.value_inv rep hrep real) (Field.value_natCast rep hrep real)
    context _ (FieldCarrier.product_ne_zero values formula)

/-- An actual normalized proposal has a squarefree core at that same selected
embedding; squarefreeness is not an assumption on the certificate. -/
theorem monic_squarefree {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (values : Fin n → PolyQuot p root) (formula : RealFormula.QF (n + 1))
    (cert : RadicalCert (PolyQuot p root) Ctx)
    (produced : RadicalCert.buildMonic context (FieldCarrier.product values formula) = some cert) :
    Squarefree (HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) cert.core) := by
  exact RadicalCert.buildMonic_squarefree (Field.value rep)
    (Field.value_eq_zero rep hrep real) (Field.value_sub rep hrep real)
    (Field.value_mul rep hrep real) (Field.value_div rep hrep real)
    (Field.value_inv rep hrep real) (Field.value_natCast rep hrep real)
    context _ cert produced

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

/-- The alternative canonical proposal API eventually produces separated intervals
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

/-- The preferred bounded search or its selected-field fallback eventually
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
    exact ⟨0, fun k _ => ⟨cert, by simp only [isolateAt, isolateAtWith, direct]⟩⟩
  | none =>
    obtain ⟨K, hK⟩ := proposeRoots_progress rep hrep head nonzero schedule progress
    refine ⟨K, fun k hk => ?_⟩
    obtain ⟨isolations, produced, gaps⟩ := hK k hk
    obtain ⟨cert, accepted⟩ := proposeRoots_accepted rep hrep real (proposalSign rep hrep)
      (proposalSign_spec rep hrep real) context head nonzero
      squarefree (schedule k) isolations produced gaps
    refine ⟨cert, ?_⟩
    simp only [isolateAt, isolateAtWith, direct]
    simp only [buildProposed, produced]
    exact accepted

/-- Construct accepted isolation evidence over the original selected field
by doubling interval precision. Selected-field root progress proves
termination; the returned certificate still passes the fixed-coordinate checker.
The preferred search and selected-field root solving each run once.
Refinement checks only interval gaps; the accepted replay is built once.
Quotation must emit the literal certificate and recheck it in the ordinary
kernel; kernel reduction of this compiled search is not required. This entry
point constructs the checked root envelope. -/
def isolateUsing [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (squarefree : Squarefree (HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) head))
    (sign : PolyQuot p root → Int) (same : sign = proposalSign rep hrep)
    (depth : Nat := 128) :
    {cert : IsolationReplay (PolyQuot p root) Ctx //
      cert.check (proposalSign rep hrep) FieldDecision.point context head = true ∧
      ∃ isolations, IsolationReplay.build (proposalSign rep hrep) FieldDecision.point
        context head isolations = some cert} := by
  -- The preferred search runs once. Only its failure starts canonical search.
  cases searched : buildProposed sign context head
      (FieldIsolate.propose? sign FieldDecision.point head depth) with
  | some cert =>
    have direct := (congrArg (fun fn => buildProposed fn context head
      (FieldIsolate.propose? fn FieldDecision.point head depth)) same).symm.trans searched
    have binding : ∃ isolations, IsolationReplay.build (proposalSign rep hrep)
        FieldDecision.point context head isolations = some cert := by
      unfold buildProposed at direct
      split at direct
      · contradiction
      · exact ⟨_, direct⟩
    refine ⟨cert, ?_⟩
    obtain ⟨isolations, built⟩ := binding
    exact ⟨(IsolationReplay.build_checked _ _ _ _ _ _ built).2, ⟨isolations, built⟩⟩
  | none =>
    -- The same selected-field roots are shared across all precision attempts.
    let roots := roots? rep hrep head
    let proposal (precision : Nat) : Option IsolationCert := do
      let roots ← roots
      let intervals ← roots.mapM fun r => rootInterval r.root precision
      return ⟨intervals⟩
    let separated (precision : Nat) := (proposal precision).filter IsolationCert.checkGaps
    have proposal_eq (precision : Nat) :
        proposal precision = proposeRoots rep hrep head precision := by
      simp only [proposal, roots, proposeRoots, bind]
    have available : ∃ k, (separated (2 ^ k)).isSome = true := by
      obtain ⟨K, progress⟩ := proposeRoots_progress rep hrep head nonzero
        (fun k => 2 ^ k) doubling_cofinal
      obtain ⟨isolations, produced, gaps⟩ := progress K le_rfl
      change proposeRoots rep hrep head (2 ^ K) = some isolations at produced
      exact ⟨K, by simp only [separated, proposal_eq, produced, Option.filter_some,
        gaps, ↓reduceIte]; rfl⟩
    let precision := 2 ^ Nat.find available
    have found : (separated precision).isSome = true := Nat.find_spec available
    let isolations := (separated precision).get found
    have filtered : separated precision = some isolations := Option.eq_some_of_isSome found
    have inputs := Option.filter_eq_some_iff.mp filtered
    have produced : proposeRoots rep hrep head precision = some isolations :=
      (proposal_eq precision).symm.trans inputs.1
    have accepted : (IsolationReplay.build sign FieldDecision.point
        context head isolations).isSome = true := by
      have meaning : ∀ a, sign a = (SignType.sign (Field.value rep a) : Int) := by
        intro a
        rw [same]
        exact proposalSign_spec rep hrep real a
      obtain ⟨cert, built⟩ := proposeRoots_accepted rep hrep real sign meaning context head nonzero
        squarefree precision isolations produced inputs.2
      rw [built]; rfl
    let cert := (IsolationReplay.build sign FieldDecision.point
      context head isolations).get accepted
    have built : IsolationReplay.build (proposalSign rep hrep) FieldDecision.point
        context head isolations = some cert := by
      have fast : IsolationReplay.build sign FieldDecision.point context head isolations =
          some cert := Option.eq_some_of_isSome accepted
      exact (congrArg (fun fn => IsolationReplay.build fn FieldDecision.point
        context head isolations) same).symm.trans fast
    exact ⟨cert, (IsolationReplay.build_checked _ _ _ _ _ _ built).2, ⟨isolations, built⟩⟩

/-- The canonical search oracle remains available to existing callers. -/
def isolate [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (head : DensePoly (PolyQuot p root)) (nonzero : head ≠ 0)
    (squarefree : Squarefree (HexPolyMathlib.Interpret.interpret
      (Field.value rep) (Field.value_eq_zero rep hrep real) head)) :=
  isolateUsing rep hrep real context head nonzero squarefree (proposalSign rep hrep) rfl

/-- Produce the complete shared carrier's radical and accepted root isolations.
Repeated and common atom roots are reduced by the actual checked gcd quotient;
squarefreeness is a proved producer conclusion. The formula retains its guard
atoms. This constructs the root envelope, not the full sign-table/decision
certificate or a quoted theorem of the source goal. -/
def isolateFormulaUsing [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (values : Fin n → PolyQuot p root) (formula : RealFormula.QF (n + 1))
    (sign : PolyQuot p root → Int) (same : sign = proposalSign rep hrep)
    (depth : Nat := 128) :
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
  exact ⟨radical, isolateUsing rep hrep real context radical.val.core
    (RadicalCert.core_ne_zero context product radical.val radical.property.2) squarefree sign same depth⟩

/-- Produce the root envelope using the canonical coordinate search signs. -/
def isolateFormula [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root) (real : rep.root.im = 0)
    (context : Ctx) (values : Fin n → PolyQuot p root) (formula : RealFormula.QF (n + 1)) :=
  isolateFormulaUsing rep hrep real context values formula (proposalSign rep hrep) rfl

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

/-- The original checked selected square produces all requested literal
field signs at one authenticated rational count-one interval. -/
theorem buildTable_success (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true)
    (keys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp))) :
    ∃ table, buildTable p s hw hp keys = some table := by
  obtain ⟨valid, card⟩ := Field.literal_domain p s hw hp real
  obtain ⟨table, produced⟩ := LiteralSign.Table.build_success (ZPoly.toRatPoly p)
    (s.re - s.radiusHi).toRat (s.re + s.radiusHi).toRat keys.dedup PolyQuot.coeffs valid card
  obtain ⟨head, lower, upper⟩ := LiteralSign.Table.build_bindings _ _ _ _ _ table produced
  have accepted := LiteralSign.Table.build_checked _ _ _ _ _ table produced
  have checked : Field.checkSignTable p s hw hp table = true := by
    simp only [Field.checkSignTable, head, lower, upper, decide_true, Bool.true_and,
      real, accepted]
  refine ⟨table, ?_⟩
  unfold buildTable
  rw [produced]
  simp only [bind, Option.bind_some, checked, ↓reduceIte]

/-- Complete fixed-field certificate production eventually succeeds along
every cofinal precision schedule. Radical, isolation, root-query and literal
sign evidence are produced by the actual builders. This is production of a
checked envelope for either verdict, not acceptance of a false source goal. -/
theorem build_progress [RealAlgebraicNumber.Laws] (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true)
    {Ctx : Type u} [DecidableEq Ctx]
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (schedule : Nat → Nat) (progress : Filter.Tendsto schedule Filter.atTop Filter.atTop) :
    ∃ K : Nat, ∀ k ≥ K, ∃ data,
      build p s hw hp values formula context (schedule k) extraSignKeys = some data := by
  let rep := Field.literalRep p s hw hp
  have hrep := Field.literalRep_mk p s hw hp
  have hr : rep.root.im = 0 := Field.literalRep_real p s hw hp real
  let product := FieldCarrier.product values formula
  obtain ⟨radical, produced⟩ := RadicalCert.build_success_real (Field.value rep)
    (Field.value_eq_zero rep hrep hr) (Field.value_one rep hrep hr)
    (Field.value_add rep hrep hr) (Field.value_sub rep hrep hr) (Field.value_mul rep hrep hr)
    (Field.value_div rep hrep hr) (Field.value_natCast rep hrep hr)
    context product (FieldCarrier.product_ne_zero values formula)
  have checked := RadicalCert.build_checked context product radical produced
  have squarefree := RadicalCert.build_squarefree (Field.value rep)
    (Field.value_eq_zero rep hrep hr) (Field.value_sub rep hrep hr)
    (Field.value_mul rep hrep hr) (Field.value_div rep hrep hr)
    (Field.value_natCast rep hrep hr) context product radical produced
  obtain ⟨K, hK⟩ := isolateAt_progress rep hrep hr context radical.core
    (RadicalCert.core_ne_zero context product radical checked) squarefree schedule progress
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨isolation, isolated⟩ := hK k hk
  obtain ⟨isolations, built⟩ := isolateAt_build rep hrep context radical.core
    (schedule k) isolation isolated
  obtain ⟨rootSigns, queried⟩ := FieldRootSigns.Table.build_success (Field.value rep)
    (Field.value_eq_zero rep hrep hr) (Field.value_one rep hrep hr)
    (Field.value_add rep hrep hr) (Field.value_sub rep hrep hr) (Field.value_mul rep hrep hr)
    (Field.value_neg rep hrep hr) (Field.value_inv rep hrep hr)
    (Field.value_natCast rep hrep hr) (proposalSign rep hrep) (proposalSign_spec rep hrep hr)
    FieldDecision.point context radical.core isolations isolation built
    (FieldSpecialize.literalPolynomial values) formula
  let keys := signKeys values formula radical.core isolation rootSigns extraSignKeys
  obtain ⟨signs, signed⟩ := buildTable_success p s hw hp real keys
  refine ⟨⟨radical, isolation, rootSigns, signs⟩, ?_⟩
  simp only [product] at produced
  change isolateAtWith (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp)
    (proposalSign rep hrep) context radical.core (schedule k) = some isolation at isolated
  change FieldRootSigns.Table.build (proposalSign rep hrep) FieldDecision.point
    context radical.core isolation (FieldSpecialize.literalPolynomial values) formula =
    some rootSigns at queried
  have signEq : (fun a : PolyQuot p (SimpleRoot.ofSquare p s hw hp) =>
      Sturm.queryPrepared (Field.prepareSign p s hw hp real).val a.coeffs) =
      proposalSign rep hrep := by
    funext a
    exact (Field.prepareSign_spec p s hw hp real a).trans
      (proposalSign_spec rep hrep hr a).symm
  unfold build
  rw [dite_eq_left real]
  dsimp only
  simp only [signEq, produced]
  simp only [isolated, queried]
  change (match buildTable p s hw hp keys with
    | none => none
    | some signs => some (Result.mk radical isolation rootSigns signs)) = _
  rw [signed]

private theorem checkedResult [RealAlgebraicNumber.Laws] (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] {Ctx : Type u} [DecidableEq Ctx]
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (data : Result p s hw hp Ctx (n + 1))
    (table : Field.checkSignTable p s hw hp data.signs = true)
    (radical : data.radical.check context (FieldCarrier.product values formula) = true)
    (isolation : data.isolation.check
      (proposalSign (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp))
      FieldDecision.point context data.radical.core = true)
    (queries : data.rootSigns.check
      (proposalSign (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp))
      FieldDecision.point context data.radical.core (FieldReplay.intervals data.isolation)
      (FieldSpecialize.literalPolynomial values) formula = true) :
    data.checkEvidence values formula context = true := by
  have real : s.meetsRealAxis = true := by
    simp only [Field.checkSignTable, Bool.and_eq_true] at table
    exact table.1.2
  have same : data.sign = proposalSign (Field.literalRep p s hw hp)
      (Field.literalRep_mk p s hw hp) := by
    funext a
    exact (Field.checkSignTable_spec p s hw hp data.signs table a).trans
      (proposalSign_spec (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp)
        (Field.literalRep_real p s hw hp real) a).symm
  simp only [Result.checkEvidence, same, table, radical, isolation, queries,
    Bool.true_and]

/-- Total production of a checked finite fixed-field certificate envelope.
The radical and root producer, atom-query builder and literal sign-table
builder each execute once. Mathematical progress proofs are erased; the
real embedding is never passed as executable data. The returned check does
not assert that the universal or existential source sentence is true. -/
def produce [RealAlgebraicNumber.Laws] (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true)
    {Ctx : Type u} [DecidableEq Ctx]
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := [])
    (depth : Nat := 256) :
    {data : Result p s hw hp Ctx (n + 1) // data.checkEvidence values formula context = true ∧
      ∀ key ∈ signKeys values formula data.radical.core data.isolation data.rootSigns extraSignKeys,
        (data.signs.lookup? key).isSome = true} := by
  let rep := Field.literalRep p s hw hp
  let hrep := Field.literalRep_mk p s hw hp
  have hr : rep.root.im = 0 := Field.literalRep_real p s hw hp real
  let prepared := Field.prepareSign p s hw hp real
  let sign := fun a : PolyQuot p (SimpleRoot.ofSquare p s hw hp) =>
    Sturm.queryPrepared prepared.val a.coeffs
  have signSpec := Field.prepareSign_spec p s hw hp real
  have same : sign = proposalSign rep hrep := by
    funext a
    exact (signSpec a).trans
      (proposalSign_spec rep hrep hr a).symm
  let envelope := isolateFormulaUsing rep hrep hr context values formula sign same depth
  let queries := FieldRootSigns.Table.build sign FieldDecision.point
    context envelope.fst.val.core envelope.snd.val
    (FieldSpecialize.literalPolynomial values) formula
  have queried : queries.isSome = true := by
    obtain ⟨isolations, isolationBuilt⟩ := envelope.snd.property.2
    have isolationBuilt := (congrArg (fun fn => IsolationReplay.build fn
      FieldDecision.point context envelope.fst.val.core isolations) same).trans isolationBuilt
    obtain ⟨table, built⟩ := FieldRootSigns.Table.build_success (Field.value rep)
      (Field.value_eq_zero rep hrep hr) (Field.value_one rep hrep hr)
      (Field.value_add rep hrep hr) (Field.value_sub rep hrep hr)
      (Field.value_mul rep hrep hr) (Field.value_neg rep hrep hr)
      (Field.value_inv rep hrep hr) (Field.value_natCast rep hrep hr)
      sign signSpec FieldDecision.point context
      envelope.fst.val.core isolations envelope.snd.val isolationBuilt
      (FieldSpecialize.literalPolynomial values) formula
    rw [show queries = some table from built]; rfl
  let rootSigns := queries.get queried
  have queryBuilt : queries = some rootSigns := Option.eq_some_of_isSome queried
  let keys := signKeys values formula envelope.fst.val.core envelope.snd.val rootSigns extraSignKeys
  have signed : (buildTable p s hw hp keys).isSome = true := by
    obtain ⟨table, built⟩ := buildTable_success p s hw hp real keys
    rw [built]; rfl
  let signs := (buildTable p s hw hp keys).get signed
  have signBuilt : buildTable p s hw hp keys = some signs := Option.eq_some_of_isSome signed
  let data : Result p s hw hp Ctx (n + 1) :=
    ⟨envelope.fst.val, envelope.snd.val, rootSigns, signs⟩
  refine ⟨data, ⟨checkedResult p s hw hp values formula context data
    (buildTable_checked p s hw hp keys signs signBuilt) envelope.fst.property.2
    envelope.snd.property.1 ?_, ?_⟩⟩
  · have queryBuilt := queryBuilt
    change FieldRootSigns.Table.build sign FieldDecision.point context
      envelope.fst.val.core envelope.snd.val
      (FieldSpecialize.literalPolynomial values) formula = some rootSigns at queryBuilt
    have queryBuilt := (congrArg (fun fn => FieldRootSigns.Table.build fn
      FieldDecision.point context envelope.fst.val.core envelope.snd.val
      (FieldSpecialize.literalPolynomial values) formula) same).symm.trans queryBuilt
    exact FieldRootSigns.Table.build_checked (proposalSign rep hrep) FieldDecision.point
      context envelope.fst.val.core envelope.snd.val
      (FieldSpecialize.literalPolynomial values) formula rootSigns queryBuilt
  · intro key requested
    exact buildTable_lookup p s hw hp keys signs signBuilt key requested

end Hex.RCF.RealCoefficients.FieldBuild
