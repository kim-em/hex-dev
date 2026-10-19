/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NativeFormula
public section

/-! Partial ordinary interpretation of the specialization used by native samples.
The actual source traversal and Horner evaluation preserve all atom occurrences
and requested original divisor operands at one reader. This consumes native
production and actual provider history; it is neither frozen replay nor complete
root coverage. Source identities for inherited fixed coefficients remain explicit.
Sample conversions and literal context/arithmetic assembly are separate. -/

namespace Hex.RCF.RealCoefficients.NativeSpecialize
open Hex Hex.RealFormula Hex.RealClosure
attribute [local instance 2500] Semiring.toGrindSemiring
variable {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [Neg E] [NatCast E]
variable (read : E → ℝ) (domain : E → Prop) (closed : Transport.Closed read domain)
variable (negative : ∀ a, domain a → domain (-a) ∧ read (-a) = -read a)

omit [DecidableEq E] [Neg E] in
include closed in
private theorem power_read (a : E) (member : domain a) (k : Nat) :
    domain (Mono.powBySq a k) ∧ read (Mono.powBySq a k) = Mono.powBySq (read a) k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simpa only [Mono.powBySq] using And.intro closed.one closed.read_one
    | succ k =>
      have smaller : (k + 1) / 2 < k + 1 := Nat.div_lt_self (Nat.succ_pos k) (by decide)
      obtain ⟨hq, same⟩ := ih _ smaller
      rw [Mono.powBySq, Mono.powBySq]
      split
      · exact ⟨closed.mul _ _ hq hq, by rw [closed.read_mul _ _ hq hq, same]⟩
      · exact ⟨closed.mul _ _ (closed.mul _ _ hq hq) member, by
          rw [closed.read_mul _ _ (closed.mul _ _ hq hq) member,
            closed.read_mul _ _ hq hq, same]⟩

omit [DecidableEq E] in
include closed negative in
private theorem scalar_read (c : Int) :
    domain (RepresentationSpecialize.scalar c : E) ∧
      read (RepresentationSpecialize.scalar c : E) = (c : ℝ) := by
  cases c with
  | ofNat n => exact ⟨closed.natCast n, closed.read_natCast n⟩
  | negSucc n =>
    obtain ⟨member, same⟩ := negative (n+1 : Nat) (closed.natCast (n+1))
    exact ⟨member, by simpa only [RepresentationSpecialize.scalar,
      closed.read_natCast, Int.cast_negSucc] using same⟩

omit [DecidableEq E] in
include closed negative in
private theorem coefficient_read (values : Fin n → E) (members : ∀ i, domain (values i))
    (m : Mono (n+1)) (c : Int) :
    domain (RepresentationSpecialize.coefficient values m c) ∧
    read (RepresentationSpecialize.coefficient values m c) =
      RepresentationSpecialize.coefficient (read ∘ values) m c := by
  have fold (indices : List (Fin n)) (acc : E) (member : domain acc) :
      domain (indices.foldl (fun acc i =>
        if m[i.castSucc] = 0 then acc else acc * Mono.powBySq (values i) m[i.castSucc]) acc) ∧
      read (indices.foldl (fun acc i =>
        if m[i.castSucc] = 0 then acc else acc * Mono.powBySq (values i) m[i.castSucc]) acc) =
      indices.foldl (fun acc i =>
        if m[i.castSucc] = 0 then acc else acc * Mono.powBySq (read (values i)) m[i.castSucc]) (read acc) := by
    induction indices generalizing acc with
    | nil => exact ⟨member, rfl⟩
    | cons i rest ih =>
      by_cases unused : m[i.castSucc] = 0
      · simpa only [List.foldl_cons, unused, ite_true] using ih acc member
      · obtain ⟨hp, same⟩ := power_read read domain closed (values i) (members i) m[i.castSucc]
        have tail := ih (acc * Mono.powBySq (values i) m[i.castSucc]) (closed.mul _ _ member hp)
        simpa only [List.foldl_cons, unused, ite_false, closed.read_mul _ _ member hp, same] using tail
  obtain ⟨member, same⟩ := fold (List.finRange n) 1 closed.one
  unfold RepresentationSpecialize.coefficient
  by_cases unit : c = 1
  · exact ⟨by simpa only [unit, ite_true] using member, by
      simp only [unit, ite_true, same, closed.read_one, Function.comp_def]⟩
  · obtain ⟨hc, scalar⟩ := scalar_read read domain closed negative c
    refine ⟨by simpa only [unit, ite_false] using closed.mul _ _ hc member, ?_⟩
    simp only [unit, ite_false, closed.read_mul _ _ hc member, scalar, same,
      closed.read_one, Function.comp_def]
    congr 1
    cases c <;> simp [RepresentationSpecialize.scalar]

omit [Neg E] in
include closed in
private theorem monomial_read (k : Nat) (c : E) (member : domain c) :
    (∀ i, domain ((DensePoly.monomial k c).coeff i)) ∧
    Transport.polynomial read (DensePoly.monomial k c) = DensePoly.monomial k (read c) := by
  constructor
  · intro i
    rw [DensePoly.coeff_monomial]
    split
    · exact member
    · exact closed.zero
  · apply DensePoly.ext_coeff
    intro i
    rw [Transport.polynomial_coeff read closed.read_zero, DensePoly.coeff_monomial,
      DensePoly.coeff_monomial]
    split
    · rfl
    · exact closed.read_zero

include closed negative in
/-- The actual specialization traversal commutes with a partial reader on its
closed arithmetic domain. No zero reflection or global field map is required. -/
theorem polynomial_read (values : Fin n → E) (members : ∀ i, domain (values i))
    (q : RealFormula.Poly (n+1)) :
    (∀ i, domain ((RepresentationSpecialize.polynomial values q).coeff i)) ∧
    Transport.polynomial read (RepresentationSpecialize.polynomial values q) =
      RepresentationSpecialize.polynomial (read ∘ values) q := by
  have fold (terms : List (Mono (n+1) × Int)) (acc : DensePoly E)
      (members' : ∀ i, domain (acc.coeff i)) :
      (∀ i, domain ((terms.foldl (fun acc term => acc + DensePoly.monomial term.1[Fin.last n]
        (RepresentationSpecialize.coefficient values term.1 term.2)) acc).coeff i)) ∧
      Transport.polynomial read (terms.foldl (fun acc term => acc + DensePoly.monomial
        term.1[Fin.last n] (RepresentationSpecialize.coefficient values term.1 term.2)) acc) =
      terms.foldl (fun acc term => acc + DensePoly.monomial term.1[Fin.last n]
        (RepresentationSpecialize.coefficient (read ∘ values) term.1 term.2))
        (Transport.polynomial read acc) := by
    induction terms generalizing acc with
    | nil => exact ⟨members', rfl⟩
    | cons term rest ih =>
      obtain ⟨hc, same⟩ := coefficient_read read domain closed negative values members term.1 term.2
      obtain ⟨hm, mapped⟩ := monomial_read read domain closed term.1[Fin.last n] _ hc
      have sum := Transport.Ring.polynomial_add read closed.read_zero acc
        (DensePoly.monomial term.1[Fin.last n] _) (fun i _ =>
          closed.read_add _ _ (members' i) (hm i))
      have result := ih (acc + DensePoly.monomial term.1[Fin.last n] _) (fun i =>
        closed.coeff_add read domain _ _ (fun i _ => members' i) (fun i _ => hm i) i)
      simpa only [List.foldl_cons, sum, mapped, same] using result
  have result := fold q.termsList 0 (fun i => by simpa only [DensePoly.coeff_zero] using closed.zero)
  simpa only [RepresentationSpecialize.polynomial,
    (Transport.polynomial_zero read closed.read_zero 0 (by simp)).mpr rfl] using result

include closed negative in
/-- Evaluation at a native sample retains the exact original shared atom. -/
theorem eval_read (values : Fin n → E) (members : ∀ i, domain (values i))
    (sample : E) (present : domain sample) (q : RealFormula.Poly (n+1)) :
    read ((RepresentationSpecialize.polynomial values q).eval sample) =
      q.eval (RealFormula.append (read ∘ values) (read sample)) := by
  obtain ⟨coefficients, mapped⟩ := polynomial_read read domain closed negative values members q
  have work := Transport.Evaluation.of_closed read domain closed _ sample present
    (fun i _ => coefficients i)
  rw [Transport.Ring.polynomial_eval read closed.read_zero _ sample work.products work.sums, mapped]
  have result := RepresentationSpecialize.polynomial_eval (id : ℝ → ℝ)
    (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (read ∘ values) q (read sample)
  have identity (p : DensePoly ℝ) : HexPolyTheory.Interpret.interpret id (fun _ => Iff.rfl) p =
      HexPolyTheory.toPolynomial p := by
    ext i
    simp only [HexPolyTheory.Interpret.coeff_interpret, HexPolyTheory.coeff_toPolynomial, id_eq]
  simpa only [RepresentationSpecialize.evaluate, identity,
    HexPolyTheory.eval_toPolynomial, Function.comp_def, id_eq] using result
end Hex.RCF.RealCoefficients.NativeSpecialize

namespace Hex.RCF.RealCoefficients.NativeSpecialize
open Hex Hex.RealFormula Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {context : Context registry}

private theorem model_negative {K : Type} [Field K] [LinearOrder K] [DecidableEq K]
    (model : Model context K) (interpretation : CoefficientMap model.field ℝ)
    (a : context.Value) (member : model.domain interpretation a) :
    model.domain interpretation (-a) ∧ model.read interpretation (-a) =
      -model.read interpretation a := by
  have same : model.toValue (-a) = -model.toValue a := Subtype.ext (model.neg a)
  have member' := (model.domain_iff interpretation a).mp member
  constructor
  · apply (model.domain_iff interpretation (-a)).mpr
    rw [same]
    exact interpretation.domain.neg_mem member'
  · rw [model.read_apply, model.read_apply, same, interpretation.map_neg member']

/-- Evaluate `RepresentationSpecialize.prepare` directly in this context.
Sample-context coefficient conversion is a separate obligation. -/
@[expose] def row (context : Context registry) (values : Fin n → context.Value)
    (sample : context.Value) (formula : RealFormula.QF (n+1)) : List Int :=
  (RepresentationSpecialize.prepare values formula).map (fun p => context.sign (p.eval sample))

/-- Native specialization has the same ordered signs in any actual context
model, including coordinates available only in the sample context. -/
theorem row_model {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
    (model : Model context K) (values : Fin n → context.Value)
    (sample : context.Value) (formula : RealFormula.QF (n+1)) :
    row context values sample formula = formula.polys.map (fun q =>
      (SignType.sign (MvPoly.eval₂ (Int.castRingHom K)
        (RepresentationSpecialize.valuation (model.value ∘ values) (model.value sample)) q) : Int)) := by
  unfold row RepresentationSpecialize.prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  dsimp only [Function.comp_def]
  rw [model.sign, ← HexPolyTheory.Interpret.eval_interpret model.value model.zero_iff model.add model.mul]
  change (SignType.sign (RepresentationSpecialize.evaluate model.value model.zero_iff
    (model.value sample) (RepresentationSpecialize.polynomial values q)) : Int) = _
  exact congrArg (fun x : K => (SignType.sign x : Int))
    (RepresentationSpecialize.polynomial_eval₂ model.value model.zero_iff model.one
      model.add model.mul model.nat model.neg values q (model.value sample))

/-- info: 'Hex.RCF.RealCoefficients.NativeSpecialize.row_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_model

private theorem origin_row (origin : Origin context) (following : origin.base.Realization)
    (values : Fin n → context.Value) (sample : context.Value) (formula : RealFormula.QF (n+1)) (guards : List context.Value) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a, domain a → domain (-a) ∧ read (-a) = -read a) ∧
      (∀ i, domain (values i)) ∧ domain sample ∧
      (∀ a ∈ guards, domain a ∧ (SignType.sign (read a) : Int) = context.sign a) ∧
      (∀ q ∈ formula.polys,
        (RepresentationSpecialize.polynomial (read ∘ values) q).size =
          (RepresentationSpecialize.polynomial values q).size) ∧
      row context values sample formula = formula.polys.map
        (fun p => (SignType.sign (p.eval (RealFormula.append (read ∘ values) (read sample))) : Int)) ∧
      (∀ a r, origin.RealValue following a r → domain a ∧ read a = r) := by
  cases origin with
  | pack base suffix same =>
    cases same
    let reference := following.reference
    let model := reference.model.extend suffix
    let operands := (List.finRange n).map values ++ [sample] ++
      ((RepresentationSpecialize.prepare values formula).map (fun p => p.eval sample) ++
        (RepresentationSpecialize.prepare values formula).map (fun p => p.leadingCoeff)) ++ guards
    obtain ⟨interpretation, finite, fixed⟩ :=
      (Origin.pack base suffix rfl).realize following model operands
    let read := model.read interpretation
    let domain := model.domain interpretation
    have closed := model.closed interpretation
    have members i : domain (values i) := (finite _ (by simp [operands])).1
    have present : domain sample := (finite _ (by simp [operands])).1
    have sizes q (hq : q ∈ formula.polys) :
        (RepresentationSpecialize.polynomial (read ∘ values) q).size =
          (RepresentationSpecialize.polynomial values q).size := by
      obtain ⟨coefficients, same⟩ := polynomial_read read domain closed
        (model_negative model interpretation) values members q
      rw [← same]
      apply Transport.polynomial_size read closed.read_zero
      intro positive zero
      let p := RepresentationSpecialize.polynomial values q
      have included : p.leadingCoeff ∈ operands := by
        unfold operands
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_append_right
        simp only [RepresentationSpecialize.prepare, List.mem_map]
        exact ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      have sign : (SignType.sign (read p.leadingCoeff) : Int) =
          suffix.context.sign p.leadingCoeff := (finite _ included).2
      have mapped : read p.leadingCoeff = 0 := by
        rw [DensePoly.leadingCoeff_eq_coeff_last p positive]
        exact zero
      have mappedSign : (SignType.sign (read p.leadingCoeff) : Int) = 0 := by
        rw [mapped]
        simp
      have signZero := (model.sign p.leadingCoeff).symm.trans (sign.symm.trans mappedSign)
      have valueZero : model.value p.leadingCoeff = 0 := by
        apply sign_eq_zero_iff.mp
        cases h : SignType.sign (model.value p.leadingCoeff) with
        | neg =>
          have bad : (-1 : Int) = 0 := by
            simpa only [h, SignType.neg_eq_neg_one, SignType.coe_neg_one] using signZero
          contradiction
        | zero => rfl
        | pos =>
          have bad : (1 : Int) = 0 := by
            simpa only [h, SignType.pos_eq_one, SignType.coe_one] using signZero
          contradiction
      exact DensePoly.leadingCoeff_ne_zero_of_pos_size p positive
        ((model.zero_iff _).mp valueZero)
    refine ⟨read, domain, closed, model_negative model interpretation, members, present,
      (fun a ha => finite a (by simp [operands, ha])), sizes, ?_, fixed⟩
    unfold row RepresentationSpecialize.prepare
    simp only [List.map_map]
    apply List.map_congr_left
    intro q hq
    have included : (RepresentationSpecialize.polynomial values q).eval sample ∈ operands := by
      unfold operands
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_append_left
      simp only [RepresentationSpecialize.prepare, List.mem_map]
      exact ⟨RepresentationSpecialize.polynomial values q, ⟨q, hq, rfl⟩, rfl⟩
    have signs := (finite _ included).2
    have semantic := eval_read read domain closed (model_negative model interpretation)
      values members sample present q
    dsimp only [Function.comp_def]
    exact signs.symm.trans (congrArg (fun a : ℝ => (SignType.sign a : Int)) semantic)

/-- One ordinary reader retains specialized atom and guard signs, normalized
sizes at its coefficient coordinates, negation and inherited fixed values, even
after internal infinitesimal choices. This uses actual provider history and
native production, not frozen replay. -/
theorem row_real (context : Context registry) (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (sample : context.Value) (formula : RealFormula.QF (n+1))
    (guards : List context.Value := []) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a, domain a → domain (-a) ∧ read (-a) = -read a) ∧
      (∀ i, domain (values i)) ∧ domain sample ∧
      (∀ a ∈ guards, domain a ∧ (SignType.sign (read a) : Int) = context.sign a) ∧
      (∀ q ∈ formula.polys,
        (RepresentationSpecialize.polynomial (read ∘ values) q).size =
          (RepresentationSpecialize.polynomial values q).size) ∧
      row context values sample formula = formula.polys.map
        (fun p => (SignType.sign (p.eval (RealFormula.append (read ∘ values) (read sample))) : Int)) ∧
      (∀ a r, context.origin.RealValue following a r → domain a ∧ read a = r) :=
  origin_row context.origin following values sample formula guards

/-- A true specialized row gives one real witness with every requested original
nonzero divisor at that same reader. Original source identities remain explicit. -/
theorem true_real (context : Context registry) (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (original : Fin n → ℝ)
    (fixed : ∀ i, context.origin.RealValue following (values i) (original i))
    (sample : context.Value) (formula : RealFormula.QF (n+1)) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval formula (row context values sample formula) = some true) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ a, domain a → domain (-a) ∧ read (-a) = -read a) ∧ domain sample ∧
      (∀ q ∈ formula.polys,
        (RepresentationSpecialize.polynomial original q).size =
          (RepresentationSpecialize.polynomial values q).size) ∧
      formula.toProp (RealFormula.append original (read sample)) ∧
      (∀ a ∈ guards, domain a ∧ read a ≠ 0) ∧
      (∀ a r, context.origin.RealValue following a r → domain a ∧ read a = r) := by
  obtain ⟨read, domain, closed, negative, members, present, guardSigns, sizes, signs, real⟩ :=
    row_real context following values sample formula guards
  have same : read ∘ values = original := by
    funext i
    exact (real _ _ (fixed i)).2
  have meaning := (Samples.Row.eval_true formula _ _ signs).mp truth
  rw [same] at meaning
  refine ⟨read, domain, closed, negative, present, ?_, meaning, ?_, real⟩
  · simpa only [same] using sizes
  · intro a member
    obtain ⟨ha, sign⟩ := guardSigns a member
    refine ⟨ha, ?_⟩
    intro zero
    apply nonzero a member
    simpa only [zero, sign_zero, SignType.coe_zero] using sign.symm

/-- A false specialized point row supplies a real universal counterexample.
No false existential or complete cell-cover decision is claimed. -/
theorem not_forall (context : Context registry) (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (original : Fin n → ℝ)
    (fixed : ∀ i, context.origin.RealValue following (values i) (original i))
    (sample : context.Value) (formula : RealFormula.QF (n+1))
    (falseRow : Samples.Row.eval formula (row context values sample formula) = some false) :
    ¬ ∀ x : ℝ, formula.toProp (RealFormula.append original x) := by
  obtain ⟨read, domain, closed, negative, members, present, guards, sizes, signs, real⟩ :=
    row_real context following values sample formula
  have same : read ∘ values = original := by
    funext i
    exact (real _ _ (fixed i)).2
  intro all
  have meaning : formula.toProp (RealFormula.append (read ∘ values) (read sample)) := by
    rw [same]
    exact all (read sample)
  have accepted := (Samples.Row.eval_true formula _ _ signs).mpr meaning
  rw [falseRow] at accepted
  contradiction

end Hex.RCF.RealCoefficients.NativeSpecialize

