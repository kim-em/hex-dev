/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FiniteReplay
public import HexRCF.RealCoefficients.FieldBuildBudget
public import HexRCF.RealCoefficients.FieldBuildProgress
public section

/-! Executable finite replay for an authenticated fixed real field. Source
expression authentication and transport are supplied by `Coefficients.Environment`.
This interface does not represent registered transcendental constants or towers. -/
namespace Hex.RCF.RealCoefficients.Replay

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable {Ctx : Type u} [DecidableEq Ctx]

/-- The complete fixed-field input. Divisors retain original order and include
those discarded by polynomial simplification. The formula retains domain atoms.
The field's defining polynomial and selected root are fixed by the type. -/
structure Input (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (Ctx : Type u) (n : Nat) where
  values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp)
  formula : RealFormula.QF (n + 1)
  quantifier : RealFormula.Quantifier
  divisors : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp))
  context : Ctx

/-- Bind a frozen envelope to its exact input. Equality is checked before any
certificate evidence or verdict is accepted. -/
structure Certificate (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (Ctx : Type u) (n : Nat) where
  input : Input p s hw hp Ctx n
  data : FieldBuild.Result p s hw hp Ctx (n + 1)

/-- Exact sentence, coefficient order, original guards and context bindings. -/
@[expose] def Input.matches (left right : Input p s hw hp Ctx n) : Bool :=
  Decidable.decide (left.values = right.values) &&
    Decidable.decide (left.formula = right.formula) &&
    Decidable.decide (left.quantifier = right.quantifier) &&
    Decidable.decide (left.divisors = right.divisors) &&
    Decidable.decide (left.context = right.context)

/-- Reflexive binding is proved without evaluating finite function equality. -/
theorem Input.matches_self (input : Input p s hw hp Ctx n) : input.matches input = true := by
  simp [Input.matches]

/-- Replay errors are structured and distinct from an accepted false verdict. -/
inductive Error where
  | binding | divisor | evidence | unresolved
  deriving DecidableEq, BEq, Repr

/-- Strict evaluation over all checked sections and sectors. -/
@[expose] def Input.value (input : Input p s hw hp Ctx n)
    (data : FieldBuild.Result p s hw hp Ctx (n + 1)) : Option Bool :=
  match input.quantifier with
  | .forallReal => data.allValue input.values input.formula
  | .existsReal => data.anyValue input.values input.formula

/-- Replay checks exact bindings, all original divisors, all recorded operands
and all evidence before the strict quantifier fold. No producer is called. -/
@[expose] def check (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) : Except Error Bool :=
  if !cert.input.matches input then .error .binding
  else if !input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) then .error .divisor
  else if !cert.data.checkFinite input.values input.formula input.context input.divisors then
    .error .evidence
  else match input.value cert.data with
    | none => .error .unresolved
    | some value => .ok value

/-- Acceptance proves each preflight gate and preserves the strict fold's
actual verdict, including false. -/
theorem check_parts (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (value : Bool)
    (h : check input cert = .ok value) :
    cert.input.matches input = true ∧
    input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) = true ∧
    cert.data.checkFinite input.values input.formula input.context input.divisors = true ∧
    input.value cert.data = some value := by
  cases binding : cert.input.matches input <;> simp only [check, binding] at h
  · contradiction
  · cases domains : input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) <;>
      simp only [domains] at h
    · contradiction
    · cases evidence : cert.data.checkFinite input.values input.formula input.context input.divisors <;>
        simp only [evidence] at h
      · contradiction
      · cases answer : input.value cert.data with
        | none => simp [answer] at h
        | some observed =>
          have same : observed = value := by simpa [answer] using h
          subst observed
          exact ⟨rfl, rfl, rfl, rfl⟩

/-- The real sentence before source-expression transport. -/
@[expose] noncomputable def Input.toProp (input : Input p s hw hp Ctx n) : Prop :=
  let valuation := fun x => RealFormula.append
    (fun j => Field.value (Field.literalRep p s hw hp) (input.values j)) x
  match input.quantifier with
  | .forallReal => ∀ x, input.formula.toProp (valuation x)
  | .existsReal => ∃ x, input.formula.toProp (valuation x)

variable [ZPoly.CheckedIrreducible p]

/-- Every original divisor is nonzero in the selected real embedding. This is
an accepted conclusion, including for constant and empty-domain sentences. -/
theorem check_domains (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (value : Bool)
    (h : check input cert = .ok value) :
    ∀ divisor ∈ input.divisors,
      Field.value (Field.literalRep p s hw hp) divisor ≠ 0 := by
  obtain ⟨binding, domains, evidence, answer⟩ := check_parts input cert value h
  have checked := cert.data.checkFinite_sound input.values input.formula input.context
    input.divisors evidence
  have table : Field.checkSignTable p s hw hp cert.data.signs = true := by
    simp only [FieldBuild.Result.checkEvidence, Bool.and_eq_true] at checked
    exact checked.1.1.1
  have real : s.meetsRealAxis = true := by
    simp only [Field.checkSignTable, Bool.and_eq_true] at table
    exact table.1.2
  intro divisor present zero
  have nonzero := List.all_eq_true.mp domains divisor present
  simp only [decide_eq_true_eq] at nonzero
  exact nonzero ((Field.value_eq_zero (Field.literalRep p s hw hp)
    (Field.literalRep_mk p s hw hp) (Field.literalRep_real p s hw hp real) divisor).mp zero)

/-- An accepted finite verdict agrees with the fixed-field real sentence. All
root coverage and real-cell obligations come from the checked evidence. -/
theorem check_spec (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (value : Bool)
    (h : check input cert = .ok value) : value = true ↔ input.toProp := by
  obtain ⟨binding, domains, evidence, answer⟩ := check_parts input cert value h
  have checked := cert.data.checkFinite_sound input.values input.formula input.context
    input.divisors evidence
  have recorded : cert.data.recorded input.values input.formula input.divisors = true := by
    simp only [FieldBuild.Result.checkFinite, Bool.and_eq_true] at evidence
    exact evidence.1.1.1.1
  have hits : ∀ key ∈ FieldBuild.signKeys input.values input.formula cert.data.radical.core
      cert.data.isolation cert.data.rootSigns,
      (cert.data.signs.lookup? key).isSome = true := by
    intro key present
    apply cert.data.recorded_spec input.values input.formula input.divisors recorded key
    simp only [FieldBuild.signKeys, List.append_nil, List.mem_append] at present
    simp only [FieldBuild.signKeys, List.mem_append]
    exact Or.inl present
  cases quantifier : input.quantifier with
  | forallReal =>
      obtain ⟨observed, folded, semantic⟩ := cert.data.forall_decision
        input.values input.formula input.context checked hits
      have same : observed = value := by
        simp only [Input.value, quantifier] at answer
        exact Option.some.inj (folded.symm.trans answer)
      subst observed
      simpa only [Input.toProp, quantifier] using semantic
  | existsReal =>
      obtain ⟨observed, folded, semantic⟩ := cert.data.exists_decision
        input.values input.formula input.context checked hits
      have same : observed = value := by
        simp only [Input.value, quantifier] at answer
        exact Option.some.inj (folded.symm.trans answer)
      subst observed
      simpa only [Input.toProp, quantifier] using semantic

/-- True acceptance proves the fixed-field sentence. False remains a diagnostic. -/
theorem check_sound (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (h : check input cert = .ok true) : input.toProp :=
  (check_spec input cert true h).mp rfl

/-- Compose with the frontend's exact original-goal equivalence. The caller
must provide that proved equivalence, not an unchecked source identity. -/
theorem check_original (input : Input p s hw hp Ctx n)
    (cert : Certificate p s hw hp Ctx n) (original : Prop)
    (equivalence : input.toProp ↔ original) (h : check input cert = .ok true) : original :=
  equivalence.mp (check_sound input cert h)

/-- Bounded production keeps input, search and replay failures distinct. -/
inductive BuildError where
  | divisor
  | search (error : FieldBuild.BuildError)
  | replay (error : Error)
  deriving DecidableEq, Repr

/-- Assemble a finite fixed-field certificate using the existing owner-backed
producer, retaining original guard operands. A rejected replay is terminal.
Acceptance is checked before returning the certificate, including false. -/
def build [RealAlgebraicNumber.Laws] (input : Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth doublings : Nat)
    (monicCore : Bool := true) : Except BuildError (Certificate p s hw hp Ctx n) :=
  if !input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) then .error .divisor
  else match FieldBuild.produceWithin p s hw hp real input.values input.formula
      input.context depth doublings input.divisors monicCore with
    | .error error => .error (.search error)
    | .ok data =>
      let cert : Certificate p s hw hp Ctx n := ⟨input, data⟩
      match check input cert with
      | .error error => .error (.replay error)
      | .ok _ => .ok cert

/-- Every returned certificate has an accepted verdict; the producer does not
claim the verdict is true, or that a bounded search must succeed. -/
theorem build_checked [RealAlgebraicNumber.Laws] (input : Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth doublings : Nat) (monicCore : Bool)
    (cert : Certificate p s hw hp Ctx n)
    (h : build input real depth doublings monicCore = .ok cert) :
    ∃ value, check input cert = .ok value := by
  unfold build at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i data produced
      dsimp only at h
      split at h
      · contradiction
      · rename_i value checked
        have same : (⟨input, data⟩ : Certificate p s hw hp Ctx n) = cert := by
          exact Except.ok.inj h
        subst cert
        exact ⟨value, checked⟩

/-- Successful bounded construction is both accepted and semantically exact.
This law says nothing about attempts which exhaust their finite resources. -/
theorem build_spec [RealAlgebraicNumber.Laws] (input : Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth doublings : Nat) (monicCore : Bool)
    (cert : Certificate p s hw hp Ctx n)
    (h : build input real depth doublings monicCore = .ok cert) :
    ∃ value, check input cert = .ok value ∧ (value = true ↔ input.toProp) := by
  obtain ⟨value, accepted⟩ := build_checked input real depth doublings monicCore cert h
  exact ⟨value, accepted, check_spec input cert value accepted⟩

/-- Total exact-field construction using the existing complete producer.
Every original zero divisor is rejected before production. This API retains
raw carrier production and its erased progress laws; it does not consume the
bounded tactic resources or represent caller-registered constants/towers. -/
def buildTotal [RealAlgebraicNumber.Laws] (input : Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth : Nat := 256) :
    Except BuildError (Certificate p s hw hp Ctx n) :=
  if input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) then
    .ok ⟨input, (FieldBuild.produce p s hw hp real input.values input.formula
      input.context input.divisors depth).val⟩
  else .error .divisor

/-- The complete producer records all operands, passes finite replay and decides
both true and false sentences. No root/sign oracle is an unproved premise. -/
theorem buildTotal_checked [RealAlgebraicNumber.Laws] (input : Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth : Nat)
    (cert : Certificate p s hw hp Ctx n)
    (h : buildTotal input real depth = .ok cert) :
    ∃ value, check input cert = .ok value := by
  unfold buildTotal at h
  split at h
  · rename_i domains
    have same := Except.ok.inj h
    subst cert
    let produced := FieldBuild.produce p s hw hp real input.values input.formula
      input.context input.divisors depth
    let data := produced.val
    have recorded : data.recorded input.values input.formula input.divisors = true :=
      List.all_eq_true.mpr produced.property.2
    have finite : data.checkFinite input.values input.formula input.context input.divisors = true := by
      rw [data.checkFinite_eq input.values input.formula input.context input.divisors recorded]
      exact produced.property.1
    have hits : ∀ key ∈ FieldBuild.signKeys input.values input.formula data.radical.core
        data.isolation data.rootSigns, (data.signs.lookup? key).isSome = true := by
      intro key present
      apply produced.property.2 key
      simp only [FieldBuild.signKeys, List.append_nil, List.mem_append] at present
      simp only [FieldBuild.signKeys, List.mem_append]
      exact Or.inl present
    have folded : ∃ value, input.value data = some value := by
      cases quantifier : input.quantifier with
      | forallReal =>
          obtain ⟨value, folded, _⟩ := data.forall_decision input.values input.formula
            input.context produced.property.1 hits
          exact ⟨value, by simpa only [Input.value, quantifier] using folded⟩
      | existsReal =>
          obtain ⟨value, folded, _⟩ := data.exists_decision input.values input.formula
            input.context produced.property.1 hits
          exact ⟨value, by simpa only [Input.value, quantifier] using folded⟩
    obtain ⟨value, folded⟩ := folded
    refine ⟨value, ?_⟩
    change check input ⟨input, data⟩ = .ok value
    simp only [check, Input.matches_self, domains, finite, Bool.not_true,
      Bool.false_eq_true, ite_false, folded]
  · contradiction

/-- Every valid exact-field input produces an accepted correct verdict,
independently of the direct proposal depth. Original divisor nonvanishing is
the valid-input condition, not an assumed certificate or goal truth. -/
theorem buildTotal_spec [RealAlgebraicNumber.Laws] (input : Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth : Nat)
    (domains : ∀ divisor ∈ input.divisors, divisor ≠ 0) :
    ∃ cert value, buildTotal input real depth = .ok cert ∧
      check input cert = .ok value ∧ (value = true ↔ input.toProp) := by
  have guards : input.divisors.all (fun divisor => Decidable.decide (divisor ≠ 0)) = true :=
    List.all_eq_true.mpr (fun divisor present => by
      simp only [decide_eq_true_eq]
      exact domains divisor present)
  let cert : Certificate p s hw hp Ctx n :=
    ⟨input, (FieldBuild.produce p s hw hp real input.values input.formula
      input.context input.divisors depth).val⟩
  have built : buildTotal input real depth = .ok cert := by
    simp only [buildTotal, guards, ↓reduceIte, cert]
  obtain ⟨value, accepted⟩ := buildTotal_checked input real depth cert built
  exact ⟨cert, value, built, accepted, check_spec input cert value accepted⟩

end Hex.RCF.RealCoefficients.Replay
