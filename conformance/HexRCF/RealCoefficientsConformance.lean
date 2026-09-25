/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients
import HexRealAlgebraicMathlib.Complex
import Lean.Elab.Command

/-! Exact source-schema equivalences and original divisor retention. -/

open Lean Meta Qq Hex.RealFormula
open Hex.RCF.RealCoefficients

namespace Hex.RCF.RealCoefficientsConformance

private def cubic : Hex.RealAlgebraicNumber :=
  (Hex.RealAlgebraicNumber.ofAlgebraic?
    (Hex.ZPoly.rootNear #p[-1, -1, 0, 1] 1.3)).getD 0

private def fieldCoefficient : Hex.RealAlgebraicNumber :=
  Coefficients.ofField cubic (cubic.toAlgebraic.toQAdjoin ^ 2 - 1)

-- These checks exercise existing root selection and fixed-field arithmetic.
#guard cubic ^ 3 = cubic + 1
#guard fieldCoefficient * cubic = 1
#guard Coefficients.ofField cubic cubic.toAlgebraic.toQAdjoin = cubic

private def coordinate (i : Fin 3) : RealFormula.Poly 3 := MvPoly.X i

private def cancellation : RealFormula.Poly 3 :=
  (coordinate 0 - coordinate 1) * coordinate 2 ^ 3 + coordinate 2 ^ 2 +
    coordinate 0 * coordinate 2 + 1

private def specialized := Specialize.polynomial (fun _ : Fin 2 => cubic) cancellation

-- Cancellation happens after interpreting the parameters, not at source syntax.
#guard cancellation.degreeOf 2 = 3
#guard specialized.natDegree = 2
#guard specialized.coeff 0 = 1
#guard specialized.coeff 1 = cubic
#guard specialized.coeff 2 = 1
#guard specialized.eval 1 = cubic + 2
#guard (Specialize.polynomial (fun _ : Fin 2 => cubic) 0).isZero
#guard (Specialize.polynomial (fun _ : Fin 2 => cubic) (MvPoly.C 3)).coeff 0 = 3

private def zeroAtom : RealFormula.QF 1 :=
  .or (.atom ⟨0, .eq⟩) (.atom ⟨MvPoly.X 0, .gt⟩)

private def repeatedAtom : RealFormula.QF 1 :=
  .or (.atom ⟨MvPoly.X 0, .eq⟩) (.atom ⟨MvPoly.X 0, .gt⟩)

-- Zero atoms contribute no factor; repeated atoms still await squarefree preparation.
#guard (Specialize.product (fun i : Fin 0 => i.elim0) zeroAtom).natDegree == 1
#guard (Specialize.product (fun i : Fin 0 => i.elim0) repeatedAtom).natDegree == 2

/-- info: 'Hex.RCF.RealCoefficients.Specialize.atom_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specialize.atom_roots

/-- info: 'Hex.RCF.RealCoefficients.Specialize.product_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specialize.product_ne_zero

private meta def prepared (source : Expr) (guards : Nat) : MetaM Reify.Source := do
  let result ← match ← Reify.prepare source with
    | .ok result => pure result
    | .error e => throwError "source preparation declined for {source}: {Hex.RealFormula.Reify.Error.toMessageData e}"
  checkWithKernel result.proof
  let expected ← mkAppM ``Iff #[← mkAppM ``Prenex.toProp #[result.formula, result.valuation], source]
  unless ← isDefEq (← inferType result.proof) expected do
    throwError "wrong source equivalence"
  unless result.divisors.size == guards do
    throwError "expected {guards} original guards, got {result.divisors.size}"
  if result.formula.hasFVar || result.formula.hasMVar || result.valuation.hasFVar ||
      result.valuation.hasMVar || result.coefficients.any (fun e => e.hasFVar || e.hasMVar) ||
      result.divisors.any (fun e => e.hasFVar || e.hasMVar) then
    throwError "escaped parameter or metavariable"
  return result

private meta def unsupported (source : Expr) : MetaM Unit := do
  match ← Reify.prepare source with
  | .error (.unsupported _ _) => pure ()
  | .error e => throwError "unexpected error: {Hex.RealFormula.Reify.Error.toMessageData e}"
  | .ok _ => throwError "unsupported source accepted"

run_meta do
  let _ ← prepared q(∀ x : ℝ, x ^ 2 + cubic.toReal * x + 1 > 0) 0
  let _ ← prepared q(∀ x : ℝ, x / cubic.toReal = fieldCoefficient.toReal * x) 1
  let _ ← prepared q(∀ x : ℝ, x * (0 / (cubic.toReal - cubic.toReal)) = 0) 1
  let _ ← prepared q(∀ x : ℝ, x + Hex.AlgebraicNumber.I.re.toReal = x) 0
  let _ ← prepared q(∀ x : ℝ,
    x + ((Hex.RealAlgebraicNumber.ofAlgebraic? Hex.AlgebraicNumber.I).getD 0).toReal = x) 0
  unsupported q(∀ x : ℝ, x + Hex.AlgebraicNumber.I.toComplex.re = x)
  pure ()

run_meta do
  let _ ← prepared q(∀ x : ℝ, x ^ 2 > Real.pi - 4) 0
  let _ ← prepared q(∀ x : ℝ, x ^ 2 + Real.exp 1 > 2) 0
  let _ ← prepared q(∃ x : ℝ, x = Real.exp 1 ∧ 2 < x ∧ x < 3) 0
  let r ← prepared q(∀ x : ℝ, x / (4 - Real.pi) = x * (4 - Real.pi)⁻¹) 2
  unless r.coefficients.size == 1 do throwError "inverse was not abstracted maximally"
  let _ ← prepared q(∀ x : ℝ, x + 1 / (4 - Real.pi) = x) 1
  let _ ← prepared q(∀ x : ℝ, x * (0 / (Real.pi - Real.pi)) = 0) 1
  let _ ← prepared q(∀ x : ℝ, x + (Real.pi - Real.pi) / (Real.pi - Real.pi) = x) 1
  let _ ← prepared q(∀ x : ℝ, x * (0 * (1 / (Real.pi - Real.pi))) = 0) 1
  let _ ← prepared q(∀ x : ℝ, x / (1 / Real.pi) = 0) 2
  let _ ← prepared q(∀ x : ℝ, x / (Real.pi - Real.pi) - x / (Real.pi - Real.pi) = 0) 1
  let _ ← prepared q(∃ x ∈ Set.Ioc (1 : ℝ) 1, x * (0 / (Real.pi - Real.pi)) = 0) 1
  let _ ← prepared q(∀ x : ℝ, x * ((Real.pi - Real.pi)⁻¹) ^ 0 = x) 1
  let _ ← prepared q(∀ x : ℝ, x < Real.pi ↔ ¬ (x ≥ Real.pi)) 0
  let _ ← prepared q(∀ x : ℝ, (x = Real.pi ∨ x ≠ Real.pi) ∧
    (x ≤ Real.pi → x < Real.pi ∨ x = Real.pi)) 0
  let _ ← prepared q(∀ x ∈ Set.Ioc (0 : ℝ) (3 / 2), x + Real.pi ≥ 0) 1
  let _ ← prepared q(∃ x ∈ Set.Ioc (1 : ℝ) 1, x = Real.exp 1) 0
  let _ ← prepared q(∀ x ∈ Set.Ioc (2 : ℝ) (-1), x < Real.pi) 0
  let _ ← prepared q(∀ x : ℝ, x + ((3 / 2 : ℚ) : ℝ) > 0) 1
  let _ ← prepared q(∀ x : ℝ, x * ((0 / 0 : ℚ) : ℝ) = 0) 1
  let _ ← prepared q(∀ _x : ℝ, True) 0
  let _ ← prepared q(∃ _x : ℝ, False) 0
  pure ()

run_meta do
  let r ← prepared q(∀ x : ℝ, Real.pi * x + Real.exp 1 * x > Real.pi) 0
  unless r.coefficients == #[q(Real.pi), q(Real.exp 1)] do
    throwError "coefficient order or deduplication changed"
  let unknown ← mkFreshExprMVar q(ℝ)
  let unknown : Q(ℝ) := unknown
  let .error (.unsupported _ _) ← Reify.prepare q(∀ x : ℝ, x + $unknown = x)
    | throwError "unresolved parameter accepted"
  if ← unknown.mvarId!.isAssigned then throwError "failed preparation assigned the source"
  withLetDecl `a q(ℝ) q(Real.pi) fun a => do
    let a : Q(ℝ) := a
    withLocalDeclD `h q($a = (1 / 2 : ℝ)) fun _ => do
      unsupported q(∀ x ∈ Set.Ioc (0 : ℝ) $a, x + Real.pi = x)
    withLocalDeclD `h q($a = Real.pi) fun _ => do
      let _ ← prepared q(∀ x : ℝ, x + $a = x + Real.pi) 0
      pure ()

run_meta do
  unsupported q(∀ x : ℝ, Real.sin x = 0)
  unsupported q(∀ x : ℝ, x + Real.sin 0 = 0)
  unsupported q(∀ x : ℝ, x / x = 1)
  unsupported q(∀ x : ℝ, x⁻¹ = 0)
  unsupported q(∀ x : ℝ, x + Real.exp 2 = 0)
  unsupported q(∀ x : ℝ, x + ((4 / 2 : ℕ) : ℝ) = 0)
  unsupported q(∀ x : ℝ, ∃ y : ℝ, x + Real.pi = y)
  unsupported q(∀ x ∈ Set.Icc (0 : ℝ) 1, x < Real.pi)
  unsupported q(∀ x ∈ Set.Ioc (0 : ℝ) (1 / 3), x < Real.pi)
  unsupported q(∀ x ∈ Set.Ioc (0 : ℝ) Real.pi, x < Real.pi)
  withLocalDeclD `a q(ℝ) fun a => do
    let a : Q(ℝ) := a
    unsupported q(∀ x : ℝ, x + $a = x)
    withLocalDeclD `h q($a = (1 / 2 : ℝ)) fun _ => do
      unsupported q(∀ x ∈ Set.Ioc (0 : ℝ) $a, x + Real.pi = x)
    withLocalDeclD `h q($a = Real.pi) fun _ => do
      let _ ← prepared q(∀ x : ℝ, x + $a = x) 0
      pure ()
  withLocalDeclD `a q(ℝ) fun a => do
    let a : Q(ℝ) := a
    withLocalDeclD `h q(Real.pi - Real.pi = $a) fun _ => do
      let r ← prepared q(∀ x : ℝ, x * (0 / $a) = 0) 1
      unless ← isDefEq r.divisors[0]! q(Real.pi - Real.pi) do
        throwError "original alias divisor was lost"
      pure ()

run_meta do
  let binary := q(@HAdd.hAdd ℝ ℝ ℝ ⟨fun _ _ => Real.sin 1⟩ Real.pi Real.pi)
  unsupported q(∀ x : ℝ, x + $binary = x)
  let unary := q(@Inv.inv ℝ ⟨fun _ => Real.sin 1⟩ Real.pi)
  unsupported q(∀ x : ℝ, x + $unary = x)
  let power := q(@HPow.hPow ℝ ℕ ℝ ⟨fun _ _ => Real.sin 1⟩ Real.pi 2)
  unsupported q(∀ x : ℝ, x + $power = x)
  let exponential := q(Real.exp (@OfNat.ofNat ℝ 1 ⟨Real.pi⟩))
  unsupported q(∀ x : ℝ, x + $exponential = x)

run_meta do
  for dimension in [Hex.Reflect.BudgetDimension.sourceNodes, .proofNodes, .exponent] do
    let result ← Reify.prepare q(∀ x : ℝ, x ^ 2 + Real.pi ^ 3 > 0)
      { ring := { budget := Hex.Reflect.Budget.default.set dimension 0 } }
    match result with
    | .error (.budget b) =>
        unless b.dimension == dimension do throwError "wrong exhausted dimension"
    | .error (.providerDeclined (.budgetExhausted b) _ _) =>
        unless b.dimension == dimension do throwError "wrong provider dimension"
    | .error e => throwError "unexpected error: {Hex.RealFormula.Reify.Error.toMessageData e}"
    | .ok _ => throwError "budget ignored"

run_meta do
  let .error (.formulaBudget _ _) ← Reify.prepare
      q(∀ x : ℝ, x > Real.pi ∨ x ≤ Real.pi) { formulaNodes := 1 }
    | throwError "formula expansion budget ignored"
  pure ()

/-- Quote an actual ordinary-kernel witness to the generated schema. -/
local elab "source_schema% " proposition:term : term => do
  let source : Q(Prop) ← Lean.Elab.Term.elabTermAndSynthesize proposition (some q(Prop))
  let source : Q(Prop) ← instantiateMVars source
  let r ← match ← Reify.prepare source with
    | .ok r => pure r
    | .error e => throwError "{Hex.RealFormula.Reify.Error.toMessageData e}"
  checkWithKernel r.proof
  let n : Q(ℕ) ← pure (mkNatLit r.coefficients.size)
  let formula : Q(Prenex $n) ← pure r.formula
  let valuation : Q(Fin $n → ℝ) ← pure r.valuation
  let proof : Q(Prenex.toProp $formula $valuation ↔ $source) ← pure r.proof
  return q((⟨$n, $formula, $valuation, $proof⟩ :
    ∃ (n : ℕ) (f : Prenex n) (ρ : Fin n → ℝ), Prenex.toProp f ρ ↔ $source))

theorem piSchema : ∃ (n : ℕ) (f : Prenex n) (ρ : Fin n → ℝ),
    Prenex.toProp f ρ ↔ (∀ x : ℝ, x ^ 2 > Real.pi - 4) :=
  source_schema% (∀ x : ℝ, x ^ 2 > Real.pi - 4)

theorem expSchema : ∃ (n : ℕ) (f : Prenex n) (ρ : Fin n → ℝ),
    Prenex.toProp f ρ ↔ (∃ x : ℝ, x = Real.exp 1 ∧ 2 < x ∧ x < 3) :=
  source_schema% (∃ x : ℝ, x = Real.exp 1 ∧ 2 < x ∧ x < 3)

theorem aliasSchema (a : ℝ) (h : Real.pi = a) :
    ∃ (n : ℕ) (f : Prenex n) (ρ : Fin n → ℝ),
      Prenex.toProp f ρ ↔ (∀ x : ℝ, x + a > x) :=
  source_schema% (∀ x : ℝ, x + a > x)

theorem quotientSchema : ∃ (n : ℕ) (f : Prenex n) (ρ : Fin n → ℝ),
    Prenex.toProp f ρ ↔ (∀ x : ℝ, x / (4 - Real.pi) = x * (4 - Real.pi)⁻¹) :=
  source_schema% (∀ x : ℝ, x / (4 - Real.pi) = x * (4 - Real.pi)⁻¹)

theorem intervalSchema : ∃ (n : ℕ) (f : Prenex n) (ρ : Fin n → ℝ),
    Prenex.toProp f ρ ↔ (∃ x ∈ Set.Ioc (1 : ℝ) 1, x = Real.exp 1) :=
  source_schema% (∃ x ∈ Set.Ioc (1 : ℝ) 1, x = Real.exp 1)

theorem fieldSchema : ∃ (n : ℕ) (f : Prenex n) (ρ : Fin n → ℝ),
    Prenex.toProp f ρ ↔ (∀ x : ℝ, x / cubic.toReal = fieldCoefficient.toReal * x) :=
  source_schema% (∀ x : ℝ, x / cubic.toReal = fieldCoefficient.toReal * x)

/-- info: 'Hex.RCF.RealCoefficientsConformance.fieldSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fieldSchema

/-- info: 'Hex.RCF.RealCoefficients.Specialize.polynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Specialize.polynomial_eval

/-- info: 'Hex.RCF.RealCoefficients.Coefficients.ofField_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Coefficients.ofField_value

/-- info: 'Hex.RCF.RealCoefficients.Coefficients.root_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Coefficients.root_alias

/-- info: 'Hex.RCF.RealCoefficientsConformance.piSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms piSchema
/-- info: 'Hex.RCF.RealCoefficientsConformance.expSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expSchema
/-- info: 'Hex.RCF.RealCoefficientsConformance.aliasSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aliasSchema

/-- info: 'Hex.RCF.RealCoefficientsConformance.quotientSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quotientSchema
/-- info: 'Hex.RCF.RealCoefficientsConformance.intervalSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intervalSchema


-- Radical notation is admitted as closed coefficient syntax. Divisors inside
-- the base and the exponent remain source obligations, even under cancellation.
run_meta do
  let _ ← prepared q(∀ x : ℝ, x ^ 2 + Real.sqrt 2 * x + 1 > 0) 0
  let _ ← prepared q(∃ x : ℝ, 0 < x ∧ x < (2 : ℝ) ^ (1 / 3 : ℝ)) 1
  let _ ← prepared q(∀ x : ℝ, x + Real.rpow 2 (1 / 3) > x) 1
  let _ ← prepared q(∀ x : ℝ, x + (2 : ℝ) ^ (3 : ℝ)⁻¹ > x) 1
  withLocalDeclD `a q(ℝ) fun a => do
    let a : Q(ℝ) ← pure a
    withLocalDeclD `h q($a = Real.sqrt 2) fun _ => do
      let _ ← prepared q(∀ x : ℝ, x + $a > x) 0
      pure ()
  let _ ← prepared q(∀ x : ℝ, x * (0 * Real.sqrt (1 / 0)) = 0) 1
  unsupported q(∀ x : ℝ, x + (2 : ℝ) ^ (1 / (3 + 0 / 0) : ℝ) > x)
  unsupported q(∀ x : ℝ, x + Real.sqrt x = 0)
  unsupported q(∀ x : ℝ, x ^ (1 / 3 : ℝ) = 0)
  unsupported q(∀ x : ℝ, (2 : ℝ) ^ x = 0)
  unsupported q(∀ x : ℝ, x + (2 : ℝ) ^ (2 / 3 : ℝ) = 0)
  unsupported q(∀ x : ℝ, x + (2 : ℝ) ^ (-1 / 3 : ℝ) = 0)
  unsupported q(∀ x : ℝ, x + (2 : ℝ) ^ Real.pi = 0)
  let power := q(@HPow.hPow ℝ ℝ ℝ ⟨fun _ _ => Real.sin 1⟩ 2 (1 / 3))
  unsupported q(∀ x : ℝ, x + $power = x)

private meta def nonnegative (source : Expr) : MetaM (Option Expr) := do
  let source : Q(ℝ) ← pure source
  let goal ← mkFreshExprMVar q(0 ≤ $source)
  let remaining ← Lean.Elab.runTactic' goal.mvarId! (← `(tactic| norm_num))
  unless remaining.isEmpty do return none
  return some (← instantiateMVars goal)

private meta def interpreted (source : Expr) : MetaM Coefficients.Prepared := do
  let result ← ((Coefficients.interpret source nonnegative).run
    { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
  match result with
  | .ok (r, _) =>
    checkWithKernel r.proof
    let target ← mkEq (← mkAppM ``Hex.RealAlgebraicNumber.toReal #[r.value]) source
    unless ← isDefEq (← inferType r.proof) target do throwError "wrong coefficient value"
    return r
  | .error e => throwError "{Hex.RealFormula.Reify.Error.toMessageData e}"

run_meta do
  for e in #[q((2 : ℝ)), q((-3 / 2 : ℝ)), q(cubic.toReal), q(fieldCoefficient.toReal),
      q(-cubic.toReal + 3 * fieldCoefficient.toReal), q(cubic.toReal⁻¹),
      q(cubic.toReal / fieldCoefficient.toReal), q(cubic.toReal ^ 3),
      q(Real.sqrt 2), q((2 : ℝ) ^ (1 / 3 : ℝ)), q(Real.rpow 2 (1 / 3)),
      q((2 : ℝ) ^ (3 : ℝ)⁻¹), q((-2 : ℝ) ^ (1 : ℝ)),
      q((2 : ℝ) ^ (1 / 6 + 1 / 6 : ℝ)), q(Real.sqrt 2 + (2 : ℝ) ^ (1 / 3 : ℝ))] do
    let _ ← interpreted e
  let r ← interpreted q(fieldCoefficient.toReal)
  unless r.value == q(fieldCoefficient) do throwError "selected field value was replaced"
  let result ← ((Coefficients.interpret q(Real.sqrt 2) (fun _ => return some (← mkEqRefl q((2 : ℝ))))).run
    { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
  let .error (.internal _) := result | throwError "wrong nonnegativity proof accepted"

local elab "coefficient_value% " scalar:term : term => do
  let source : Q(ℝ) ← Lean.Elab.Term.elabTermAndSynthesize scalar (some q(ℝ))
  let source : Q(ℝ) ← instantiateMVars source
  let r ← interpreted source
  let a : Q(Hex.RealAlgebraicNumber) ← pure r.value
  let h : Q(($a).toReal = $source) ← pure r.proof
  return q((⟨$a, $h⟩ : ∃ a : Hex.RealAlgebraicNumber, a.toReal = $source))

theorem mixedRadicals : ∃ a : Hex.RealAlgebraicNumber,
    a.toReal = Real.sqrt 2 + (2 : ℝ) ^ (1 / 3 : ℝ) :=
  coefficient_value% (Real.sqrt 2 + (2 : ℝ) ^ (1 / 3 : ℝ))

theorem fieldArithmetic : ∃ a : Hex.RealAlgebraicNumber,
    a.toReal = cubic.toReal / fieldCoefficient.toReal + 1 :=
  coefficient_value% (cubic.toReal / fieldCoefficient.toReal + 1)

/-- info: 'Hex.RCF.RealCoefficientsConformance.mixedRadicals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedRadicals

/-- info: 'Hex.RCF.RealCoefficientsConformance.fieldArithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fieldArithmetic

run_meta do
  let reference ← interpreted q((2 : ℝ) ^ (1 / 3 : ℝ))
  for e in #[q(Real.rpow 2 (1 / 3)), q((2 : ℝ) ^ (3 : ℝ)⁻¹),
      q((2 : ℝ) ^ (1 / 6 + 1 / 6 : ℝ))] do
    let candidate ← interpreted e
    unless ← isDefEq reference.value candidate.value do
      throwError "equivalent root exponents selected different algebraic values"
  for e in #[q(Real.pi), q(Real.exp 1), q((2 : ℝ) ^ (2 / 3 : ℝ)),
      q(@HAdd.hAdd ℝ ℝ ℝ ⟨fun _ _ => Real.sin 1⟩ 2 3),
      q(@Inv.inv ℝ ⟨fun _ => Real.sin 1⟩ 2),
      q(@HPow.hPow ℝ ℕ ℝ ⟨fun _ _ => Real.sin 1⟩ 2 3),
      q(@HPow.hPow ℝ ℝ ℝ ⟨fun _ _ => Real.sin 1⟩ 2 (1 / 3))] do
    let .error (.unsupported _ _) ← ((Coefficients.interpret e nonnegative).run
      { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
      | throwError "unsupported coefficient did not decline"
  withLocalDeclD `a q(ℝ) fun a => do
    let .error (.unsupported _ _) ← ((Coefficients.interpret a nonnegative).run
      { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
      | throwError "open coefficient accepted"
  let .error (.unsupported _ _) ← ((Coefficients.interpret q(Real.sqrt (-1))
      (fun _ => pure none)).run
    { config := {}, budget := .ofBudget Hex.Reflect.Budget.default }).run
    | throwError "unproved nonnegative base did not decline"
  for (source, dimension, limit) in #[
      (q((2 : ℝ) ^ (1 / 3 : ℝ)), Hex.Reflect.BudgetDimension.exponent, 2),
      (q(Real.sqrt 2), .exponent, 1), (q(Real.sqrt 2), .proofNodes, 0),
      (q(Real.sqrt 2), .sourceNodes, 0)] do
    let .error (.budget b) ← ((Coefficients.interpret source nonnegative).run
      { config := {}, budget := .ofBudget (Hex.Reflect.Budget.default.set dimension limit) }).run
      | throwError "coefficient interpretation ignored its budget"
    unless b.dimension == dimension do throwError "wrong coefficient budget dimension"

/-- info: 'Hex.RCF.RealCoefficients.Coefficients.ofField_toReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Coefficients.ofField_toReal

end Hex.RCF.RealCoefficientsConformance
