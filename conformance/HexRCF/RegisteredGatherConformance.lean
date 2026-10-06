/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RegisteredGather
public import HexRCF.RealFormula
public meta import HexRCF.RealFormula
public import HexOrderedFnMathlib.LiouvilleTests
public meta import Lean.Util.CollectAxioms

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.OrderedFn Hex.OrderedFn.Oracle
open scoped List HexMvPolyMathlib

public section

namespace Hex.RCF.RealCoefficients.RegisteredGatherConformance
@[expose] def key : BaseContext.ConstantKey := ⟨"liouville", 1⟩
@[expose] def registry : BaseContext.Registry := fun k =>
  if k.name = "liouville" then some LiouvilleTests.provider else none
private theorem present : (registry key).isSome = true := by simp [registry, key]
noncomputable abbrev rational := BaseContext.RealPrefix.Model.rational registry
private theorem transcendence :
    letI : Field rational.context.Carrier := HexPolyMathlib.fieldOfGrind
    Real.RelativeTranscendence rational.interpretation.hom (liouvilleNumber 2) := by
  let : Field Rat := HexPolyMathlib.fieldOfGrind
  change Real.RelativeTranscendence (Rat.castHom ℝ) (liouvilleNumber 2)
  exact LiouvilleTests.transcendence
private theorem contained (δ : Rat) (_positive : 0 < δ) :
    Contains ((registry key).get present δ) (liouvilleNumber 2) :=
  LiouvilleTests.provider_contains δ
private theorem width (δ : Rat) (positive : 0 < δ) :
    ((registry key).get present δ).width ≤ δ := LiouvilleTests.provider_width δ positive
noncomputable def provider :=
  rational.register key present (liouvilleNumber 2) contained width transcendence
private theorem keys : provider.context.keys = [key] := by
  exact (BaseContext.RealPrefix.Model.register_keys rational key present
    (liouvilleNumber 2) contained width transcendence).trans (by
      simp only [rational, BaseContext.RealPrefix.Model.rational_context,
        BaseContext.RealPrefix.keys_rational, List.nil_append])

noncomputable abbrev owner := Context.ofBase provider.context.finish
noncomputable abbrev owners := [owner]

theorem decision (catalog : BaseContext.Catalog registry)
    (inserted : (BaseContext.Catalog.empty registry).insert provider.context = some catalog)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, Gather.runFrom? catalog coefficients formula quantifier =
      some result := by
  have member : provider.context ∈ catalog.prefixes :=
    (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ inserted).mpr (Or.inl rfl)
  have compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants <+ provider.context.keys ∧
        source.origin.base.depth = 0 := by
    intro source mem
    simp only [owners, List.mem_singleton] at mem
    subst source
    have origin : owner.origin.base = provider.context.finish :=
      Context.ofBase_origin_base provider.context.finish
    rw [origin]
    simp only [BaseContext.PackedContext.depth, BaseContext.RealPrefix.finish_signature]
    exact ⟨List.Sublist.refl _, True.intro⟩
  have interpreted : ∀ entry ∈ catalog.prefixes,
      (∀ source ∈ owners, source.origin.base.signature.constants <+ entry.keys) →
      ∃ model : BaseContext.RealPrefix.Model registry, model.context = entry := by
    intro entry member admitted
    have cases := (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ inserted).mp member
    rcases cases with same | original
    · exact ⟨provider, same.symm⟩
    · rw [BaseContext.Catalog.prefixes_empty] at original
      simp only [List.mem_singleton] at original
      subst entry
      exact ⟨rational, BaseContext.RealPrefix.Model.rational_context registry⟩
  obtain ⟨_, _, _, _, _, _, result, produced, _⟩ :=
    RCF.RealCoefficients.Gather.gather_catalog catalog interpreted provider.context member
      compatible coefficients formula quantifier
  exact ⟨result, produced⟩

run_meta do
  for name in #[``Gather.run_registered, ``decision] do
    let axioms ← Lean.collectAxioms name
    unless axioms == #[`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected axiom inventory {axioms}"
    Lean.logInfo m!"registered concrete gathering axioms {name}: {axioms}"

private theorem installed : ∃ catalog : BaseContext.Catalog registry,
    (BaseContext.Catalog.empty registry).insert provider.context = some catalog := by
  have unused : (BaseContext.Catalog.empty registry).lookup provider.context.keys = none :=
    BaseContext.Catalog.lookup_empty registry _ (by rw [keys]; simp)
  have success := (BaseContext.Catalog.insert_isSome_iff _ _).mpr unused
  cases produced : (BaseContext.Catalog.empty registry).insert provider.context with
  | none => simp only [produced, Option.isSome_none, Bool.false_eq_true] at success
  | some catalog => exact ⟨catalog, rfl⟩

theorem total (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ (catalog : BaseContext.Catalog registry) (result : Bool),
      (BaseContext.Catalog.empty registry).insert provider.context = some catalog ∧
      Gather.runFrom? catalog coefficients formula quantifier =
        some result := by
  obtain ⟨catalog, inserted⟩ := installed
  obtain ⟨result, produced⟩ := decision catalog inserted coefficients formula quantifier
  exact ⟨catalog, result, inserted, produced⟩

run_meta do
  for name in #[``installed, ``total] do
    let axioms ← Lean.collectAxioms name
    unless axioms == #[`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected axiom inventory {axioms}"
    Lean.logInfo m!"registered total gathering axioms {name}: {axioms}"

noncomputable def coordinate : owner.Value := ⟨RationalFn.X⟩

theorem coordinate_value : provider.towerModel.value coordinate = liouvilleNumber 2 := by
  rw [BaseContext.RealPrefix.Model.towerModel_value]
  dsimp only [coordinate, provider, rational, BaseContext.RealPrefix.Model.register,
    BaseContext.RealPrefix.Model.rational, BaseContext.RealPrefix.Model.context,
    BaseContext.RealPrefix.Model.interpretation, Context.baseStored]
  exact BaseContext.RealChain.interpretStep_X _ _ _ _ _ _ _ _ _ _

theorem source (formula : RealFormula.QF 2) (quantifier : RealFormula.Quantifier) :
    ∃ (catalog : BaseContext.Catalog registry) (result : Bool),
      (BaseContext.Catalog.empty registry).insert provider.context = some catalog ∧
      Gather.runFrom? (owners := owners) catalog
        (Fin.cases coordinate (fun i => Fin.elim0 i)) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun _ : Fin 1 => liouvilleNumber 2)) := by
  obtain ⟨catalog, inserted⟩ := installed
  obtain ⟨result, produced, semantic⟩ :=
    RCF.RealCoefficients.Gather.run_registered provider
      catalog inserted coordinate formula quantifier
  exact ⟨catalog, result, inserted, produced, by simpa only [coordinate_value] using semantic⟩

run_meta do
  for name in #[``coordinate_value, ``source] do
    let axioms ← Lean.collectAxioms name
    unless axioms == #[`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected axiom inventory {axioms}"
    Lean.logInfo m!"registered original source axioms {name}: {axioms}"

private theorem coefficient_positive : (0 : ℝ) < liouvilleNumber 2 := by
  have bounded := LiouvilleTests.provider_contains (1 / 100)
  have lower : (3 / 4 : Rat) < (LiouvilleTests.provider (1 / 100)).lower := by decide +kernel
  have positiveLower : (0 : Rat) < (LiouvilleTests.provider (1 / 100)).lower :=
    lt_trans (by norm_num : (0 : Rat) < 3 / 4) lower
  exact lt_of_lt_of_le (by exact_mod_cast positiveLower) bounded.1

/-- This is a producer law derived from real semantics, not a quoted tactic certificate. -/
theorem positive_decision :
    ∃ (catalog : BaseContext.Catalog registry),
      (BaseContext.Catalog.empty registry).insert provider.context = some catalog ∧
      Gather.runFrom? (owners := owners) catalog
        (Fin.cases coordinate (fun i => Fin.elim0 i))
        (.atom ⟨MvPoly.X 1 ^ 2 + MvPoly.X 0, .gt⟩) .forallReal = some true := by
  obtain ⟨catalog, result, inserted, produced, semantic⟩ :=
    source (.atom ⟨MvPoly.X 1 ^ 2 + MvPoly.X 0, .gt⟩) .forallReal
  have truth : ∀ x : ℝ, x ^ 2 + liouvilleNumber 2 > 0 := by
    intro x
    exact add_pos_of_nonneg_of_pos (sq_nonneg x) coefficient_positive
  have trueResult : result = true := semantic.mpr (by
    intro x
    change 0 < RealFormula.Poly.eval (MvPoly.X 1 ^ 2 + MvPoly.X 0)
      (RealFormula.append (fun _ : Fin 1 => liouvilleNumber 2) x)
    unfold RealFormula.Poly.eval
    rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
    simpa [HexMvPolyMathlib.toMvPolynomial_add,
      HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_X,
      RealFormula.append] using truth x)
  subst result
  exact ⟨catalog, inserted, produced⟩

run_meta do
  for name in #[``coefficient_positive, ``positive_decision] do
    let axioms ← Lean.collectAxioms name
    unless axioms == #[`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected axiom inventory {axioms}"
    Lean.logInfo m!"registered positive producer axioms {name}: {axioms}"

/-- False native verdicts remain diagnostic; this is a producer law. -/
theorem false_decision :
    ∃ (catalog : BaseContext.Catalog registry),
      (BaseContext.Catalog.empty registry).insert provider.context = some catalog ∧
      Gather.runFrom? (owners := owners) catalog
        (Fin.cases coordinate (fun i => Fin.elim0 i))
        (.atom ⟨MvPoly.X 1 ^ 2 + MvPoly.X 0, .lt⟩) .forallReal = some false := by
  obtain ⟨catalog, result, inserted, produced, semantic⟩ :=
    source (.atom ⟨MvPoly.X 1 ^ 2 + MvPoly.X 0, .lt⟩) .forallReal
  have falseResult : result ≠ true := by
    intro accepted
    have truth := semantic.mp accepted
    have impossible := truth 0
    change RealFormula.Poly.eval (MvPoly.X 1 ^ 2 + MvPoly.X 0)
      (RealFormula.append (fun _ : Fin 1 => liouvilleNumber 2) 0) < 0 at impossible
    unfold RealFormula.Poly.eval at impossible
    rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at impossible
    simp [HexMvPolyMathlib.toMvPolynomial_add,
      HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_X,
      RealFormula.append] at impossible
    exact (not_lt_of_ge coefficient_positive.le) impossible
  cases result with
  | false => exact ⟨catalog, inserted, produced⟩
  | true => exact False.elim (falseResult rfl)

/-- Native root production over the actual registered field reaches a further root. -/
theorem root_decision :
    ∃ (catalog : BaseContext.Catalog registry),
      (BaseContext.Catalog.empty registry).insert provider.context = some catalog ∧
      Gather.runFrom? (owners := owners) catalog
        (Fin.cases coordinate (fun i => Fin.elim0 i))
        (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩) .existsReal = some true := by
  obtain ⟨catalog, result, inserted, produced, semantic⟩ :=
    source (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩) .existsReal
  have trueResult : result = true := semantic.mpr (by
    refine ⟨Real.sqrt (liouvilleNumber 2), ?_⟩
    change RealFormula.Poly.eval (MvPoly.X 1 ^ 2 - MvPoly.X 0)
      (RealFormula.append (fun _ : Fin 1 => liouvilleNumber 2)
        (Real.sqrt (liouvilleNumber 2))) = 0
    unfold RealFormula.Poly.eval
    rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
    simpa [HexMvPolyMathlib.toMvPolynomial_sub,
      HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_X,
      RealFormula.append, sub_eq_zero] using Real.sq_sqrt coefficient_positive.le)
  subst result
  exact ⟨catalog, inserted, produced⟩

run_meta do
  for name in #[``false_decision, ``root_decision] do
    let axioms ← Lean.collectAxioms name
    unless axioms == #[`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected axiom inventory {axioms}"
    Lean.logInfo m!"registered false/root producer axioms {name}: {axioms}"

/-- Use the RCF sentence adapter's guard atoms in the bound-variable coordinate.
This does not exercise the real-coefficient source reifier's Ioc lowering. -/
@[expose] def guardedRoot (lower upper : Dyadic) : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩)
    ((RCF.RealFormula.guard lower upper).rename (fun _ => (1 : Fin 2)))

private theorem guardedRoot_correct (lower upper : Dyadic) (x : ℝ) :
    (guardedRoot lower upper).toProp
      (RealFormula.append (fun _ : Fin 1 => liouvilleNumber 2) x) ↔
      x ^ 2 = liouvilleNumber 2 ∧ x ∈ Set.Ioc
        (HexRealRootsMathlib.Dyadic.toReal lower)
        (HexRealRootsMathlib.Dyadic.toReal upper) := by
  change _ = 0 ∧ _ ↔ _
  rw [RealFormula.QF.rename_correct, RCF.RealFormula.guard_correct]
  unfold RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_sub, HexMvPolyMathlib.toMvPolynomial_pow,
    HexMvPolyMathlib.toMvPolynomial_X, RealFormula.append, sub_eq_zero]

/-- One ordinary real root satisfies the equation and the lowered Ioc guards. -/
theorem guarded_root :
    ∃ catalog : BaseContext.Catalog registry,
      (BaseContext.Catalog.empty registry).insert provider.context = some catalog ∧
      Gather.runFrom? (owners := owners) catalog
        (Fin.cases coordinate (fun i => Fin.elim0 i)) (guardedRoot (Dyadic.ofInt 0) (Dyadic.ofInt 2)) .existsReal = some true := by
  obtain ⟨catalog, result, inserted, produced, semantic⟩ := source (guardedRoot (Dyadic.ofInt 0) (Dyadic.ofInt 2)) .existsReal
  have bounded := LiouvilleTests.provider_contains 1
  have lower : (0 : Rat) < (LiouvilleTests.provider 1).lower := by decide +kernel
  have upper : (LiouvilleTests.provider 1).upper ≤ (4 : Rat) := by decide +kernel
  have pos : (0 : ℝ) < liouvilleNumber 2 := lt_of_lt_of_le (by exact_mod_cast lower) bounded.1
  have hi : liouvilleNumber 2 ≤ (4 : ℝ) := bounded.2.trans (by exact_mod_cast upper)
  have square := Real.sq_sqrt pos.le
  have nonnegative := Real.sqrt_nonneg (liouvilleNumber 2)
  have inDomain : (0 : ℝ) < Real.sqrt (liouvilleNumber 2) ∧ Real.sqrt (liouvilleNumber 2) ≤ 2 := by
    constructor <;> nlinarith
  have accepted : result = true := semantic.mpr (by
    refine ⟨Real.sqrt (liouvilleNumber 2), (guardedRoot_correct _ _ _).mpr ?_⟩
    exact ⟨square, by simpa only [HexRealRootsMathlib.toReal_ofInt, Int.cast_zero, Int.cast_ofNat, Set.mem_Ioc] using inDomain⟩)
  subst result
  exact ⟨catalog, inserted, produced⟩

/-- A domain above both roots changes the diagnostic verdict. -/
theorem excluded_root :
    ∃ catalog : BaseContext.Catalog registry,
      (BaseContext.Catalog.empty registry).insert provider.context = some catalog ∧
      Gather.runFrom? (owners := owners) catalog
        (Fin.cases coordinate (fun i => Fin.elim0 i)) (guardedRoot (Dyadic.ofInt 2) (Dyadic.ofInt 3)) .existsReal = some false := by
  obtain ⟨catalog, result, inserted, produced, semantic⟩ := source (guardedRoot (Dyadic.ofInt 2) (Dyadic.ofInt 3)) .existsReal
  have bounded := LiouvilleTests.provider_contains 1
  have upper : (LiouvilleTests.provider 1).upper ≤ (4 : Rat) := by decide +kernel
  have hi : liouvilleNumber 2 ≤ (4 : ℝ) := bounded.2.trans (by exact_mod_cast upper)
  have falseResult : result ≠ true := by
    intro accepted
    obtain ⟨x, hx⟩ := semantic.mp accepted
    obtain ⟨square, domain⟩ := (guardedRoot_correct _ _ _).mp hx
    have lower : (2 : ℝ) < x := by
      simpa only [HexRealRootsMathlib.toReal_ofInt, Int.cast_zero, Int.cast_ofNat, Set.mem_Ioc] using domain.1
    nlinarith
  cases result with
  | false => exact ⟨catalog, inserted, produced⟩
  | true => exact False.elim (falseResult rfl)

/-- The shared domain excludes its lower endpoint and includes its upper endpoint. -/
theorem guard_endpoints :
    ¬ (RCF.RealFormula.guard (Dyadic.ofInt 0) (Dyadic.ofInt 2)).toProp (fun _ => (0 : ℝ)) ∧
      (RCF.RealFormula.guard (Dyadic.ofInt 0) (Dyadic.ofInt 2)).toProp (fun _ => (2 : ℝ)) := by
  rw [RCF.RealFormula.guard_correct, RCF.RealFormula.guard_correct]
  norm_num only [Set.mem_Ioc, HexRealRootsMathlib.toReal_ofInt]
  simp only [false_and, not_false_eq_true, and_self]

-- Executable rational checks inspect the actual atom comparisons separately
-- from the real-semantic guard theorem, including a fractional lower endpoint.
#guard !(RCF.RealFormula.guard (Dyadic.ofInt 0) (Dyadic.ofInt 2)).evalRat (fun _ => 0)
#guard (RCF.RealFormula.guard (Dyadic.ofInt 0) (Dyadic.ofInt 2)).evalRat (fun _ => 2)
#guard !(RCF.RealFormula.guard (Dyadic.ofInt 1 >>> (1 : Int)) (Dyadic.ofInt 2)).evalRat
  (fun _ => 1 / 2)
#guard (RCF.RealFormula.guard (Dyadic.ofInt 1 >>> (1 : Int)) (Dyadic.ofInt 2)).evalRat
  (fun _ => 2)

run_meta do
  for name in #[``guardedRoot_correct, ``guarded_root, ``excluded_root, ``guard_endpoints] do
    let axioms ← Lean.collectAxioms name
    unless axioms == #[`propext, `Classical.choice, `Quot.sound] do
      throwError "unexpected guarded root axioms {axioms}"
    Lean.logInfo m!"registered guarded root axioms {name}: {axioms}"

end Hex.RCF.RealCoefficients.RegisteredGatherConformance
