/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RadicalBuild
public import HexPolyMathlib.Interpret
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Basic.Real.Basic
import HexRealClosureMathlib.YunInvariant
import HexNumberFieldMathlib.Yun
import Mathlib.Analysis.Complex.Polynomial.Basic
public section
namespace Hex.RCF.RealCoefficients.RadicalCert
open HexPolyMathlib
attribute [local instance 2000] Field.toGrindField

private theorem polynomial_ne_zero {K : Type*} [Field K] [DecidableEq K]
    (poly : DensePoly K) (nonzero : poly ≠ 0) : toPolynomial poly ≠ 0 := by
  intro h
  exact nonzero ((equiv (R := K)).injective (h.trans toPolynomial_zero.symm))

private theorem normalizedCore_separable {K : Type*} [Field K] [DecidableEq K]
    [CharZero K] [IsAlgClosed K] (input : DensePoly K) (nonzero : input ≠ 0)
    (degree : 0 < input.natDegree) :
    (toPolynomial (input / DensePoly.monicize
      (DensePoly.gcd input input.derivativeImpl))).Separable := by
  have invariant : Hex.RealClosure.Yun.Invariant input 1
      (input / DensePoly.monicize (DensePoly.gcd input input.derivativeImpl))
      (input.derivativeImpl / DensePoly.monicize (DensePoly.gcd input input.derivativeImpl)) :=
    Hex.RealClosure.Yun.Invariant.init input nonzero degree
  have nonzeroPolynomial := polynomial_ne_zero _ invariant.nonzero
  have simple : (toPolynomial (input / DensePoly.monicize
      (DensePoly.gcd input input.derivativeImpl))).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro x
    rw [Polynomial.count_roots]
    exact invariant.simple x
  exact (Polynomial.nodup_roots_iff_of_splits nonzeroPolynomial (IsAlgClosed.splits _)).mp simple

private theorem divide_mul {K : Type*} [Field K] [DecidableEq K]
    (input divisor : DensePoly K) (divides : divisor ∣ input) :
    toPolynomial (input / divisor) * toPolynomial divisor = toPolynomial input := by
  have identity := DensePoly.div_mul_add_mod input divisor
  rw [DensePoly.mod_eq_zero_of_dvd input divisor divides] at identity
  simpa only [toPolynomial_add, toPolynomial_mul, toPolynomial_zero, add_zero] using
    congrArg toPolynomial identity

private theorem divide_dvd {K : Type*} [Field K] [DecidableEq K]
    (input divisor : DensePoly K) (divides : divisor ∣ input) : (input / divisor) ∣ input := by
  refine ⟨divisor, ?_⟩
  apply (equiv (R := K)).injective
  simpa only [equiv_apply, toPolynomial_mul] using (divide_mul input divisor divides).symm

private theorem core_associated {K : Type*} [Field K] [DecidableEq K]
    (input : DensePoly K) (nonzero : input ≠ 0) :
    Associated (toPolynomial (input / DensePoly.gcd input input.derivativeImpl))
      (toPolynomial (input / DensePoly.monicize (DensePoly.gcd input input.derivativeImpl))) := by
  let gcd := DensePoly.gcd input input.derivativeImpl
  let normalized := DensePoly.monicize gcd
  have divides : gcd ∣ input := DensePoly.gcd_dvd_left _ _
  have gcdNe : gcd ≠ 0 := by
    intro zero
    rw [zero] at divides
    obtain ⟨q, hq⟩ := divides
    exact nonzero (by simpa only [DensePoly.zero_mul] using hq)
  have normalDivides : normalized ∣ input := DensePoly.monicize_dvd_of_dvd gcdNe divides
  have productEq : toPolynomial (input / gcd) * toPolynomial gcd = toPolynomial input := by
    exact divide_mul input gcd divides
  have normalEq : toPolynomial (input / normalized) * toPolynomial normalized = toPolynomial input := by
    exact divide_mul input normalized normalDivides
  have normalizedValue : toPolynomial normalized =
      Polynomial.C gcd.leadingCoeff⁻¹ * toPolynomial gcd := by
    dsimp only [normalized]
    rw [DensePoly.monicize_eq_scale, toPolynomial_scale]
  have gcdPolyNe := polynomial_ne_zero gcd gcdNe
  have coreEq : toPolynomial (input / gcd) =
      toPolynomial (input / normalized) * Polynomial.C gcd.leadingCoeff⁻¹ := by
    apply mul_right_cancel₀ gcdPolyNe
    rw [mul_assoc, ← normalizedValue, normalEq, productEq]
  have unit : IsUnit (Polynomial.C gcd.leadingCoeff⁻¹) := by
    apply (isUnit_iff_ne_zero.mpr (inv_ne_zero (DensePoly.leadingCoeff_ne_zero gcdNe))).map
  rw [coreEq]
  apply Associated.symm
  exact associated_mul_unit_right _ _ unit

private theorem core_separable_pos {K : Type*} [Field K] [DecidableEq K]
    [CharZero K] [IsAlgClosed K] (input : DensePoly K) (nonzero : input ≠ 0)
    (degree : 0 < input.natDegree) :
    (toPolynomial (input / DensePoly.gcd input input.derivativeImpl)).Separable :=
  (core_associated input nonzero).symm.separable
    (normalizedCore_separable input nonzero degree)

private theorem core_roots_pos {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (input : DensePoly K) (nonzero : input ≠ 0) (degree : 0 < input.natDegree) (x : K) :
    (toPolynomial (input / DensePoly.gcd input input.derivativeImpl)).IsRoot x ↔
      (toPolynomial input).IsRoot x := by
  have invariant : Hex.RealClosure.Yun.Invariant input 1
      (input / DensePoly.monicize (DensePoly.gcd input input.derivativeImpl))
      (input.derivativeImpl / DensePoly.monicize (DensePoly.gcd input input.derivativeImpl)) :=
    Hex.RealClosure.Yun.Invariant.init input nonzero degree
  have normalNe := polynomial_ne_zero _ invariant.nonzero
  have association := core_associated input nonzero
  have coreNe : toPolynomial (input / DensePoly.gcd input input.derivativeImpl) ≠ 0 := by
    intro h
    exact normalNe (association.eq_zero_iff.mp h)
  rw [← Polynomial.mem_roots coreNe, association.roots_eq, Polynomial.mem_roots normalNe,
    invariant.roots, ← Polynomial.rootMultiplicity_pos (polynomial_ne_zero input nonzero)]
  omega

private theorem core_separable {K : Type*} [Field K] [DecidableEq K]
    [CharZero K] [IsAlgClosed K] (input : DensePoly K) (nonzero : input ≠ 0) :
    (toPolynomial (input / DensePoly.gcd input input.derivativeImpl)).Separable := by
  by_cases degree : 0 < input.natDegree
  · exact core_separable_pos input nonzero degree
  · have zeroDegree : (toPolynomial input).natDegree = 0 := by
      rw [natDegree_toPolynomial]; omega
    have inputNe := polynomial_ne_zero input nonzero
    have constantEq := Polynomial.eq_C_of_natDegree_eq_zero zeroDegree
    have coefficientNe : (toPolynomial input).coeff 0 ≠ 0 := by
      intro zero
      apply inputNe
      rw [constantEq, zero, Polynomial.C_0]
    have inputSeparable : (toPolynomial input).Separable := by
      rw [constantEq]
      exact (Polynomial.separable_C _).mpr (isUnit_iff_ne_zero.mpr coefficientNe)
    apply inputSeparable.of_dvd
    exact ⟨toPolynomial (DensePoly.gcd input input.derivativeImpl),
      (divide_mul input _ (DensePoly.gcd_dvd_left _ _)).symm⟩

private theorem core_roots {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (input : DensePoly K) (nonzero : input ≠ 0) (x : K) :
    (toPolynomial (input / DensePoly.gcd input input.derivativeImpl)).IsRoot x ↔
      (toPolynomial input).IsRoot x := by
  by_cases degree : 0 < input.natDegree
  · exact core_roots_pos input nonzero degree x
  · have zeroDegree : (toPolynomial input).natDegree = 0 := by
      rw [natDegree_toPolynomial]; omega
    have inputNe := polynomial_ne_zero input nonzero
    have constantEq := Polynomial.eq_C_of_natDegree_eq_zero zeroDegree
    have coefficientNe : (toPolynomial input).coeff 0 ≠ 0 := by
      intro zero
      apply inputNe
      rw [constantEq, zero, Polynomial.C_0]
    have noRoot : ¬ (toPolynomial input).IsRoot x := by
      rw [constantEq]
      exact Polynomial.not_isRoot_C _ _ coefficientNe
    constructor
    · intro root
      rw [← divide_mul input _ (DensePoly.gcd_dvd_left _ _)]
      exact Polynomial.root_mul_right_of_isRoot _ root
    · exact fun root => False.elim (noRoot root)

private theorem quotient_dvd_power {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (input core quotient : Polynomial K) (nonzero : input ≠ 0)
    (product : core * quotient = input)
    (roots : ∀ x, core.IsRoot x ↔ input.IsRoot x) :
    quotient ∣ core ^ (input.natDegree + 1) := by
  have factors : core ≠ 0 ∧ quotient ≠ 0 := by
    exact (mul_ne_zero_iff).mp (fun h => nonzero (product.symm.trans h))
  apply (IsAlgClosed.splits quotient).dvd_of_roots_le_roots factors.2
  rw [Multiset.le_iff_count]
  intro x
  rw [Polynomial.roots_pow, Multiset.count_nsmul, Polynomial.count_roots,
    Polynomial.count_roots]
  have bound := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd nonzero
    (show quotient ∣ input from ⟨core, by rw [mul_comm, product]⟩) x
  have degreeBound := Hex.PolyQuot.Roots.rootMultiplicity_le_natDegree input nonzero x
  by_cases root : core.IsRoot x
  · have positive := (Polynomial.rootMultiplicity_pos factors.1).mpr root
    have sufficient : input.natDegree + 1 ≤
        (input.natDegree + 1) * core.rootMultiplicity x := Nat.le_mul_of_pos_right _ positive
    omega
  · have absent : ¬ quotient.IsRoot x := by
      intro h
      have present : input.IsRoot x := by
        rw [← product]
        exact Polynomial.root_mul_left_of_isRoot core h
      exact root ((roots x).mpr present)
    rw [Polynomial.rootMultiplicity_eq_zero absent]
    exact Nat.zero_le _

private theorem power_value {K : Type*} [Field K] [DecidableEq K]
    (input : DensePoly K) (n : Nat) :
    toPolynomial (DensePoly.natPow input n) = (toPolynomial input) ^ n := by
  induction n with
  | zero => rw [DensePoly.natPow_zero, toPolynomial_one, pow_zero]
  | succ n ih => rw [DensePoly.natPow_succ, toPolynomial_mul, ih, pow_succ]

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
  [Mul E] [Div E] [NatCast E]
variable {K : Type v} [Field K] [DecidableEq K] [CharZero K] [IsAlgClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
  (hs : ∀ a b, f (a - b) = f a - f b)
  (hm : ∀ a b, f (a * b) = f a * f b)
  (hd : ∀ a b, f (a / b) = f a / f b)
  (hnat : ∀ n : Nat, f (n : E) = (n : K))
  (h1 : f (1 : E) = 1) (ha : ∀ a b, f (a + b) = f a + f b)

include hz hs hm hd hnat
private theorem core_interpret (input : DensePoly E) (nonzero : input ≠ 0) :
    (Interpret.interpret f hz (input / DensePoly.gcd input input.derivativeImpl)).Separable := by
  rw [Interpret.interpret_map, DensePoly.Interpret.map_div f hz hs hm hd,
    DensePoly.Interpret.map_gcd f hz hs hm hd,
    ← DensePoly.derivative_eq_derivativeImpl,
    DensePoly.Interpret.map_derivative f hz hnat hm, DensePoly.derivative_eq_derivativeImpl]
  exact core_separable (DensePoly.Interpret.map f hz input)
    (fun h => nonzero ((DensePoly.Interpret.map_eq_zero f hz input).mp h))

omit [CharZero K] [IsAlgClosed K] [Sub E] [Div E] [NatCast E] hs hd hnat in
include h1 ha in
private theorem interpreted_power (input : DensePoly E) (n : Nat) :
    Interpret.interpret f hz (DensePoly.natPow input n) =
      (Interpret.interpret f hz input) ^ n := by
  rw [Interpret.interpret_map, DensePoly.Interpret.map_natPow f hz hm ha h1,
    power_value, ← Interpret.interpret_map]

include h1 ha in
set_option maxHeartbeats 800000 in
private theorem candidate_identities (input : DensePoly E) (nonzero : input ≠ 0) :
    let core := (DensePoly.divMod input (DensePoly.gcd input input.derivativeImpl)).1
    let quotient := (DensePoly.divMod input core).1
    let cofactor := (DensePoly.divMod (DensePoly.natPow core (input.natDegree + 1)) quotient).1
    (input - core * quotient).isZero = true ∧
      (DensePoly.natPow core (input.natDegree + 1) - quotient * cofactor).isZero = true := by
  let mapped := DensePoly.Interpret.map f hz input
  let core := (DensePoly.divMod input (DensePoly.gcd input input.derivativeImpl)).1
  let quotient := (DensePoly.divMod input core).1
  let cofactor := (DensePoly.divMod (DensePoly.natPow core (input.natDegree + 1)) quotient).1
  have mappedNe : mapped ≠ 0 := fun h => nonzero ((DensePoly.Interpret.map_eq_zero f hz input).mp h)
  have coreEq : DensePoly.Interpret.map f hz core =
      mapped / DensePoly.gcd mapped mapped.derivativeImpl := by
    change DensePoly.Interpret.map f hz (input / DensePoly.gcd input input.derivativeImpl) = _
    rw [DensePoly.Interpret.map_div f hz hs hm hd,
      DensePoly.Interpret.map_gcd f hz hs hm hd, ← DensePoly.derivative_eq_derivativeImpl,
      DensePoly.Interpret.map_derivative f hz hnat hm, DensePoly.derivative_eq_derivativeImpl]
  have coreDivides : (mapped / DensePoly.gcd mapped mapped.derivativeImpl) ∣ mapped :=
    divide_dvd mapped _ (DensePoly.gcd_dvd_left _ _)
  have quotientEq : DensePoly.Interpret.map f hz quotient =
      mapped / (mapped / DensePoly.gcd mapped mapped.derivativeImpl) := by
    change DensePoly.Interpret.map f hz (input / core) = _
    rw [DensePoly.Interpret.map_div f hz hs hm hd, coreEq]
  have productEq : toPolynomial (mapped / DensePoly.gcd mapped mapped.derivativeImpl) *
      toPolynomial (mapped / (mapped / DensePoly.gcd mapped mapped.derivativeImpl)) =
        toPolynomial mapped := by
    rw [mul_comm]
    exact divide_mul mapped _ coreDivides
  have first : Interpret.interpret f hz input =
      Interpret.interpret f hz core * Interpret.interpret f hz quotient := by
    simpa only [Interpret.interpret_map, coreEq, quotientEq] using productEq.symm
  have inputNe := polynomial_ne_zero mapped mappedNe
  have quotientNe : Interpret.interpret f hz quotient ≠ 0 := by
    intro zero
    have identity := first
    rw [zero, mul_zero] at identity
    exact inputNe (by simpa only [Interpret.interpret_map] using identity)
  have powerDivides : Interpret.interpret f hz quotient ∣
      (Interpret.interpret f hz core) ^ (input.natDegree + 1) := by
    have divides := quotient_dvd_power (toPolynomial mapped)
      (toPolynomial (mapped / DensePoly.gcd mapped mapped.derivativeImpl))
      (toPolynomial (mapped / (mapped / DensePoly.gcd mapped mapped.derivativeImpl)))
      inputNe productEq (core_roots mapped mappedNe)
    simpa only [Interpret.interpret_map, coreEq, quotientEq, natDegree_toPolynomial,
      DensePoly.Interpret.map_degree, mapped] using divides
  have cofactorEq : Interpret.interpret f hz cofactor =
      (Interpret.interpret f hz core) ^ (input.natDegree + 1) / Interpret.interpret f hz quotient := by
    have transfer := congrArg Prod.fst (Interpret.interpret_divMod f hz hs hm hd
      (DensePoly.natPow core (input.natDegree + 1)) quotient)
    simpa only [interpreted_power f hz hm h1 ha] using transfer
  constructor
  · exact (Interpret.sub_isZero f hz hs input (core * quotient)).mpr
      (by rw [Interpret.interpret_mul f hz ha hm]; exact first)
  · apply (Interpret.sub_isZero f hz hs _ _).mpr
    rw [interpreted_power f hz hm h1 ha, Interpret.interpret_mul f hz ha hm,
      cofactorEq]
    exact (EuclideanDomain.mul_div_cancel' quotientNe powerDivides).symm

include h1 ha in
/-- Zero-reflecting characteristic-zero arithmetic makes the actual bounded
radical producer succeed for every nonzero input. -/
theorem build_success {Ctx : Type w} [DecidableEq Ctx] (context : Ctx)
    (input : DensePoly E) (nonzero : input ≠ 0) :
    ∃ cert, build context input = some cert := by
  have identities := candidate_identities f hz hs hm hd hnat h1 ha input nonzero
  have separable := core_interpret f hz hs hm hd hnat input nonzero
  have coreNe : (DensePoly.divMod input (DensePoly.gcd input input.derivativeImpl)).1 ≠ 0 := by
    intro zero
    apply separable.ne_zero
    change Interpret.interpret f hz (DensePoly.divMod input
      (DensePoly.gcd input input.derivativeImpl)).1 = 0
    rw [zero, Interpret.interpret_zero]
  exact build_fromIdentities context input nonzero identities coreNe

omit hz hs hm hd hnat in
private theorem core_squarefree (value : E → ℝ) (zero : ∀ a, value a = 0 ↔ a = 0)
    (sub : ∀ a b, value (a-b) = value a - value b)
    (mul : ∀ a b, value (a*b) = value a * value b)
    (div : ∀ a b, value (a/b) = value a / value b)
    (nat : ∀ n : Nat, value (n : E) = (n : ℝ))
    (input : DensePoly E) (nonzero : input ≠ 0) :
    Squarefree (Interpret.interpret value zero
      (input / DensePoly.gcd input input.derivativeImpl)) := by
  classical
  let complex (a : E) : ℂ := value a
  have complexZero : ∀ a, complex a = 0 ↔ a = 0 := by
    intro a; simpa only [complex, Complex.ofReal_eq_zero] using zero a
  have complexSub : ∀ a b, complex (a-b) = complex a - complex b := by
    intro a b; simp only [complex, sub, Complex.ofReal_sub]
  have complexMul : ∀ a b, complex (a*b) = complex a * complex b := by
    intro a b; simp only [complex, mul, Complex.ofReal_mul]
  have complexDiv : ∀ a b, complex (a/b) = complex a / complex b := by
    intro a b; simp only [complex, div, Complex.ofReal_div]
  have complexNat : ∀ n : Nat, complex (n : E) = (n : ℂ) := by
    intro n; simp only [complex, nat, Complex.ofReal_natCast]
  have separable := core_interpret complex complexZero complexSub complexMul complexDiv complexNat
    input nonzero
  have transfer : (Interpret.interpret value zero
      (input / DensePoly.gcd input input.derivativeImpl)).map Complex.ofRealHom =
        Interpret.interpret complex complexZero (input / DensePoly.gcd input input.derivativeImpl) := by
    ext i; simp only [Polynomial.coeff_map, Interpret.coeff_interpret]; rfl
  exact ((Polynomial.separable_map Complex.ofRealHom).mp
    (by rw [transfer]; exact separable)).squarefree

omit hz hs hm hd hnat in
/-- The real interpretation consumes the actual algebraically closed-field
Yun laws through the ordinary complex embedding; no laws are asserted on raw
coefficient storage. -/
theorem build_success_real {Ctx : Type w} [DecidableEq Ctx]
    (value : E → ℝ) (zero : ∀ a, value a = 0 ↔ a = 0)
    (one : value (1 : E) = 1) (add : ∀ a b, value (a+b) = value a + value b)
    (sub : ∀ a b, value (a-b) = value a - value b)
    (mul : ∀ a b, value (a*b) = value a * value b)
    (div : ∀ a b, value (a/b) = value a / value b)
    (nat : ∀ n : Nat, value (n : E) = (n : ℝ))
    (context : Ctx) (input : DensePoly E) (nonzero : input ≠ 0) :
    ∃ cert, build context input = some cert := by
  classical
  exact build_success (fun a => (value a : ℂ))
    (fun a => by simpa only [Complex.ofReal_eq_zero] using zero a)
    (fun a b => by simp only [sub, Complex.ofReal_sub])
    (fun a b => by simp only [mul, Complex.ofReal_mul])
    (fun a b => by simp only [div, Complex.ofReal_div])
    (fun n => by simp only [nat, Complex.ofReal_natCast])
    (by simp only [one, Complex.ofReal_one])
    (fun a b => by simp only [add, Complex.ofReal_add]) context input nonzero

omit hz hs hm hd hnat in
/-- A returned radical certificate has a genuinely squarefree interpreted
core, derived from the producer's exact gcd quotient rather than assumed. -/
theorem build_squarefree {Ctx : Type w} [DecidableEq Ctx]
    (value : E → ℝ) (zero : ∀ a, value a = 0 ↔ a = 0)
    (sub : ∀ a b, value (a-b) = value a - value b)
    (mul : ∀ a b, value (a*b) = value a * value b)
    (div : ∀ a b, value (a/b) = value a / value b)
    (nat : ∀ n : Nat, value (n : E) = (n : ℝ))
    (context : Ctx) (input : DensePoly E) (cert : RadicalCert E Ctx)
    (produced : build context input = some cert) :
    Squarefree (Interpret.interpret value zero cert.core) := by
  rw [build_core context input cert produced]
  exact core_squarefree value zero sub mul div nat input (build_nonzero context input cert produced)

omit hz hs hm hd hnat in
/-- Execute the original bounded radical search using its proved progress law.
The semantic coefficient function appears only in that proof, so callers can
use a noncomputable interpretation without passing it to compiled arithmetic.
The output retains exact producer binding as well as literal acceptance;
`build_squarefree` supplies the semantic core conclusion from that binding. -/
def reduce {Ctx : Type w} [DecidableEq Ctx] (context : Ctx) (input : DensePoly E)
    (progress : ∃ cert, build context input = some cert) :
    {cert : RadicalCert E Ctx // build context input = some cert ∧ cert.check context input = true} := by
  have available : (build context input).isSome = true := by
    obtain ⟨cert, produced⟩ := progress
    rw [produced]; rfl
  let cert := (build context input).get available
  have produced : build context input = some cert := Option.eq_some_of_isSome available
  exact ⟨cert, produced, build_checked context input cert produced⟩

end Hex.RCF.RealCoefficients.RadicalCert
