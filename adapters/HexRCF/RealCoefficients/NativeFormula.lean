/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.Samples
public import HexRealClosureMathlib.NativeRealization
public section

/-! Shared-formula semantics for the owner's actual finite native realization.
Native point evaluation retains every atom and its integer coefficient. The
partial ordinary reader preserves the reached arithmetic without a global
field interpretation of symbolic infinitesimals. Fixed source coordinates
require the stored origin's explicit inherited-real-value proofs.

Frozen replay still requires checked context/history and reached arithmetic
assembly, exact original-source equivalence and every original divisor guard.
The native row below performs sign production and supplies no root coverage. -/
namespace Hex.RCF.RealCoefficients.NativeFormula
open Hex Hex.RealFormula Hex.RealClosure
attribute [local instance 2500] Semiring.toGrindSemiring
variable {E : Type} [Zero E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]

/-- Interpret an integer using the actual casts and subtraction supplied by
`Transport.Closed`. Negative integers use subtraction from zero. -/
@[expose] def scalar : Int → E
  | .ofNat n => (n : E)
  | .negSucc n => 0 - (n + 1 : Nat)

/-- Evaluate the existing shared polynomial at one native point. Every term
uses its stored monomial and actual coefficient operations. -/
@[expose] def polynomial (values : Fin n → E) (p : RealFormula.Poly n) : E :=
  p.termsList.foldl (fun acc term => acc + scalar term.2 * Mono.prod values term.1) 0

omit [Zero E] [One E] [Add E] [Sub E] [Mul E] [NatCast E] in
private theorem fold {A : Type} (read : E → ℝ) (domain : E → Prop)
    (xs : List A) (step : E → A → E) (mapped : ℝ → A → ℝ)
    (closed : ∀ acc a, domain acc → a ∈ xs → domain (step acc a))
    (same : ∀ acc a, domain acc → a ∈ xs → read (step acc a) = mapped (read acc) a)
    (acc : E) (member : domain acc) :
    domain (xs.foldl step acc) ∧ read (xs.foldl step acc) = xs.foldl mapped (read acc) := by
  induction xs generalizing acc with
  | nil => exact ⟨member, rfl⟩
  | cons a xs ih =>
    have member' := closed acc a member (by simp)
    have same' := same acc a member (by simp)
    have result := ih (fun acc b h hb => closed acc b h (by simp [hb]))
      (fun acc b h hb => same acc b h (by simp [hb])) (step acc a) member'
    exact ⟨result.1, by simpa only [List.foldl_cons, same'] using result.2⟩

private theorem scalar_read (read : E → ℝ) (domain : E → Prop)
    (closed : Transport.Closed read domain) (c : Int) :
    domain (scalar c : E) ∧ read (scalar c : E) = (c : ℝ) := by
  cases c with
  | ofNat n => exact ⟨closed.natCast n, closed.read_natCast n⟩
  | negSucc n =>
    exact ⟨closed.sub _ _ closed.zero (closed.natCast (n + 1)), by
      simp only [scalar, closed.read_sub _ _ closed.zero (closed.natCast (n + 1)),
        closed.read_zero, closed.read_natCast, Int.cast_negSucc, zero_sub]⟩

private theorem power_read (read : E → ℝ) (domain : E → Prop)
    (closed : Transport.Closed read domain) (a : E) (member : domain a) (k : Nat) :
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

private theorem monomial_read (read : E → ℝ) (domain : E → Prop)
    (closed : Transport.Closed read domain) (values : Fin n → E)
    (members : ∀ i, domain (values i)) (m : Mono n) :
    domain (Mono.prod values m) ∧ read (Mono.prod values m) = Mono.prod (read ∘ values) m := by
  have powers i := power_read read domain closed (values i) (members i) m[i]
  have result := fold read domain (List.finRange n)
    (fun acc i => acc * Mono.powBySq (values i) m[i])
    (fun acc i => acc * Mono.powBySq (read (values i)) m[i])
    (fun acc i h _ => closed.mul _ _ h (powers i).1)
    (fun acc i h _ => by rw [closed.read_mul _ _ h (powers i).1, (powers i).2])
    1 closed.one
  exact ⟨result.1, by simpa only [Mono.prod, closed.read_one, Function.comp_def] using result.2⟩

/-- The partial reader interprets this actual shared formula traversal. -/
theorem polynomial_read (read : E → ℝ) (domain : E → Prop)
    (closed : Transport.Closed read domain) (values : Fin n → E)
    (members : ∀ i, domain (values i)) (p : RealFormula.Poly n) :
    domain (polynomial values p) ∧ read (polynomial values p) = p.eval (read ∘ values) := by
  have terms (term : Mono n × Int) := closed.mul _ _ (scalar_read read domain closed term.2).1
    (monomial_read read domain closed values members term.1).1
  have result := fold read domain p.termsList _
    (fun acc term => acc + (term.2 : ℝ) * Mono.prod (read ∘ values) term.1)
    (fun acc term h _ => closed.add _ _ h (terms term))
    (fun acc term h _ => by
      rw [closed.read_add _ _ h (terms term),
        closed.read_mul _ _ (scalar_read read domain closed term.2).1
          (monomial_read read domain closed values members term.1).1,
        (scalar_read read domain closed term.2).2,
        (monomial_read read domain closed values members term.1).2])
    0 closed.zero
  refine ⟨result.1, ?_⟩
  simpa only [polynomial, RealFormula.Poly.eval, MvPoly.eval₂, MvPoly.foldTerms,
    Std.ExtTreeMap.foldl_eq_foldl_toList, MvPoly.termsList, closed.read_zero,
    Int.coe_castRingHom] using result.2

variable {registry : BaseContext.Registry} (context : Tower.Context registry)

/-- Produce every atom's sign in source order, including repeats and guards.
These are native computed signs; checking frozen evidence is a separate API. -/
@[expose] def row (values : Fin n → context.Value) (formula : RealFormula.QF n) : List Int :=
  formula.polys.map (fun p => context.sign (polynomial values p))

/-- All signs of a native shared formula have one partial ordinary reader. -/
theorem row_real (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (formula : RealFormula.QF n) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ i, domain (values i)) ∧
      row context values formula = formula.polys.map
        (fun p => (SignType.sign (p.eval (read ∘ values)) : Int)) ∧
      (∀ a r, context.origin.RealValue following a r → domain a ∧ read a = r) := by
  obtain ⟨read, domain, closed, finite, fixed⟩ := context.realize_values following
    ((List.finRange n).map values ++ formula.polys.map (polynomial values))
  have members i : domain (values i) := (finite _ (by simp)).1
  refine ⟨read, domain, closed, members, ?_, fixed⟩
  apply List.map_congr_left
  intro p hp
  have present : polynomial values p ∈
      (List.finRange n).map values ++ formula.polys.map (polynomial values) :=
    List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have observed := (finite (polynomial values p) present).2
  rw [← observed, (polynomial_read read domain closed values members p).2]

/-- A true native row gives a real witness with its inherited base coefficients.
This consumes actual native history and is not frozen-certificate checking. -/
theorem exists_real (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (original : Fin n → ℝ)
    (fixed : ∀ i, context.origin.RealValue following (values i) (original i))
    (sample : context.Value) (formula : RealFormula.QF (n + 1))
    (truth : Samples.Row.eval formula (row context (Fin.snoc values sample) formula) = some true) :
    ∃ x : ℝ, formula.toProp (RealFormula.append original x) := by
  obtain ⟨read, domain, closed, members, exactRow, real⟩ :=
    row_real context following (Fin.snoc values sample) formula
  have same : read ∘ Fin.snoc values sample = RealFormula.append original (read sample) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [RealFormula.append]
    · simp [RealFormula.append, (real _ _ (fixed j)).2]
  refine ⟨read sample, ?_⟩
  have meaning := (Samples.Row.eval_true formula _ _ exactRow).mp truth
  simpa only [same] using meaning

/-- A false point row gives a real counterexample to a universal statement.
It does not decide the existential sentence. -/
theorem not_forall (following : context.origin.base.Realization)
    (values : Fin n → context.Value) (original : Fin n → ℝ)
    (fixed : ∀ i, context.origin.RealValue following (values i) (original i))
    (sample : context.Value) (formula : RealFormula.QF (n + 1))
    (falseRow : Samples.Row.eval formula (row context (Fin.snoc values sample) formula) = some false) :
    ¬ ∀ x : ℝ, formula.toProp (RealFormula.append original x) := by
  obtain ⟨read, domain, closed, members, exactRow, real⟩ :=
    row_real context following (Fin.snoc values sample) formula
  have same : read ∘ Fin.snoc values sample = RealFormula.append original (read sample) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [RealFormula.append]
    · simp [RealFormula.append, (real _ _ (fixed j)).2]
  intro all
  have meaning : formula.toProp (read ∘ Fin.snoc values sample) := by
    simpa only [same] using all (read sample)
  have accepted := (Samples.Row.eval_true formula _ _ exactRow).mpr meaning
  rw [falseRow] at accepted
  contradiction

end Hex.RCF.RealCoefficients.NativeFormula
