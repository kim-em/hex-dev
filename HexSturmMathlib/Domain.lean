/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm
public import HexRealRootsMathlib.QueryGcd

public section

namespace HexSturmMathlib

open Hex DensePoly HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Strict extended order under interpretation of finite endpoints. -/
def EndpointLt (f : E → K) : Endpoint E → Endpoint E → Prop
  | .negInf, .finite _ | .negInf, .posInf | .finite _, .posInf => True
  | .finite a, .finite b => f a < f b
  | _, _ => False

/-- Infinite endpoints impose no evaluation condition. -/
def Nonvanishing (f : E → K) (p : Polynomial K) : Endpoint E → Prop
  | .finite a => p.eval (f a) ≠ 0
  | _ => True

/-- The exact mathematical domain of an ordered-field query. -/
def Domain (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
    (p : DensePoly E) (a b : Endpoint E) : Prop :=
  interpret f hz p ≠ 0 ∧ Squarefree (interpret f hz p) ∧ EndpointLt f a b ∧
    Nonvanishing f (interpret f hz p) a ∧ Nonvanishing f (interpret f hz p) b

variable [One E] [Add E] [Sub E] [Mul E] [Neg E] [NatCast E] [Inv E]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (sign : E → Int)
variable (hneg : ∀ a, sign a < 0 ↔ f a < 0)
variable (hzero : ∀ a, sign a = 0 ↔ f a = 0)

include hs hneg in
omit [DecidableEq K] [One E] [Neg E] [NatCast E] [Inv E] in
/-- Finite comparison signs and structural infinity order give strict
mathematical endpoint order. -/
theorem endpoint_lt (a b : Endpoint E) :
    a.lt (Sturm.adapter sign) b = true ↔ EndpointLt f a b := by
  cases a <;> cases b <;>
    simp only [Endpoint.lt, Sturm.adapter, EndpointLt, decide_eq_true_eq, hneg, hs,
      sub_lt_zero, Bool.false_eq_true]

include hz ha hm hzero in
omit [LinearOrder K] [IsStrictOrderedRing K] [One E] [Neg E] [NatCast E] [Inv E] in
/-- The field adapter's Horner nonvanishing check reflects semantic evaluation. -/
theorem endpoint_nonzero (p : DensePoly E) (a : Endpoint E) :
    a.rootFree (Sturm.adapter sign) p = true ↔ Nonvanishing f (interpret f hz p) a := by
  cases a <;>
    simp only [Endpoint.rootFree, Sturm.adapter, Nonvanishing, bne_iff_ne, ne_eq,
      hzero, eval_interpret f hz ha hm]

include hz ha hs hm hneg hzero in
omit [One E] [NatCast E] [Neg E] [Inv E] in
/-- All executable endpoint guards have their exact semantic meaning. -/
theorem guards_iff (p : DensePoly E) (a b : Endpoint E) :
    QueryReplay.endpointGuards (Sturm.adapter sign) p a b = true ↔
      interpret f hz p ≠ 0 ∧ EndpointLt f a b ∧
        Nonvanishing f (interpret f hz p) a ∧ Nonvanishing f (interpret f hz p) b := by
  have hp : (!p.isZero) = true ↔ interpret f hz p ≠ 0 := by
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    change (¬ p.isZero = true) ↔ _
    rw [DensePoly.isZero_eq_true_iff, DensePoly.size_eq_zero_iff]
    exact not_congr (interpret_eq_zero f hz p).symm
  simp only [QueryReplay.endpointGuards, Bool.and_eq_true, hp, endpoint_lt f hs sign hneg,
    endpoint_nonzero f hz ha hm sign hzero, and_assoc]

variable (h1 : f (1 : E) = 1) (hn : ∀ a, f (-a) = -f a)
variable (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hpos : ∀ a, sign a = 1 ↔ 0 < f a)

include hz hm hneg hn hi in
omit [One E] [Add E] [Sub E] [NatCast E] in
/-- Field normalization divides by a positive absolute leading coefficient,
so even a negative leading sign is retained by the actual chain entry. -/
theorem normalize_eq (p : DensePoly E) (hp : p ≠ 0) :
    0 < f (Sturm.normalize sign p).1 ∧
      Polynomial.C (f (Sturm.normalize sign p).1) *
        interpret f hz (Sturm.normalize sign p).2 = interpret f hz p := by
  have hl : f p.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_interpret f hz p]
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => hp ((interpret_eq_zero f hz p).mp h))
  have hfactor : 0 < f (if sign p.leadingCoeff < 0 then -p.leadingCoeff else p.leadingCoeff) := by
    split
    · rename_i h
      rw [hn]
      exact neg_pos.mpr ((hneg _).mp h)
    · rename_i h
      exact lt_of_le_of_ne (le_of_not_gt (fun hh => h ((hneg _).mpr hh))) (Ne.symm hl)
  refine ⟨hfactor, ?_⟩
  simp only [Sturm.normalize, interpret_scale f hz hm, hi]
  rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (ne_of_gt hfactor), Polynomial.C_1, one_mul]

include hz ha hs hm h1 hn hi hpos hneg in
/-- The field frontend uses the shared producer with positive normalization. -/
theorem chain_checks (p g : DensePoly E) (hp : p ≠ 0) :
    QueryChain.check sign p g (QueryChain.build sign (Sturm.normalize sign) p g) = true := by
  exact HexRealRootsMathlib.Query.build_checks f hz ha hs hm h1 hn sign hpos hneg
    (Sturm.normalize sign) (normalize_eq f hz hm sign hneg hn hi) p g hp

include hz ha hs hm h1 hn hi hnat hpos hneg hzero in
/-- Query failure is exactly mathematical domain failure, for arbitrary
noninjective coefficient interpretations into ordered fields. -/
theorem query_isSome (p g : DensePoly E) (a b : Endpoint E) :
    (Sturm.query sign p g a b).isSome = true ↔ Domain f hz p a b := by
  change (QueryReplay.query sign (Sturm.adapter sign) (Sturm.normalize sign) p g a b).isSome = true ↔ _
  rw [HexRealRootsMathlib.Query.query_isSome f hz ha hs hm hnat sign hpos h1
    (Sturm.adapter sign) (Sturm.normalize sign) (chain_checks f hz ha hs hm sign hneg h1 hn hi hpos),
    guards_iff f hz ha hs hm sign hneg hzero]
  simp only [Domain, and_left_comm, and_comm]

include hz ha hs hm h1 hn hi hnat hpos hneg hzero in
/-- Preparation succeeds on exactly the same mathematical domain. -/
theorem prepare_isSome (p : DensePoly E) (a b : Endpoint E) :
    (Sturm.prepare sign p a b).isSome = true ↔ Domain f hz p a b := by
  rw [Sturm.prepare_isSome sign p 1 a b]
  exact query_isSome f hz ha hs hm sign hneg hzero h1 hn hi hnat hpos p 1 a b

include hz ha hs hm h1 hn hi hnat hpos hneg hzero in
/-- Successful preparation establishes the domain and exact input bindings. -/
theorem prepare_sound (p : DensePoly E) (a b : Endpoint E) (domain : Sturm.Prepared E)
    (h : Sturm.prepare sign p a b = some domain) :
    Domain f hz p a b ∧ domain.sign = sign ∧ domain.head = p ∧
      domain.lower = a ∧ domain.upper = b := by
  refine ⟨(prepare_isSome f hz ha hs hm sign hneg hzero h1 hn hi hnat hpos p a b).mp ?_,
    Sturm.prepare_eq_some sign p a b domain h⟩
  rw [h]
  rfl

include hz ha hs hm h1 hn hi hnat hpos hneg hzero in
/-- Every opaque prepared object carries a valid domain for its bound inputs. -/
theorem prepared_domain (domain : Sturm.Prepared E) (hsign : domain.sign = sign) :
    Domain f hz domain.head domain.lower domain.upper := by
  apply (query_isSome f hz ha hs hm sign hneg hzero h1 hn hi hnat hpos
    domain.head 1 domain.lower domain.upper).mp
  rw [← hsign, Sturm.query_prepared]
  rfl

include hz ha hs hm h1 hn hi hpos hneg in
/-- Every produced certificate passes the shared literal replay. The sign
range is a law of the supplied exact coefficient sign operation. -/
theorem certify_checks (hbound : ∀ x, -1 ≤ sign x ∧ sign x ≤ 1)
    {Ctx : Type w} [DecidableEq Ctx] (context : Ctx)
    (p g : DensePoly E) (a b : Endpoint E) (cert : QueryReplay E E Ctx)
    (hcert : Sturm.certify sign context p g a b = some cert) :
    Sturm.Replay.check sign context p g a b cert.value cert = true := by
  apply QueryReplay.certify_checks sign (Sturm.adapter sign) (Sturm.normalize sign)
    (chain_checks f hz ha hs hm sign hneg h1 hn hi hpos) _ context p g a b cert hcert
  intro q e
  exact Endpoint.signAt_bounds sign (Sturm.adapter sign) hbound
    (fun q x => hbound (q.eval x)) q e

include hz ha hs hm h1 hn hi hpos hneg in
/-- Prepared certificates pass replay with their exact bound inputs and context. -/
theorem certifyPrepared_checks (hbound : ∀ x, -1 ≤ sign x ∧ sign x ≤ 1)
    {Ctx : Type w} [DecidableEq Ctx] (context : Ctx)
    (domain : Sturm.Prepared E) (hsign : domain.sign = sign) (g : DensePoly E) :
    Sturm.Replay.check sign context domain.head g domain.lower domain.upper
      (Sturm.certifyPrepared context domain g).value
      (Sturm.certifyPrepared context domain g) = true := by
  apply certify_checks f hz ha hs hm sign hneg h1 hn hi hpos hbound
    context domain.head g domain.lower domain.upper
  rw [← hsign]
  exact Sturm.certify_prepared context domain g

include hz ha hs hm h1 hnat hpos hneg hzero in
omit [Neg E] [Inv E] in
/-- Accepted replay establishes the mathematical domain from its supplied
squarefree witness, without running a gcd or query producer. -/
theorem check_domain {Ctx : Type w} [DecidableEq Ctx] (context : Ctx)
    (p g : DensePoly E) (a b : Endpoint E) (value : Int) (cert : QueryReplay E E Ctx)
    (hc : Sturm.Replay.check sign context p g a b value cert = true) : Domain f hz p a b := by
  simp only [Sturm.Replay.check, QueryReplay.check, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] at hc
  obtain ⟨_, _, _, _, _, _, hg, hsf, hconst, _⟩ := hc
  obtain ⟨hp, hab, ha', hb'⟩ := (guards_iff f hz ha hs hm sign hneg hzero p a b).mp hg
  exact ⟨hp, (HexRealRootsMathlib.Query.check_squarefree f hz ha hs hm hnat sign hpos h1
    p cert.squarefree hsf).mp hconst, hab, ha', hb'⟩

omit [IsStrictOrderedRing K] in
/-- Canonical ordered coefficients provide the exact sign laws used by the
representation-independent frontend proofs. -/
theorem orderSign_spec (x : K) :
    (Sturm.orderSign x = 1 ↔ 0 < x) ∧ (Sturm.orderSign x < 0 ↔ x < 0) ∧
      (Sturm.orderSign x = 0 ↔ x = 0) ∧ -1 ≤ Sturm.orderSign x ∧ Sturm.orderSign x ≤ 1 := by
  by_cases hn : x < 0
  · simp [Sturm.orderSign, hn, ne_of_lt hn, not_lt_of_ge (le_of_lt hn)]
  · by_cases hz : x = 0
    · simp [Sturm.orderSign, hz]
    · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [Sturm.orderSign, hn, hz, hp]

end HexSturmMathlib
