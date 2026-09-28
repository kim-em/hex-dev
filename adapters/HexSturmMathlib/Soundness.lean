/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Domain
public import HexRealRootsMathlib.TarskiSoundness

public section

namespace HexSturmMathlib

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib

/-- The canonical executable sign is the mathematical three-valued sign. -/
theorem orderSign_eq {K : Type*} [Zero K] [DecidableEq K] [LinearOrder K] (x : K) :
    Sturm.orderSign x = (SignType.sign x : Int) := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [Sturm.orderSign, _root_.sign_neg h, h]
  · simp [Sturm.orderSign, h]
  · simp [Sturm.orderSign, _root_.sign_pos h, ne_of_gt h, not_lt_of_ge h.le]

variable {E : Type u} {R : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [Field R] [DecidableEq R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable (f : E → R) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : R))
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include hsign in
omit [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
    [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem sign_spec (x : E) :
    (sign x = 1 ↔ 0 < f x) ∧ (sign x < 0 ↔ f x < 0) ∧
    (sign x = 0 ↔ f x = 0) ∧ -1 ≤ sign x ∧ sign x ≤ 1 := by
  rcases lt_trichotomy (f x) 0 with h | h | h
  · simp [hsign, _root_.sign_neg h, h, ne_of_lt h, not_lt_of_ge h.le]
  · simp [hsign, h]
  · simp [hsign, _root_.sign_pos h, h, ne_of_gt h, not_lt_of_ge h.le]

include h1 ha hs hm hnat hsign in
/-- Arbitrary accepted field certificates establish both their domain and
their mathematical query value through the shared replay theorem. -/
theorem check_sound {Ctx : Type w} [DecidableEq Ctx] (context : Ctx)
    (p q : DensePoly E) (a b : Endpoint E) (value : Int)
    (certificate : TarskiCertificate E E Ctx)
    (checked : Sturm.check sign context p q a b value certificate = true) :
    Domain f hz p a b ∧
      value = Tarski.rootSum (interpret f hz p) (interpret f hz q) (a.map f) (b.map f) := by
  have hsg := sign_spec f sign hsign
  refine ⟨check_domain f hz ha hs hm sign (fun x => (hsg x).2.1)
    (fun x => (hsg x).2.2.1) h1 hnat (fun x => (hsg x).1)
    context p q a b value certificate checked, ?_⟩
  apply Tarski.check_rootSum f hz h1 ha hs hm hnat sign hsign f
    (EndpointSigns.ofSign sign) _ _ context p q a b value certificate checked
  · intro x y
    simp only [EndpointSigns.ofSign, hsign, hs]
  · intro p x
    simp only [EndpointSigns.ofSign, hsign, eval_interpret f hz ha hm]

variable [Neg E] [Inv E]
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include h1 ha hs hm hnat hsign hn hi in
/-- Prepared querying has root-sum semantics without repeating preparation. -/
theorem queryPrepared_sound (domain : Sturm.PreparedDomain E)
    (binding : domain.sign = sign) (q : DensePoly E) :
    Sturm.queryPrepared domain q =
      Tarski.rootSum (interpret f hz domain.head) (interpret f hz q)
        (domain.lower.map f) (domain.upper.map f) := by
  have hsg := sign_spec f sign hsign
  have checked := certifyPrepared_checks f hz ha hs hm sign
    (fun x => (hsg x).2.1) h1 hn hi (fun x => (hsg x).1)
    (fun x => (hsg x).2.2.2) () domain binding q
  exact (check_sound f hz h1 ha hs hm hnat sign hsign () _ _ _ _ _ _ checked).2

include h1 ha hs hm hnat hsign hn hi in
/-- A successful ordinary query has the same meaning as prepared querying. -/
theorem query_sound (p q : DensePoly E) (a b : Endpoint E) (value : Int)
    (result : Sturm.query sign p q a b = some value) :
    value = Tarski.rootSum (interpret f hz p) (interpret f hz q) (a.map f) (b.map f) := by
  have hv : (Sturm.certify sign () p q a b).map TarskiCertificate.value = some value := by
    rw [Sturm.certify_value, result]
  obtain ⟨certificate, produced, hvalue⟩ := Option.map_eq_some_iff.mp hv
  have hsg := sign_spec f sign hsign
  have checked := certify_checks f hz ha hs hm sign
    (fun x => (hsg x).2.1) h1 hn hi (fun x => (hsg x).1)
    (fun x => (hsg x).2.2.2) () p q a b certificate produced
  rw [← hvalue]
  exact (check_sound f hz h1 ha hs hm hnat sign hsign () _ _ _ _ _ _ checked).2

include h1 ha hs hm hnat hsign hn hi in
/-- A successful query of one is exactly the number of distinct interval roots. -/
theorem query_count (p : DensePoly E) (a b : Endpoint E) (value : Int)
    (result : Sturm.query sign p 1 a b = some value) :
    value = (Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).card := by
  simpa only [interpret_one f hz h1, Tarski.rootSum_one] using
    query_sound f hz h1 ha hs hm hnat sign hsign hn hi p 1 a b value result

include hz h1 ha hs hm hnat hsign hn hi in
/-- Actual query-one answers are nonnegative; this justifies conversion to natural counts. -/
theorem query_nonneg (p : DensePoly E) (a b : Endpoint E) (value : Int)
    (result : Sturm.query sign p 1 a b = some value) : 0 ≤ value := by
  rw [query_count f hz h1 ha hs hm hnat sign hsign hn hi p a b value result]
  exact Int.natCast_nonneg _

include h1 ha hs hm hnat hsign hn hi in
/-- A successful query is bounded by the number of distinct interval roots and the head degree. -/
theorem query_bound (p q : DensePoly E) (a b : Endpoint E) (value : Int)
    (result : Sturm.query sign p q a b = some value) :
    |value| ≤ (Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).card ∧
      (Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).card ≤ p.natDegree := by
  rw [query_sound f hz h1 ha hs hm hnat sign hsign hn hi p q a b value result]
  exact ⟨Tarski.abs_rootSum_le _ _ _ _, by
    simpa only [natDegree_interpret] using Tarski.rootsIn_card_le (interpret f hz p) (a.map f) (b.map f)⟩

include h1 ha hs hm hnat hsign hn hi in
/-- On an interval containing exactly one root, a query returns the sign at that root. -/
theorem query_sign (p q : DensePoly E) (a b : Endpoint E) (value : Int) (x : R)
    (result : Sturm.query sign p q a b = some value)
    (single : Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f) = {x}) :
    value = (SignType.sign ((interpret f hz q).eval x) : Int) := by
  rw [query_sound f hz h1 ha hs hm hnat sign hsign hn hi p q a b value result]
  exact Tarski.rootSum_singleton _ _ _ _ x single

include h1 ha hs hm hnat hsign hn hi in
/-- Successful natural counts are exactly the cardinality of the semantic root set. -/
theorem rootCount_eq (p : DensePoly E) (a b : Endpoint E) (n : Nat)
    (result : Sturm.rootCount sign p a b = some n) :
    n = (Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).card := by
  obtain ⟨value, hvalue, rfl⟩ := Option.map_eq_some_iff.mp result
  rw [query_count f hz h1 ha hs hm hnat sign hsign hn hi p a b value hvalue]
  exact Int.toNat_natCast _

include h1 ha hs hm hnat hsign hn hi in
omit [IsRealClosed R] in
/-- Natural counting succeeds exactly on the existing query domain. -/
theorem rootCount_isSome (p : DensePoly E) (a b : Endpoint E) :
    (Sturm.rootCount sign p a b).isSome = true ↔ Domain f hz p a b := by
  have hsg := sign_spec f sign hsign
  simpa only [Sturm.rootCount, Option.isSome_map] using
    query_isSome f hz ha hs hm sign (fun x => (hsg x).2.1)
      (fun x => (hsg x).2.2.1) h1 hn hi hnat (fun x => (hsg x).1) p 1 a b

include hz h1 ha hs hm hnat hsign hn hi in
/-- A successful query-one answer is preserved exactly by natural-count conversion. -/
theorem rootCount_query (p : DensePoly E) (a b : Endpoint E) (value : Int)
    (result : Sturm.query sign p 1 a b = some value) :
    ∃ n, Sturm.rootCount sign p a b = some n ∧ (n : Int) = value := by
  refine ⟨value.toNat, ?_, Int.toNat_of_nonneg ?_⟩
  · simp only [Sturm.rootCount, result, Option.map_some]
  · exact query_nonneg f hz h1 ha hs hm hnat sign hsign hn hi p a b value result

include hz h1 ha hs hm hnat hsign hn hi in
/-- Casting natural counts back to integers preserves the whole query result. -/
theorem rootCount_map (p : DensePoly E) (a b : Endpoint E) :
    (Sturm.rootCount sign p a b).map (fun n => (n : Int)) = Sturm.query sign p 1 a b := by
  cases result : Sturm.query sign p 1 a b with
  | none => simp [Sturm.rootCount, result]
  | some value =>
    simp only [Sturm.rootCount, result, Option.map_some]
    exact congrArg some (Int.toNat_of_nonneg
      (query_nonneg f hz h1 ha hs hm hnat sign hsign hn hi p a b value result))

end HexSturmMathlib
