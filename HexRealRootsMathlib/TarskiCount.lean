/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.TarskiSigns
public import HexRealRootsMathlib.TarskiDomain
public import HexRealRootsMathlib.LiteralChain
public import HexRealRootsMathlib.TarskiSum

public section
namespace HexRealRootsMathlib.Tarski
open Hex Polynomial HexPolyMathlib.Interpret

/-- The open distinct-root set agrees with the legacy half-open multiset
count when roots are simple and the upper endpoint is not a root. -/
theorem rootsIn_card (p : Polynomial ℝ) (I : DyadicInterval)
    (hsf : Squarefree p) (hb : p.eval (Dyadic.toReal I.upper) ≠ 0) :
    (rootsIn p (.finite (Dyadic.toReal I.lower)) (.finite (Dyadic.toReal I.upper))).card =
      (Literal.rootsIn p I).card := by
  classical
  have he : rootsIn p (.finite (Dyadic.toReal I.lower)) (.finite (Dyadic.toReal I.upper)) =
      (Literal.rootsIn p I).toFinset := by
    ext x
    simp only [mem_rootsIn, Multiset.mem_toFinset, Literal.rootsIn,
      Multiset.mem_filter, inInterval_finite, Literal.InInterval]
    constructor
    · rintro ⟨hx, ha, hupper⟩
      exact ⟨hx, ha, hupper.le⟩
    · rintro ⟨hx, ha, hxle⟩
      refine ⟨hx, ha, lt_of_le_of_ne hxle ?_⟩
      intro he
      exact hb (he ▸ (Polynomial.isRoot_of_mem_roots hx).eq_zero)
  rw [he, Multiset.toFinset_card_of_nodup]
  exact (Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hsf)).filter _

private theorem replay_list (a b : Polynomial ℝ) (rest : List (Polynomial ℝ))
    (hlast : IsUnit ((a :: b :: rest).getD ((a :: b :: rest).length - 1) 0))
    (hstep : ∀ i, i + 2 < (a :: b :: rest).length →
      Sturm.ReplayStep ((a :: b :: rest).getD i 0) ((a :: b :: rest).getD (i + 1) 0)
        ((a :: b :: rest).getD (i + 2) 0)) : Sturm.Replay a b rest := by
  induction rest generalizing a b with
  | nil => exact Sturm.Replay.pair (by simpa using hlast)
  | cons c rest ih =>
    apply Sturm.Replay.cons
    · simpa using hstep 0 (by simp)
    · apply ih b c
      · simpa only [List.length_cons, Nat.add_sub_cancel, List.getD_cons_succ] using hlast
      · intro i hi
        simpa only [List.getD_cons_succ, Nat.add_assoc] using hstep (i + 1) (by simpa using hi)

private theorem cast_unit (p : ZPoly) (h : p.size = 1) : IsUnit (toPolyℝ p) := by
  have hp : toPolyℝ p ≠ 0 := by
    intro hp
    have := toPolyℝ_eq_zero_iff.mp hp
    subst p
    simp at h
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hp,
    natDegree_toPolyℝ, DensePoly.natDegree_eq_size_sub_one, h]
  rfl

/-- The supplied positive recurrence of a checked integer derivative chain
is a literal real Sturm replay when its last entry is constant. -/
private theorem integer_replay (p : ZPoly) (cert : SignedRemainderChain Int)
    (h : SignedRemainderChain.check Int.sign p 1 cert = true)
    (hlast : SignedRemainderChain.lastIsConstant cert = true)
    (hn : cert.chain.size ≠ 1) :
    ∃ a b rest, cert.chain.toList.map toPolyℝ = a :: b :: rest ∧ Sturm.Replay a b rest := by
  have hbound := check_bound (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero) Int.sign p 1 cert h
  have hlen : 2 ≤ (cert.chain.toList.map toPolyℝ).length := by simpa using (show 2 ≤ cert.chain.size by omega)
  have hunit : IsUnit ((cert.chain.toList.map toPolyℝ).getD
      ((cert.chain.toList.map toPolyℝ).length - 1) 0) := by
    have hz : toPolyℝ (0 : ZPoly) = 0 := toPolyℝ_zero
    have he (i : Nat) : (cert.chain.toList.map toPolyℝ).getD i 0 = toPolyℝ (cert.chain.getD i 0) := by
      rw [← hz, List.getD_map]
      simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
    rw [List.length_map, Array.length_toList, he]
    apply cast_unit
    simpa only [SignedRemainderChain.lastIsConstant, beq_iff_eq] using hlast
  have hstep : ∀ i, i + 2 < (cert.chain.toList.map toPolyℝ).length →
      Sturm.ReplayStep ((cert.chain.toList.map toPolyℝ).getD i 0)
        ((cert.chain.toList.map toPolyℝ).getD (i + 1) 0)
        ((cert.chain.toList.map toPolyℝ).getD (i + 2) 0) := by
    intro i hi
    have ht := (check_tail Int.sign p 1 cert h hn).1
    have hs := check_step (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
      Int.cast_add Int.cast_sub Int.cast_mul Int.sign
      (fun z => Int.sign_eq_one_iff_pos.trans Int.cast_pos.symm) p 1 cert h hn i (by
        simp only [List.length_map, Array.length_toList] at hi
        omega)
    refine ⟨_, interpret (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
      (cert.steps.getD i ⟨0, 0, 0⟩).quotient, _, hs.1, hs.2.1, ?_⟩
    have he (i : Nat) : (cert.chain.toList.map toPolyℝ).getD i 0 =
        interpret (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero) (cert.chain.getD i 0) := by
      rw [interpret_int_real, ← toPolyℝ_zero, List.getD_map]
      simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
    simpa only [he] using hs.2.2
  generalize he : cert.chain.toList.map toPolyℝ = l at hlen hunit hstep ⊢
  cases l with
  | nil => simp at hlen
  | cons a l => cases l with
    | nil => simp at hlen
    | cons b rest => exact ⟨a, b, rest, rfl, replay_list a b rest hunit hstep⟩


/-- A checked derivative chain over the integers satisfies the existing real
Sturm-chain axioms. The initial quotient disappears by strict derivative degree. -/
theorem integer_sturmChain (p : ZPoly) (cert : SignedRemainderChain Int)
    (h : SignedRemainderChain.check Int.sign p 1 cert = true)
    (hlast : SignedRemainderChain.lastIsConstant cert = true)
    (hn : cert.chain.size ≠ 1) :
    Sturm.IsSturmChain (toPolyℝ p) (cert.chain.toList.map toPolyℝ) := by
  obtain ⟨a, b, rest, he, hrep⟩ := integer_replay p cert h hlast hn
  have hentry (i : Nat) : (cert.chain.toList.map toPolyℝ).getD i 0 = toPolyℝ (cert.chain.getD i 0) := by
    rw [← toPolyℝ_zero, List.getD_map]
    simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  have ha : a = toPolyℝ p := by
    have hh := hentry 0
    rw [he, check_head Int.sign p 1 cert h] at hh
    simpa using hh
  subst a
  have hp : toPolyℝ p ≠ 0 := by
    intro hp
    have hz := toPolyℝ_eq_zero_iff.mp hp
    subst p
    simp only [SignedRemainderChain.check, show (0 : ZPoly).isZero = true from rfl,
      Bool.not_true, Bool.false_and, Bool.false_eq_true] at h
  obtain ⟨c, hc, hsecond⟩ := check_initial_rem (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
    Int.cast_add Int.cast_sub Int.cast_mul (fun n => Int.cast_natCast n) Int.sign
    (fun z => Int.sign_eq_one_iff_pos.trans Int.cast_pos.symm) p 1 cert h
  rw [interpret_one _ _ Int.cast_one, one_mul, interpret_int_real, interpret_int_real,
    (Polynomial.mod_eq_self_iff hp).mpr (Polynomial.degree_derivative_lt hp)] at hsecond
  have hb : b = C c * (toPolyℝ p).derivative := by
    rw [← hentry 1, he] at hsecond
    simpa using hsecond
  have hderiv : (toPolyℝ p).derivative = C c⁻¹ * b := by
    rw [hb, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (ne_of_gt hc), C_1, one_mul]
  have hnz : ∀ q ∈ toPolyℝ p :: b :: rest, q ≠ 0 := by
    intro q hq
    rw [← he, List.mem_map] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [← interpret_int_real]
    exact check_nonzero (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
      Int.sign p 1 cert h z (by simpa using hz)
  rw [he]
  exact Sturm.isChain_of_replay hrep hnz c⁻¹ (inv_pos.mpr hc) hderiv


private theorem integer_squarefree (p : ZPoly) (cert : SignedRemainderChain Int)
    (h : SignedRemainderChain.check Int.sign p 1 cert = true) :
    SignedRemainderChain.lastIsConstant cert = true ↔ Squarefree (toPolyℝ p) := by
  simpa only [interpret_int_real] using check_squarefree
    (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
    Int.cast_add Int.cast_sub Int.cast_mul (fun n => Int.cast_natCast n) Int.sign
    (fun z => Int.sign_eq_one_iff_pos.trans Int.cast_pos.symm) Int.cast_one p cert h

/-- Accepted integer certificates for query `1` count the roots in the real
half-open interval, using the existing derivative Sturm theorem. Endpoint
guards also exclude the upper root, so this is the specified open count. -/
theorem integer_check_count {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p : ZPoly) (I : DyadicInterval) (value : Int) (cert : TarskiCertificate Int Dyadic Ctx)
    (h : TarskiCertificate.check Int.sign EndpointSigns.intDyadic context p 1
      (.finite I.lower) (.finite I.upper) value cert = true) :
    value = (Literal.rootsIn (toPolyℝ p) I).card := by
  have hv := (check_value Int.sign EndpointSigns.intDyadic context p 1
    (.finite I.lower) (.finite I.upper) value cert h).2
  have hh := h
  simp only [TarskiCertificate.check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hh
  obtain ⟨_, _, _, _, _, _, _, hsf, hlast, hr, _⟩ := hh
  have hsq := (integer_squarefree p cert.squarefree hsf).mp hlast
  have ht := (integer_squarefree p cert.remainders hr).mpr hsq
  by_cases hn : cert.remainders.chain.size = 1
  · have hp : p.size = 1 := by
      simpa only [SignedRemainderChain.lastIsConstant, hn, Nat.sub_self,
        check_head Int.sign p 1 cert.remainders hr, beq_iff_eq] using ht
    have hpC : toPolyℝ p = C ((toPolyℝ p).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (by
        rw [natDegree_toPolyℝ, DensePoly.natDegree_eq_size_sub_one, hp])
    rw [check_singleton Int.sign EndpointSigns.intDyadic context p 1
      (.finite I.lower) (.finite I.upper) value cert h hn, hpC]
    simp only [Literal.rootsIn, Polynomial.roots_C, Multiset.filter_zero, Multiset.card_zero, Nat.cast_zero]
  · have hc := integer_sturmChain p cert.remainders hr ht hn
    have hcount := literalCount_eq_card_roots p cert.remainders.chain hsq hc I
    simpa only [TarskiCertificate.signs, Hex.Array.map'_eq_map, Array.toList_map,
      Endpoint.signAt, EndpointSigns.intDyadic, sturmVarAt] using hv.trans hcount

/-- Accepted query-one certificates realize the open-interval root sum. -/
theorem integer_check_rootSum {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p : ZPoly) (I : DyadicInterval) (value : Int) (cert : TarskiCertificate Int Dyadic Ctx)
    (h : TarskiCertificate.check Int.sign EndpointSigns.intDyadic context p 1
      (.finite I.lower) (.finite I.upper) value cert = true) :
    value = rootSum (toPolyℝ p) 1 (.finite (Dyadic.toReal I.lower))
      (.finite (Dyadic.toReal I.upper)) := by
  have hh := h
  simp only [TarskiCertificate.check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hh
  obtain ⟨_, _, _, _, _, _, hend, hsf, hlast, _⟩ := hh
  have hs := (integer_squarefree p cert.squarefree hsf).mp hlast
  have hb := ((integer_checkEndpoints p I).mp hend).2.2
  rw [rootSum_one, rootsIn_card _ I hs hb]
  exact integer_check_count context p I value cert h

/-- The effective integer/dyadic query of `1` has the existing real root-count semantics. -/
theorem integer_query_count (p : ZPoly) (I : DyadicInterval) (value : Int)
    (h : ZPoly.tarskiQuery p 1 I = some value) :
    value = (Literal.rootsIn (toPolyℝ p) I).card := by
  have hc : ∃ cert, IntTarskiCertificate.certify p 1 I = some cert ∧ cert.value = value := by
    exact Option.map_eq_some_iff.mp h
  obtain ⟨cert, hc, hv⟩ := hc
  have hh := (integer_certify_checks p 1 I cert hc).1
  have he := integer_check_count () p I cert.value cert hh
  simpa only [hv] using he

/-- The supported query-one result uses the same open finite-root sum as the
abstract Sturm–Tarski interface. -/
theorem integer_query_rootSum (p : ZPoly) (I : DyadicInterval) (value : Int)
    (h : ZPoly.tarskiQuery p 1 I = some value) :
    value = rootSum (toPolyℝ p) 1 (.finite (Dyadic.toReal I.lower))
      (.finite (Dyadic.toReal I.upper)) := by
  have hd := (integer_domain p 1 I).mp (by simp only [h, Option.isSome_some])
  rw [rootSum_one, rootsIn_card _ I hd.2.1 hd.2.2.2]
  exact integer_query_count p I value h

/-- The effective integer/dyadic query of `1` is nonnegative. -/
theorem integer_query_nonneg (p : ZPoly) (I : DyadicInterval) (value : Int)
    (h : ZPoly.tarskiQuery p 1 I = some value) : 0 ≤ value := by
  rw [integer_query_count p I value h]
  exact Int.natCast_nonneg _


/-- A checked integer derivative certificate on the whole line counts all
real roots, using the existing real derivative-Sturm theorem. -/
theorem integer_check_total {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p : ZPoly) (value : Int) (cert : TarskiCertificate Int Dyadic Ctx)
    (h : TarskiCertificate.check Int.sign EndpointSigns.intDyadic context p 1
      .negInf .posInf value cert = true) : value = (toPolyℝ p).roots.card := by
  have hv := (check_value Int.sign EndpointSigns.intDyadic context p 1
    .negInf .posInf value cert h).2
  have hh := h
  simp only [TarskiCertificate.check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hh
  obtain ⟨_, _, _, _, _, _, _, hsf, hlast, hr, _⟩ := hh
  have hsq := (integer_squarefree p cert.squarefree hsf).mp hlast
  have ht := (integer_squarefree p cert.remainders hr).mpr hsq
  by_cases hn : cert.remainders.chain.size = 1
  · have hp : p.size = 1 := by
      simpa only [SignedRemainderChain.lastIsConstant, hn, Nat.sub_self,
        check_head Int.sign p 1 cert.remainders hr, beq_iff_eq] using ht
    have hpC : toPolyℝ p = C ((toPolyℝ p).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (by
        rw [natDegree_toPolyℝ, DensePoly.natDegree_eq_size_sub_one, hp])
    rw [check_singleton Int.sign EndpointSigns.intDyadic context p 1
      .negInf .posInf value cert h hn, hpC]
    simp only [Polynomial.roots_C, Multiset.card_zero, Nat.cast_zero]
  · have hc := integer_sturmChain p cert.remainders hr ht hn
    have hcount := literalRootCount_eq_card_roots p cert.remainders.chain hsq hc
    simpa only [TarskiCertificate.signs, Hex.Array.map'_eq_map, Array.toList_map,
      Endpoint.signAt, EndpointSigns.intDyadic, sturmVarNegInf, sturmVarPosInf] using hv.trans hcount

end HexRealRootsMathlib.Tarski
