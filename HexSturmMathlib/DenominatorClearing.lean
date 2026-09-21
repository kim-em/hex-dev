/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Rational

public section

namespace HexSturmMathlib.DenominatorClearing

open Hex HexPolyMathlib Polynomial
open HexRealRootsMathlib (toPolyℝ toPolyℝ_eq_zero_iff toReal_eq_cast_toRat)

/-- Clear a literal three-term identity when its three polynomial entries
are scaled by `a`, `b`, and `c`. All new scalar factors are integers; no
division or chain production is performed on the translated evidence. -/
def step (a b c : Nat) (s : RemainderStep Rat) : RemainderStep Int where
  leftScale := (b * c * s.rightScale.den * (ZPoly.clearDenominators s.quotient).1 : Nat) * s.leftScale.num
  quotient := DensePoly.scale (a * c * s.leftScale.den * s.rightScale.den : Nat)
    (ZPoly.clearDenominators s.quotient).2
  rightScale := (a * b * s.leftScale.den * (ZPoly.clearDenominators s.quotient).1 : Nat) * s.rightScale.num

/-- Clear every polynomial and scale in a supplied literal chain. Initial
product scaling includes both the head and query clearing factors. The terminal
identity is translated from its supplied quotient, without running division. -/
def chain (p : DensePoly Rat) (queryScale : Nat) (cert : SignedRemainderChain Rat) : SignedRemainderChain Int :=
  let entries := Hex.Array.map' (fun q => (ZPoly.clearDenominators q).2) cert.chain
  let factor i := (ZPoly.clearDenominators (cert.chain.getD i 0)).1
  { chain := entries
    degrees := Hex.Array.map' DensePoly.natDegree entries
    initial := step ((ZPoly.clearDenominators p).1 * queryScale)
      (ZPoly.clearDenominators p).1 (factor 1) cert.initial
    steps := Hex.Array.ofFn' fun i : Fin cert.steps.size =>
      step (factor i.val) (factor (i.val + 1)) (factor (i.val + 2)) cert.steps[i]
    terminal := cert.terminal.map fun (l, q) =>
      let s := step (factor (cert.chain.size - 2)) (factor (cert.chain.size - 1)) 1 ⟨l, q, 1⟩
      (s.leftScale, s.quotient) }

/-- Translate both supplied chains and renew exact endpoint signs and literal
input bindings. The caller supplies the dyadic interval represented by the
original rational endpoints; the full literal context is retained. -/
@[expose] def certificate {Ctx : Type u} (p g : DensePoly Rat) (I : DyadicInterval)
    (cert : TarskiCertificate Rat Rat Ctx) : TarskiCertificate Int Dyadic Ctx :=
  TarskiCertificate.fromChains Int.sign EndpointSigns.intDyadic cert.context
    (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 (.finite I.lower) (.finite I.upper)
    (chain p 1 cert.squarefree) (chain p (ZPoly.clearDenominators g).1 cert.remainders)

theorem step_pos (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (s : RemainderStep Rat) (hl : 0 < s.leftScale) (hr : 0 < s.rightScale) :
    0 < (step a b c s).leftScale ∧ 0 < (step a b c s).rightScale := by
  have hln := Rat.num_pos.mpr hl
  have hrn := Rat.num_pos.mpr hr
  have hld := s.leftScale.den_pos
  have hrd := s.rightScale.den_pos
  have hq := ZPoly.clearDenominators_pos s.quotient
  dsimp only [step]
  constructor <;> positivity

private theorem cast_num (q : Rat) : (q.num : Rat) = q * q.den := by
  have h := div_mul_cancel₀ (q.num : Rat) (by exact_mod_cast q.den_nz : (q.den : Rat) ≠ 0)
  rw [q.num_div_den] at h
  exact h.symm

/-- The three translated coefficients multiply their corresponding scaled
entries by one common positive denominator product. -/
theorem step_spec (a b c : Nat) (s : RemainderStep Rat) :
    let k : Rat := (a * b * c * s.leftScale.den * s.rightScale.den *
      (ZPoly.clearDenominators s.quotient).1 : Nat)
    ((step a b c s).leftScale : Rat) * a = k * s.leftScale ∧
      HexPolyZMathlib.toPolyℚ (step a b c s).quotient * C (b : Rat) =
        C k * toPolynomial s.quotient ∧
      ((step a b c s).rightScale : Rat) * c = k * s.rightScale := by
  dsimp only
  constructor
  · simp only [step, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, cast_num]
    ring
  constructor
  · rw [step, ← HexPolyZMathlib.toPolynomial_toRatPoly, ZPoly.toRatPoly_scale_int,
      toPolynomial_scale, ZPoly.toRatPoly_clearDenominators, toPolynomial_scale]
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring
  · simp only [step, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, cast_num]
    ring

private theorem clear_size (p : DensePoly Rat) :
    (ZPoly.clearDenominators p).2.size = p.size := by
  rw [← ZPoly.size_toRatPoly, ZPoly.toRatPoly_clearDenominators]
  exact DensePoly.size_scale_field (by exact_mod_cast ne_of_gt (ZPoly.clearDenominators_pos p)) p

private theorem clear_zero : (ZPoly.clearDenominators (0 : DensePoly Rat)).2 = 0 := by
  apply (DensePoly.size_eq_zero_iff _).mp
  rw [clear_size]
  rfl

private theorem chain_entry (p : DensePoly Rat) (g : Nat) (cert : SignedRemainderChain Rat) (i : Nat) :
    (chain p g cert).chain.getD i 0 = (ZPoly.clearDenominators (cert.chain.getD i 0)).2 := by
  by_cases hi : i < cert.chain.size
  · have hi' : i < (chain p g cert).chain.size := by
      simpa only [chain, Hex.Array.size_map'] using hi
    rw [← Array.getElem_eq_getD (h := hi') 0, ← Array.getElem_eq_getD (h := hi) 0]
    simp only [chain, Hex.Array.getElem_map']
  · have hi' : ¬ i < (chain p g cert).chain.size := by
      simpa only [chain, Hex.Array.size_map'] using hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact clear_zero.symm

private theorem step_terms (a b c : Nat) (s : RemainderStep Rat)
    (p q r p' q' r' : Polynomial Rat)
    (hp : p' = C (a : Rat) * p) (hq : q' = C (b : Rat) * q) (hr : r' = C (c : Rat) * r) :
    let k : Rat := (a * b * c * s.leftScale.den * s.rightScale.den *
      (ZPoly.clearDenominators s.quotient).1 : Nat)
    C ((step a b c s).leftScale : Rat) * p' = C k * (C s.leftScale * p) ∧
      HexPolyZMathlib.toPolyℚ (step a b c s).quotient * q' = C k * (toPolynomial s.quotient * q) ∧
      C ((step a b c s).rightScale : Rat) * r' = C k * (C s.rightScale * r) := by
  obtain ⟨hl, hm, hs⟩ := step_spec a b c s
  dsimp only at hl hm hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hp, ← mul_assoc, ← C_mul, hl, C_mul, mul_assoc]
  · rw [hq, ← mul_assoc, hm, mul_assoc]
  · rw [hr, ← mul_assoc, ← C_mul, hs, C_mul, mul_assoc]

private theorem step_add (a b c : Nat) (s : RemainderStep Rat)
    (p q r p' q' r' : Polynomial Rat)
    (hp : p' = C (a : Rat) * p) (hq : q' = C (b : Rat) * q) (hr : r' = C (c : Rat) * r)
    (h : C s.leftScale * p = toPolynomial s.quotient * q + C s.rightScale * r) :
    C ((step a b c s).leftScale : Rat) * p' =
      HexPolyZMathlib.toPolyℚ (step a b c s).quotient * q' +
        C ((step a b c s).rightScale : Rat) * r' := by
  obtain ⟨hl, hm, hs⟩ := step_terms a b c s p q r p' q' r' hp hq hr
  rw [hl, hm, hs, h, mul_add]

private theorem step_sub (a b c : Nat) (s : RemainderStep Rat)
    (p q r p' q' r' : Polynomial Rat)
    (hp : p' = C (a : Rat) * p) (hq : q' = C (b : Rat) * q) (hr : r' = C (c : Rat) * r)
    (h : C s.leftScale * p = toPolynomial s.quotient * q - C s.rightScale * r) :
    C ((step a b c s).leftScale : Rat) * p' =
      HexPolyZMathlib.toPolyℚ (step a b c s).quotient * q' -
        C ((step a b c s).rightScale : Rat) * r' := by
  obtain ⟨hl, hm, hs⟩ := step_terms a b c s p q r p' q' r' hp hq hr
  rw [hl, hm, hs, h, mul_sub]

private theorem rat_interpret (p : DensePoly Rat) :
    Interpret.interpret id (fun _ => Iff.rfl) p = toPolynomial p := by
  ext i
  simp only [Interpret.coeff_interpret, coeff_toPolynomial, id_eq]

private theorem int_interpret (p : ZPoly) :
    Interpret.interpret (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero) p =
      HexPolyZMathlib.toPolyℚ p := by
  ext i
  simp only [Interpret.coeff_interpret, HexPolyZMathlib.toPolyℚ, Polynomial.coeff_map,
    coeff_toPolynomial, Int.coe_castRingHom]

private theorem step_checks (p q r : DensePoly Rat) (s : RemainderStep Rat)
    (h : SignedRemainderChain.checkStep Sturm.orderSign p q r s = true) :
    SignedRemainderChain.checkStep Int.sign (ZPoly.clearDenominators p).2
      (ZPoly.clearDenominators q).2 (ZPoly.clearDenominators r).2
      (step (ZPoly.clearDenominators p).1 (ZPoly.clearDenominators q).1
        (ZPoly.clearDenominators r).1 s) = true := by
  have hh := (HexRealRootsMathlib.Tarski.step_iff id (fun _ => Iff.rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) Sturm.orderSign
    (fun x => (orderSign_spec x).1) p q r s).mp h
  simp only [id_eq, rat_interpret] at hh
  apply (HexRealRootsMathlib.Tarski.step_iff (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero)
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b)
    Int.sign (fun x => Int.sign_eq_one_iff_pos.trans Int.cast_pos.symm) _ _ _ _).mpr
  have hpos := step_pos _ _ _ (ZPoly.clearDenominators_pos p) (ZPoly.clearDenominators_pos q)
    (ZPoly.clearDenominators_pos r) s hh.1 hh.2.1
  refine ⟨by exact_mod_cast hpos.1, by exact_mod_cast hpos.2, ?_⟩
  simp only [int_interpret]
  exact step_sub _ _ _ s (toPolynomial p) (toPolynomial q) (toPolynomial r) _ _ _
    (HexPolyZMathlib.toPolynomial_clearDenominators p)
    (HexPolyZMathlib.toPolynomial_clearDenominators q)
    (HexPolyZMathlib.toPolynomial_clearDenominators r) hh.2.2

private theorem subIsZero_int (p q : ZPoly) :
    SignedRemainderChain.subIsZero p q = true ↔ HexPolyZMathlib.toPolyℚ p = HexPolyZMathlib.toPolyℚ q := by
  simpa only [SignedRemainderChain.subIsZero, int_interpret] using
    Interpret.sub_isZero (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero)
      (fun a b => Int.cast_sub a b) p q

private theorem initial_checks (p g : DensePoly Rat) (g' : ZPoly) (d : Nat) (hd : 0 < d)
    (hclear : HexPolyZMathlib.toPolyℚ g' = C (d : Rat) * toPolynomial g) (cert : SignedRemainderChain Rat)
    (h : SignedRemainderChain.check Sturm.orderSign p g cert = true) :
    Int.sign (chain p d cert).initial.leftScale = 1 ∧
      Int.sign (chain p d cert).initial.rightScale = 1 ∧
      SignedRemainderChain.subIsZero
        (DensePoly.scale (chain p d cert).initial.leftScale
          (g' * (ZPoly.clearDenominators p).2.derivative))
        ((chain p d cert).initial.quotient * (ZPoly.clearDenominators p).2 +
          DensePoly.scale (chain p d cert).initial.rightScale ((chain p d cert).chain.getD 1 0)) = true := by
  have hh := HexRealRootsMathlib.Tarski.check_initial id (fun _ => Iff.rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    Sturm.orderSign (fun x => (orderSign_spec x).1) p g cert h
  simp only [id_eq, rat_interpret] at hh
  have hp := ZPoly.clearDenominators_pos p
  have hr := ZPoly.clearDenominators_pos (cert.chain.getD 1 0)
  have hpos := step_pos _ _ _ (Nat.mul_pos hp hd) hp hr cert.initial hh.1 hh.2.1
  refine ⟨Int.sign_eq_one_iff_pos.mpr hpos.1, Int.sign_eq_one_iff_pos.mpr hpos.2, ?_⟩
  rw [subIsZero_int, chain_entry]
  have hprod : HexPolyZMathlib.toPolyℚ
      (g' * (ZPoly.clearDenominators p).2.derivative) =
      C (((ZPoly.clearDenominators p).1 * d : Nat) : Rat) *
        (toPolynomial g * (toPolynomial p).derivative) := by
    simp only [HexPolyZMathlib.toPolyℚ, HexPolyZMathlib.toPolynomial] at hclear
    simp only [HexPolyZMathlib.toPolyℚ, toPolynomial_mul, toPolynomial_derivative,
      Polynomial.map_mul, ← Polynomial.derivative_map]
    rw [hclear, HexPolyZMathlib.toPolynomial_clearDenominators,
      Polynomial.derivative_C_mul]
    simp only [Nat.cast_mul, C_mul]
    ring
  have he := step_add _ _ _ cert.initial (toPolynomial g * (toPolynomial p).derivative)
    (toPolynomial p) (toPolynomial (cert.chain.getD 1 0)) _ _ _ hprod
    (HexPolyZMathlib.toPolynomial_clearDenominators p)
    (HexPolyZMathlib.toPolynomial_clearDenominators (cert.chain.getD 1 0)) hh.2.2
  simpa only [chain, HexPolyZMathlib.toPolyℚ, toPolynomial_scale, toPolynomial_mul,
    toPolynomial_add, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Int.coe_castRingHom]
      using he

private theorem terminal_checks (p q a : DensePoly Rat) (u : Rat) (hu : 0 < u)
    (h : C u * toPolynomial p = toPolynomial a * toPolynomial q) :
    let s := step (ZPoly.clearDenominators p).1 (ZPoly.clearDenominators q).1 1 ⟨u, a, 1⟩
    Int.sign s.leftScale = 1 ∧ SignedRemainderChain.subIsZero
      (DensePoly.scale s.leftScale (ZPoly.clearDenominators p).2)
      (s.quotient * (ZPoly.clearDenominators q).2) = true := by
  have hp := ZPoly.clearDenominators_pos p
  have hq := ZPoly.clearDenominators_pos q
  have hpos := step_pos _ _ 1 hp hq (by omega) ⟨u, a, 1⟩ hu (by norm_num)
  refine ⟨Int.sign_eq_one_iff_pos.mpr hpos.1, ?_⟩
  rw [subIsZero_int]
  have he := step_add _ _ 1 ⟨u, a, 1⟩ (toPolynomial p) (toPolynomial q) 0
    (HexPolyZMathlib.toPolyℚ (ZPoly.clearDenominators p).2)
    (HexPolyZMathlib.toPolyℚ (ZPoly.clearDenominators q).2) 0
    (HexPolyZMathlib.toPolynomial_clearDenominators p)
    (HexPolyZMathlib.toPolynomial_clearDenominators q) (by simp) (by simpa using h)
  simpa only [mul_zero, add_zero, HexPolyZMathlib.toPolyℚ, toPolynomial_scale,
    toPolynomial_mul, Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom] using he

/-- Clearing the supplied chain preserves acceptance by the actual integer
checker, including singleton chains and nonconstant terminal entries. -/
theorem chain_checks (p g : DensePoly Rat) (g' : ZPoly) (d : Nat) (hd : 0 < d)
    (hclear : HexPolyZMathlib.toPolyℚ g' = C (d : Rat) * toPolynomial g) (cert : SignedRemainderChain Rat)
    (h : SignedRemainderChain.check Sturm.orderSign p g cert = true) :
    SignedRemainderChain.check Int.sign (ZPoly.clearDenominators p).2
      g' (chain p d cert) = true := by
  have hi := initial_checks p g g' d hd hclear cert h
  have hsize : (chain p d cert).chain.size = cert.chain.size := by
    simp only [chain, Hex.Array.size_map']
  have hsrc := h
  simp only [SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hsrc
  obtain ⟨hp, hn, hb, hh, _, hnz, hd, _, _, _, ht⟩ := hsrc
  simp only [SignedRemainderChain.check, hsize, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨?_, hn, ?_, ?_, rfl, ?_, ?_, hi.1, hi.2.1, hi.2.2, ?_⟩
  · simpa only [Bool.not_eq_true', DensePoly.isZero_eq_false_iff, clear_size] using hp
  · simpa only [clear_size] using hb
  · simp only [chain, Hex.Array.map'_eq_map, Array.getElem?_map, hh, Option.map_some]
  · rw [← hsize]
    apply Array.all_eq_true_iff_forall_mem.mpr
    intro q hq
    simp only [chain, Hex.Array.map'_eq_map, Array.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    simpa only [Bool.not_eq_true', DensePoly.isZero_eq_false_iff, clear_size] using
      Array.all_eq_true_iff_forall_mem.mp hnz r hr
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro i hi
    simpa only [chain_entry, clear_size] using Array.all_eq_true_iff_forall_mem.mp hd i hi
  · by_cases hs : cert.chain.size = 1
    · simp only [hs, ↓reduceIte, Bool.and_eq_true] at ht ⊢
      constructor
      · simpa only [chain, Array.isEmpty, Hex.Array.size_ofFn'] using ht.1
      · simpa only [chain, Option.isNone_map] using ht.2
    · simp only [hs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at ht ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [chain, Hex.Array.size_ofFn'] using ht.1
      · apply Array.all_eq_true_iff_forall_mem.mpr
        intro i hi
        have hidx : i < cert.steps.size := by
          simpa only [chain, Hex.Array.size_ofFn'] using Array.mem_range.mp hi
        have hh := Array.all_eq_true_iff_forall_mem.mp ht.2.1 i (Array.mem_range.mpr hidx)
        have hnew := step_checks (cert.chain.getD i 0) (cert.chain.getD (i + 1) 0)
          (cert.chain.getD (i + 2) 0) (cert.steps.getD i ⟨0, 0, 0⟩) hh
        rw [chain_entry, chain_entry, chain_entry]
        have hi' : i < (chain p d cert).steps.size := by simpa only [chain, Hex.Array.size_ofFn'] using hidx
        rw [← Array.getElem_eq_getD (h := hi') ⟨0, 0, 0⟩]
        simpa only [chain, Hex.Array.getElem_ofFn', Fin.getElem_fin,
          ← Array.getElem_eq_getD (h := hidx) ⟨0, 0, 0⟩]
          using hnew
      · cases he : cert.terminal with
        | none => simp only [he, Bool.false_eq_true] at ht; exact ht.2.2.elim
        | some pair =>
          obtain ⟨u, q⟩ := pair
          have hh := HexRealRootsMathlib.Tarski.check_terminal id (fun _ => Iff.rfl)
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) Sturm.orderSign
            (fun x => (orderSign_spec x).1) p g cert h hs u q he
          simp only [id_eq, rat_interpret] at hh
          have hterm := terminal_checks (cert.chain.getD (cert.chain.size - 2) 0)
            (cert.chain.getD (cert.chain.size - 1) 0) q u hh.1 hh.2
          simpa only [chain, he, Option.map_some, Bool.and_eq_true, decide_eq_true_eq,
            ← chain_entry p d cert] using hterm

private theorem guards (p : DensePoly Rat) (I : DyadicInterval)
    (h : TarskiCertificate.checkEndpoints (EndpointSigns.ofSign Sturm.orderSign) p
      (.finite I.lower.toRat) (.finite I.upper.toRat) = true) :
    TarskiCertificate.checkEndpoints EndpointSigns.intDyadic (ZPoly.clearDenominators p).2
      (.finite I.lower) (.finite I.upper) = true := by
  obtain ⟨hp, _, ha, hb⟩ := (checkEndpoints_iff (fun z : Rat => (z : ℝ)) (fun _ => Rat.cast_eq_zero)
    (fun a b => Rat.cast_add a b) (fun a b => Rat.cast_sub a b) (fun a b => Rat.cast_mul a b)
    Sturm.orderSign (fun z => (orderSign_spec z).2.1.trans Rat.cast_lt_zero.symm)
    (fun z => (orderSign_spec z).2.2.1.trans Rat.cast_eq_zero.symm)
    p (.finite I.lower.toRat) (.finite I.upper.toRat)).mp h
  have hc : ((ZPoly.clearDenominators p).1 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (ZPoly.clearDenominators_pos p)
  apply (HexRealRootsMathlib.Tarski.integer_checkEndpoints _ I).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hp' : toPolyℝ (ZPoly.clearDenominators p).2 ≠ 0 := by
      rw [toPolyℝ_clearDenominators]
      exact mul_ne_zero (C_ne_zero.mpr hc) hp
    exact hp' (toPolyℝ_eq_zero_iff.mpr hz)
  · rw [toPolyℝ_clearDenominators, Polynomial.eval_mul, Polynomial.eval_C, toReal_eq_cast_toRat]
    exact mul_ne_zero hc ha
  · rw [toPolyℝ_clearDenominators, Polynomial.eval_mul, Polynomial.eval_C, toReal_eq_cast_toRat]
    exact mul_ne_zero hc hb

private theorem lastIsConstant_eq (p : DensePoly Rat) (d : Nat) (cert : SignedRemainderChain Rat) :
    SignedRemainderChain.lastIsConstant (chain p d cert) = SignedRemainderChain.lastIsConstant cert := by
  simp only [SignedRemainderChain.lastIsConstant, show (chain p d cert).chain.size = cert.chain.size by
    simp only [chain, Hex.Array.size_map'], chain_entry, clear_size]

/-- Clearing a supplied chain preserves all its finite dyadic endpoint signs. -/
theorem signs_eq (p : DensePoly Rat) (d : Nat) (cert : SignedRemainderChain Rat) (x : Dyadic) :
    TarskiCertificate.signs Sturm.orderSign (EndpointSigns.ofSign Sturm.orderSign) cert.chain
        (.finite x.toRat) =
      TarskiCertificate.signs Int.sign EndpointSigns.intDyadic (chain p d cert).chain (.finite x) := by
  apply signs_rat_eq
  · simp only [chain, Hex.Array.size_map']
  · intro i
    refine ⟨((ZPoly.clearDenominators (cert.chain.getD i 0)).1 : ℝ), ?_, ?_⟩
    · exact_mod_cast ZPoly.clearDenominators_pos (cert.chain.getD i 0)
    · rw [chain_entry, HexRealRootsMathlib.Tarski.interpret_int_real, toPolyℝ_clearDenominators]

/-- Translating an accepted rational certificate preserves its exact value,
literal context, and acceptance by the integer/dyadic checker. -/
theorem certificate_checks {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p g : DensePoly Rat) (I : DyadicInterval) (value : Int) (cert : TarskiCertificate Rat Rat Ctx)
    (h : Sturm.check Sturm.orderSign context p g (.finite I.lower.toRat) (.finite I.upper.toRat)
      value cert = true) :
    TarskiCertificate.check Int.sign EndpointSigns.intDyadic context
      (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2
      (.finite I.lower) (.finite I.upper) value (certificate p g I cert) = true := by
  have hv := (HexRealRootsMathlib.Tarski.check_value Sturm.orderSign
    (EndpointSigns.ofSign Sturm.orderSign) context p g
    (.finite I.lower.toRat) (.finite I.upper.toRat) value cert h).2
  simp only [Sturm.check, TarskiCertificate.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hctx, _, _, _, _, _, hg, hsf, hc, hr, _⟩ := h
  have hsf' := chain_checks p 1 (1 : ZPoly) 1 (by decide) (by simp [HexPolyZMathlib.toPolyℚ]) cert.squarefree hsf
  have hr' := chain_checks p g (ZPoly.clearDenominators g).2 (ZPoly.clearDenominators g).1
    (ZPoly.clearDenominators_pos g) (by
      rw [← HexPolyZMathlib.toPolynomial_toRatPoly, ZPoly.toRatPoly_clearDenominators,
        toPolynomial_scale]) cert.remainders hr
  have hv' : value = (certificate p g I cert).value := by
    simpa only [certificate, TarskiCertificate.fromChains, signs_eq p (ZPoly.clearDenominators g).1]
      using hv
  simp only [certificate, TarskiCertificate.check, TarskiCertificate.fromChains, hctx, hv',
    guards p I hg, hsf', hr', lastIsConstant_eq, hc, decide_true,
    TarskiCertificate.signs_bounded Int.sign EndpointSigns.intDyadic HexRealRootsMathlib.Tarski.integer_signs,
    Bool.and_true]

end HexSturmMathlib.DenominatorClearing
