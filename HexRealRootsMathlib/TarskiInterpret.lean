/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski
public import HexRealRoots.TarskiProofs
public import HexPolyMathlib.Pseudo

public section

/-! Algebraic interpretation of the actual shared query producer and replay.
These results supply the signed identities and degree bounds. Root-sum
semantics additionally require the signed-remainder/Cauchy-index theorem. -/
namespace HexRealRootsMathlib.Tarski

open Hex DensePoly HexPolyMathlib.Interpret

universe u v
variable {D : Type u} {K : Type v} [Zero D] [DecidableEq D]
variable [Field K] [DecidableEq K]
variable (f : D → K) (hz : ∀ a, f a = 0 ↔ a = 0)

variable [One D] [Add D] [Sub D] [Mul D]
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)

include ha hs hm in
omit [One D] in
/-- The actual replay step tests positive scales and a semantic zero difference. -/
theorem step_iff [LinearOrder K] [IsStrictOrderedRing K] (sign : D → Int)
    (hsign : ∀ a, sign a = 1 ↔ 0 < f a) (a b c : DensePoly D) (s : RemainderStep D) :
    SignedRemainderChain.checkStep sign a b c s = true ↔
      0 < f s.leftScale ∧ 0 < f s.rightScale ∧
      Polynomial.C (f s.leftScale) * interpret f hz a =
        interpret f hz s.quotient * interpret f hz b -
          Polynomial.C (f s.rightScale) * interpret f hz c := by
  simp only [SignedRemainderChain.checkStep, SignedRemainderChain.subIsZero, Bool.and_eq_true, decide_eq_true_eq,
    sub_isZero f hz hs, interpret_sub f hz hs, interpret_mul f hz ha hm,
    interpret_scale f hz hm, hsign, and_assoc]

include hs in
omit [One D] [Add D] [Mul D] in
/-- A nonzero scalar normalization preserves stored size, also after the
negative sign required by the signed-remainder recurrence. -/
theorem normalize_bounds (normalize : DensePoly D → D × DensePoly D)
    (hnormalize : ∀ r : DensePoly D, r ≠ 0 →
      f (normalize r).1 ≠ 0 ∧
      Polynomial.C (f (normalize r).1) * interpret f hz (normalize r).2 = interpret f hz r)
    (r : DensePoly D) (hr : r ≠ 0) :
    (normalize r).2 ≠ 0 ∧ (normalize r).2.size = r.size ∧
      -(normalize r).2 ≠ 0 ∧ (-(normalize r).2).size = r.size := by
  obtain ⟨hc, heq⟩ := hnormalize r hr
  have hq : (normalize r).2 ≠ 0 := by
    intro hq
    apply hr
    apply (interpret_eq_zero f hz r).mp
    rw [← heq, hq, interpret_zero, mul_zero]
  have hneg : -(normalize r).2 ≠ 0 := by
    intro hneg
    have hh := congrArg (interpret f hz) hneg
    rw [interpret_neg f hz hs, interpret_zero, neg_eq_zero] at hh
    exact hq ((interpret_eq_zero f hz _).mp hh)
  have hdeg := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_C_mul hc] at hdeg
  simp only [natDegree_interpret, natDegree_eq_size_sub_one] at hdeg
  have hn : (interpret f hz (-(normalize r).2)).natDegree =
      (interpret f hz (normalize r).2).natDegree := by
    rw [interpret_neg f hz hs, Polynomial.natDegree_neg]
  simp only [natDegree_interpret, natDegree_eq_size_sub_one] at hn
  have hr' := Nat.pos_of_ne_zero (fun h => hr ((size_eq_zero_iff r).mp h))
  have hq' := Nat.pos_of_ne_zero (fun h => hq ((size_eq_zero_iff _).mp h))
  have hn' := Nat.pos_of_ne_zero (fun h => hneg ((size_eq_zero_iff _).mp h))
  exact ⟨hq, by omega, hneg, by omega⟩

include ha hs hm in
omit [One D] in
/-- Accepted replay supplies the positive initial product reduction. This is
an algebraic identity, not yet the Sturm–Tarski root-sum theorem. -/
theorem check_initial [NatCast D] [LinearOrder K] [IsStrictOrderedRing K]
    (hn : ∀ n : Nat, f (n : D) = (n : K)) (sign : D → Int)
    (hsign : ∀ a, sign a = 1 ↔ 0 < f a)
    (p g : DensePoly D) (cert : SignedRemainderChain D) (h : SignedRemainderChain.check sign p g cert = true) :
    0 < f cert.initial.leftScale ∧ 0 < f cert.initial.rightScale ∧
      Polynomial.C (f cert.initial.leftScale) *
        (interpret f hz g * (interpret f hz p).derivative) =
      interpret f hz cert.initial.quotient * interpret f hz p +
        Polynomial.C (f cert.initial.rightScale) * interpret f hz (cert.chain.getD 1 0) := by
  simp only [SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, _, hl, hr, hi, _⟩ := h
  refine ⟨(hsign _).mp hl, (hsign _).mp hr, ?_⟩
  have hi' := (sub_isZero f hz hs _ _).mp hi
  simpa only [interpret_scale f hz hm, interpret_mul f hz ha hm, interpret_add f hz ha,
    interpret_derivative f hz hn hm] using hi'

include ha hs hm in
omit [One D] in
/-- Every accepted finite triple has the positive signed recurrence under
interpretation. The checker reads the supplied quotient; it does not divide. -/
theorem check_step [NatCast D] [LinearOrder K] [IsStrictOrderedRing K]
    (sign : D → Int) (hsign : ∀ a, sign a = 1 ↔ 0 < f a)
    (p g : DensePoly D) (cert : SignedRemainderChain D) (h : SignedRemainderChain.check sign p g cert = true)
    (hn : cert.chain.size ≠ 1) (i : Nat) (hi : i < cert.steps.size) :
    0 < f (cert.steps.getD i ⟨0, 0, 0⟩).leftScale ∧
    0 < f (cert.steps.getD i ⟨0, 0, 0⟩).rightScale ∧
      Polynomial.C (f (cert.steps.getD i ⟨0, 0, 0⟩).leftScale) *
          interpret f hz (cert.chain.getD i 0) =
        interpret f hz (cert.steps.getD i ⟨0, 0, 0⟩).quotient *
          interpret f hz (cert.chain.getD (i + 1) 0) -
        Polynomial.C (f (cert.steps.getD i ⟨0, 0, 0⟩).rightScale) *
          interpret f hz (cert.chain.getD (i + 2) 0) := by
  simp only [SignedRemainderChain.check, hn, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsteps, _⟩ := h
  have hstep := (Array.all_eq_true_iff_forall_mem.mp hsteps) i (Array.mem_range.mpr hi)
  exact (step_iff f hz ha hs hm sign hsign _ _ _ _).mp hstep

include ha hs hm in
omit [One D] in
/-- Terminal replay is an exact zero-remainder identity with positive scale;
the last polynomial is allowed to be nonconstant. -/
theorem check_terminal [NatCast D] [LinearOrder K] [IsStrictOrderedRing K]
    (sign : D → Int) (hsign : ∀ a, sign a = 1 ↔ 0 < f a)
    (p g : DensePoly D) (cert : SignedRemainderChain D) (h : SignedRemainderChain.check sign p g cert = true)
    (hn : cert.chain.size ≠ 1) (u : D) (q : DensePoly D)
    (ht : cert.terminal = some (u, q)) :
    0 < f u ∧ Polynomial.C (f u) * interpret f hz (cert.chain.getD (cert.chain.size - 2) 0) =
      interpret f hz q * interpret f hz (cert.chain.getD (cert.chain.size - 1) 0) := by
  simp only [SignedRemainderChain.check, hn, ↓reduceIte, ht, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hu, heq⟩ := h
  refine ⟨(hsign _).mp hu, ?_⟩
  have hh := (sub_isZero f hz hs _ _).mp heq
  simpa only [interpret_scale f hz hm, interpret_mul f hz ha hm] using hh

omit [One D] in
/-- Replay's literal size guard supplies the mathematical chain bound. -/
theorem check_bound [NatCast D] (sign : D → Int)
    (p g : DensePoly D) (cert : SignedRemainderChain D) (h : SignedRemainderChain.check sign p g cert = true) :
    0 < cert.chain.size ∧ cert.chain.size ≤ (interpret f hz p).natDegree + 1 := by
  simp only [SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, hn, hb, _⟩ := h
  rw [natDegree_interpret, natDegree_eq_size_sub_one]
  exact ⟨hn, by omega⟩

omit [One D] in
/-- Every supplied entry of an accepted replay is semantically nonzero. -/
theorem check_nonzero [NatCast D] (sign : D → Int)
    (p g : DensePoly D) (cert : SignedRemainderChain D) (h : SignedRemainderChain.check sign p g cert = true)
    (r : DensePoly D) (hr : r ∈ cert.chain) : interpret f hz r ≠ 0 := by
  simp only [SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, _, hentries, _⟩ := h
  have he := (Array.all_eq_true_iff_forall_mem.mp hentries) r hr
  change (!r.isZero) = true at he
  intro hz'
  have hr0 := (interpret_eq_zero f hz r).mp hz'
  rw [hr0] at he
  contradiction

include hs in
/-- The actual producer reaches its terminal identity after every nonzero
initial remainder. The only normalization premise is a nonzero scalar identity. -/
theorem build_complete [Neg D] [NatCast D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D)
    (hnormalize : ∀ r : DensePoly D, r ≠ 0 →
      f (normalize r).1 ≠ 0 ∧
      Polynomial.C (f (normalize r).1) * interpret f hz (normalize r).2 = interpret f hz r)
    (p g : DensePoly D) (hp : p ≠ 0)
    (hr : (positivePseudoDiv sign (g * p.derivative) p).remainder.isZero = false) :
    (SignedRemainderChain.build sign normalize p g).terminal.isSome = true := by
  apply SignedRemainderChain.build_terminal sign normalize _ _ p g hp hr
  · intro r hr
    have h := normalize_bounds f hz hs normalize hnormalize r hr
    exact ⟨h.1, Nat.le_of_eq h.2.1⟩
  · intro r hr
    have h := normalize_bounds f hz hs normalize hnormalize r hr
    exact ⟨h.2.2.1, Nat.le_of_eq h.2.2.2⟩

include hs in
/-- The producer's array satisfies the replay length bound under interpretation. -/
theorem build_bound [Neg D] [NatCast D] (sign : D → Int)
    (normalize : DensePoly D → D × DensePoly D)
    (hnormalize : ∀ r : DensePoly D, r ≠ 0 →
      f (normalize r).1 ≠ 0 ∧
      Polynomial.C (f (normalize r).1) * interpret f hz (normalize r).2 = interpret f hz r)
    (p g : DensePoly D) (hp : p ≠ 0) :
    (SignedRemainderChain.build sign normalize p g).chain.size ≤ p.size := by
  apply SignedRemainderChain.build_size sign normalize _ _ p g hp
  · intro r hr
    have h := normalize_bounds f hz hs normalize hnormalize r hr
    exact ⟨h.1, Nat.le_of_eq h.2.1⟩
  · intro r hr
    have h := normalize_bounds f hz hs normalize hnormalize r hr
    exact ⟨h.2.2.1, Nat.le_of_eq h.2.2.2⟩

section Production
variable [Neg D] [LinearOrder K] [IsStrictOrderedRing K]
variable (h1 : f (1 : D) = 1) (hn : ∀ a, f (-a) = -f a)
variable (sign : D → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)
variable (hneg : ∀ a, sign a < 0 ↔ f a < 0)
variable (normalize : DensePoly D → D × DensePoly D)
variable (hnormalize : ∀ r : DensePoly D, r ≠ 0 →
  0 < f (normalize r).1 ∧
  Polynomial.C (f (normalize r).1) * interpret f hz (normalize r).2 = interpret f hz r)
include hz ha hs hm h1 hn hpos hneg hnormalize

/-- The producer's actual sign-corrected remainder and normalization satisfy
the positive three-term replay check. -/
theorem step_produced (a b : DensePoly D) (hb : b ≠ 0)
    (hr : (positivePseudoDiv sign a b).remainder.isZero = false) :
    SignedRemainderChain.checkStep sign a b (-(normalize (positivePseudoDiv sign a b).remainder).2)
      ⟨(positivePseudoDiv sign a b).multiplier, (positivePseudoDiv sign a b).quotient,
        (normalize (positivePseudoDiv sign a b).remainder).1⟩ = true := by
  have hrne : (positivePseudoDiv sign a b).remainder ≠ 0 := by
    intro hzero
    rw [hzero] at hr
    contradiction
  obtain ⟨hc, hnorm⟩ := hnormalize _ hrne
  apply (step_iff f hz ha hs hm sign hpos _ _ _ _).mpr
  refine ⟨positive_multiplier f hz h1 ha hs hm hn sign hneg a b hb, hc, ?_⟩
  simp only [interpret_neg f hz hs, mul_neg, sub_neg_eq_add, hnorm]
  exact positive_reconstruct f hz h1 ha hs hm hn sign a b

omit hnormalize in
/-- A zero final remainder produces the positive terminal identity checked by
replay, independently of whether the last nonzero polynomial is constant. -/
theorem terminal_produced (a b : DensePoly D) (hb : b ≠ 0)
    (hr : (positivePseudoDiv sign a b).remainder.isZero = true) :
    sign (positivePseudoDiv sign a b).multiplier = 1 ∧
      SignedRemainderChain.subIsZero (scale (positivePseudoDiv sign a b).multiplier a)
        ((positivePseudoDiv sign a b).quotient * b) = true := by
  refine ⟨(hpos _).mpr (positive_multiplier f hz h1 ha hs hm hn sign hneg a b hb), ?_⟩
  have hrzero : (positivePseudoDiv sign a b).remainder = 0 :=
    (size_eq_zero_iff _).mp ((isZero_eq_true_iff _).mp hr)
  apply (sub_isZero f hz hs _ _).mpr
  simp only [interpret_scale f hz hm, interpret_mul f hz ha hm]
  simpa only [hrzero, interpret_zero, _root_.add_zero] using
    positive_reconstruct f hz h1 ha hs hm hn sign a b

/-- Every chain produced from a nonzero head passes literal replay. The proof
follows the array loop and discharges its backend laws through interpretation;
no field structure is imposed on stored representatives. -/
theorem build_checks [NatCast D] (p g : DensePoly D) (hp : p ≠ 0) :
    SignedRemainderChain.check sign p g (SignedRemainderChain.build sign normalize p g) = true := by
  have hnorm' : ∀ r : DensePoly D, r ≠ 0 →
      f (normalize r).1 ≠ 0 ∧
      Polynomial.C (f (normalize r).1) * interpret f hz (normalize r).2 = interpret f hz r := by
    intro r hr
    exact ⟨ne_of_gt (hnormalize r hr).1, (hnormalize r hr).2⟩
  have hnext : ∀ r : DensePoly D, r ≠ 0 →
      -(normalize r).2 ≠ 0 ∧ (-(normalize r).2).size ≤ r.size := by
    intro r hr
    have h := normalize_bounds f hz hs normalize hnorm' r hr
    exact ⟨h.2.2.1, Nat.le_of_eq h.2.2.2⟩
  have hleft := (hpos _).mpr (positive_multiplier f hz h1 ha hs hm hn sign hneg
    (g * p.derivative) p hp)
  have hrec := positive_reconstruct f hz h1 ha hs hm hn sign (g * p.derivative) p
  simp only [SignedRemainderChain.build]
  split
  · rename_i hr
    have hrzero : (positivePseudoDiv sign (g * p.derivative) p).remainder = 0 :=
      (size_eq_zero_iff _).mp ((isZero_eq_true_iff _).mp hr)
    apply SignedRemainderChain.singleton_checks sign p g _ hp hleft ((hpos _).mpr (by rw [h1]; exact zero_lt_one))
    apply (sub_isZero f hz hs _ _).mpr
    simp only [interpret_scale f hz hm, interpret_add f hz ha, interpret_mul f hz ha hm,
      interpret_zero, mul_zero, _root_.add_zero]
    simpa only [hrzero, interpret_zero, _root_.add_zero, interpret_mul f hz ha hm] using hrec
  · rename_i hr
    have hrne : (positivePseudoDiv sign (g * p.derivative) p).remainder ≠ 0 := by
      intro hzero
      rw [hzero] at hr
      exact hr rfl
    have hb := normalize_bounds f hz hs normalize hnorm' _ hrne
    obtain ⟨hc, hnorm⟩ := hnormalize _ hrne
    have hd := positivePseudoDiv_remainder_lt sign (g * p.derivative) p hp
    have hi : SignedRemainderChain.subIsZero
        (scale (positivePseudoDiv sign (g * p.derivative) p).multiplier (g * p.derivative))
        ((positivePseudoDiv sign (g * p.derivative) p).quotient * p +
          scale (normalize (positivePseudoDiv sign (g * p.derivative) p).remainder).1
            (normalize (positivePseudoDiv sign (g * p.derivative) p).remainder).2) = true := by
      apply (sub_isZero f hz hs _ _).mpr
      simp only [interpret_scale f hz hm, interpret_add f hz ha, interpret_mul f hz ha hm, hnorm]
      simpa only [interpret_mul f hz ha hm] using hrec
    have hpref := SignedRemainderChain.Prefix.pair sign p g
      (normalize (positivePseudoDiv sign (g * p.derivative) p).remainder).2
      ⟨(positivePseudoDiv sign (g * p.derivative) p).multiplier,
        (positivePseudoDiv sign (g * p.derivative) p).quotient,
        (normalize (positivePseudoDiv sign (g * p.derivative) p).remainder).1⟩ hp hb.1
      (by omega) hleft ((hpos _).mpr hc) hi
    refine SignedRemainderChain.buildAux_checks sign normalize hnext
      (step_produced f hz ha hs hm h1 hn sign hpos hneg normalize hnormalize)
      (terminal_produced f hz ha hs hm h1 hn sign hpos hneg)
      p g _ hp p.natDegree p _ #[p, _] #[] hpref rfl rfl hb.1 ?_ ?_
    · rw [natDegree_eq_size_sub_one]
      omega
    · change 2 + _ - 1 ≤ p.size
      omega

end Production
end HexRealRootsMathlib.Tarski
