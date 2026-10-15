/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFnTheory.Convergence
public import HexOrderedFnTheory.Evaluation

public section

/-!
Universal progress of sign and approximation searches from containment, shrinking
widths and relative transcendence, yielding erased accessibility proofs.
-/

namespace Hex.OrderedFn.Real

open Oracle HexPolyTheory Filter Topology
universe u
variable {K : Type u} [Field K] [DecidableEq K]
variable {ι : K →+* ℝ} {τ : ℝ} {a : Approximation K}

/-- Every nonzero polynomial's bounds eventually determine its sign. -/
theorem enclose_sign_eventually (ha : ApproximationCorrect ι τ a)
    (hw : ApproximationWidth a) (ht : RelativeTranscendence ι τ)
    (p : DensePoly K) (hp : p ≠ 0) :
    ∀ᶠ n in atTop, (enclose a p (precision n)).sign?.isSome = true := by
  apply Contains.sign_eventually (fun n => enclose_sound ha p _ (precision_pos n))
    (horner_converges ha hw p)
  apply ht
  intro he
  exact hp (equiv.injective (he.trans toPolynomial_zero.symm))

/-- Total-sign refinement eventually succeeds. Relative transcendence is over
all coefficients in the predecessor field, with the same embedding and providers. -/
theorem attempt_progress (ha : ApproximationCorrect ι τ a)
    (hw : ApproximationWidth a) (ht : RelativeTranscendence ι τ) (f : RationalFn K) :
    ∃ N, ∀ n ≥ N, (attempt a f n).isSome = true := by
  apply eventually_atTop.mp
  by_cases hz : f.num = 0
  · exact Eventually.of_forall (fun n => by simp [attempt, hz])
  · filter_upwards [enclose_sign_eventually ha hw ht f.num hz,
      enclose_sign_eventually ha hw ht f.den f.den_ne_zero] with n hn hd
    unfold attempt
    rw [ite_eq_right hz]
    cases he₁ : (enclose a f.num (precision n)).sign? <;>
      cases he₂ : (enclose a f.den (precision n)).sign? <;> simp_all

/-- Approximation refinement eventually attains every positive requested width. -/
theorem approx_progress (ha : ApproximationCorrect ι τ a)
    (hw : ApproximationWidth a) (ht : RelativeTranscendence ι τ)
    (f : RationalFn K) (δ : Rat) (hδ : 0 < δ) :
    ∃ N, ∀ n ≥ N, (approxAttempt a f δ n).isSome = true := by
  apply eventually_atTop.mp
  by_cases hz : f.num = 0
  · exact Eventually.of_forall (fun n => by simp [approxAttempt, hz, le_of_lt hδ])
  · have hq := Contains.quotient_converges
      (fun n => enclose_sound ha f.num _ (precision_pos n))
      (fun n => enclose_sound ha f.den _ (precision_pos n))
      (horner_converges ha hw f.num) (horner_converges ha hw f.den)
      (eval_den_ne_zero ht f)
    have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
    filter_upwards [enclose_sign_eventually ha hw ht f.den f.den_ne_zero,
      (tendsto_order.mp hq).2 (δ : ℝ) hδ'] with n hd hn
    have hsep : (enclose a f.den (precision n)).separated = true := by
      unfold Bounds.sign? at hd
      split at hd
      · simp [Bounds.separated, *]
      · split at hd
        · simp [Bounds.separated, *]
        · contradiction
    have hn' : (Bounds.hull4
        ((enclose a f.num (precision n)).lower / (enclose a f.den (precision n)).lower)
        ((enclose a f.num (precision n)).lower / (enclose a f.den (precision n)).upper)
        ((enclose a f.num (precision n)).upper / (enclose a f.den (precision n)).lower)
        ((enclose a f.num (precision n)).upper / (enclose a f.den (precision n)).upper)).width ≤ δ := by
      exact_mod_cast hn.le
    simp [approxAttempt, hz, Bounds.div?, hsep, hn']

/-- Accessibility for the derived approximation search, including coarse
nonpositive requests, follows from the same provider hypotheses. -/
theorem approx_acc (ha : ApproximationCorrect ι τ a) (hw : ApproximationWidth a)
    (ht : RelativeTranscendence ι τ) (f : RationalFn K) (δ : Rat) (n : Nat) :
    Acc (Next (approxAttempt a f (requestWidth δ))) n :=
  next_acc _ (approx_progress ha hw ht f _ (requestWidth_pos δ)) n

/-- Accessibility is derived semantically; executing `sign` still performs each
refinement until its first successful trial. -/
theorem sign_acc (ha : ApproximationCorrect ι τ a) (hw : ApproximationWidth a)
    (ht : RelativeTranscendence ι τ) (f : RationalFn K) (n : Nat) :
    Acc (Next (attempt a f)) n := next_acc _ (attempt_progress ha hw ht f) n

/-- The proof-founded total search agrees with the injective real evaluation. -/
theorem sign_eq (ha : ApproximationCorrect ι τ a) (ht : RelativeTranscendence ι τ)
    (f : RationalFn K) (h : Acc (Next (attempt a f)) 0) :
    sign a f h = sgn (evalHom ht f) := by
  rw [evalHom_apply]
  exact sign_sound ha f h

/-- Relative transcendence makes formal zero exactly the zero total sign. -/
theorem sign_eq_zero_iff (ha : ApproximationCorrect ι τ a) (ht : RelativeTranscendence ι τ)
    (f : RationalFn K) (h : Acc (Next (attempt a f)) 0) : sign a f h = 0 ↔ f = 0 := by
  rw [sign_eq ha ht]
  have hz : sgn (evalHom ht f) = 0 ↔ evalHom ht f = 0 := by
    rcases lt_trichotomy (evalHom ht f) 0 with h | h | h
    · simp [sgn, h, h.ne]
    · simp [sgn, h]
    · simp [sgn, h, h.ne']
  rw [hz, ← map_zero (evalHom ht), (evalHom ht).injective.eq_iff]

end Hex.OrderedFn.Real
