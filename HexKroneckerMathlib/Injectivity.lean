/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Height
public import HexKroneckerMathlib.Radix
public import HexMatrix.Certificate

public section

namespace Hex.Kronecker

open scoped BigOperators

noncomputable section

/-- Every supported exponent vector belongs to the common degree box. -/
@[expose] def InBox {k : Nat} (ds : List Nat) (p : MvPolynomial (Fin k) Int) : Prop :=
  ∀ e ∈ p.support, List.Forall₂ (· ≤ ·) (List.ofFn fun i => e i) ds

/-- One balanced digit after flattening the exponent box in mixed-radix order. -/
@[expose] def digit {k : Nat} (ss : List Nat) (p : MvPolynomial (Fin k) Int) (n : Nat) : Int :=
  ∑ e ∈ p.support, if code ss (List.ofFn fun i => e i) = n then p.coeff e else 0

/-- The dense list is a semantic object; the kernel checker never constructs it. -/
@[expose] def digits {k : Nat} (ds : List Nat) (p : MvPolynomial (Fin k) Int) : List Int :=
  List.ofFn (fun i : Fin (boxSize ds) => digit (makeStrides 1 ds) p i.val)

theorem digit_bound {k : Nat} (ss : List Nat) (p : MvPolynomial (Fin k) Int) (n : Nat) :
    (digit ss p n).natAbs ≤ norm₁ p := by
  classical
  unfold digit norm₁
  apply (Int.natAbs_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> simp

theorem digit_coeff {k : Nat} (ds : List Nat) (p : MvPolynomial (Fin k) Int)
    (hp : InBox ds p) (e : Fin k →₀ Nat)
    (he : List.Forall₂ (· ≤ ·) (List.ofFn fun i => e i) ds) :
    digit (makeStrides 1 ds) p (code (makeStrides 1 ds) (List.ofFn fun i => e i)) =
      p.coeff e := by
  classical
  unfold digit
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    have hn : code (makeStrides 1 ds) (List.ofFn fun i => f i) ≠
        code (makeStrides 1 ds) (List.ofFn fun i => e i) := by
      intro h
      apply hfe
      exact Finsupp.ext (congrFun (List.ofFn_injective (code_inj (hp f hf) he h)))
    simp [hn]
  · intro h
    simp [MvPolynomial.notMem_support_iff.mp h]

theorem packDigits_ofFn (base : Int) (n : Nat) (f : Fin n → Int) :
    Hex.Internal.packDigits base (List.ofFn f) = ∑ i, f i * base ^ i.val := by
  induction n with
  | zero => simp [Hex.Internal.packDigits]
  | succ n ih =>
      simp only [List.ofFn_succ, Hex.Internal.packDigits, ih, Fin.sum_univ_succ,
        Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem pack_digits {k : Nat} (ds : List Nat) (hd : ds.length = k)
    (base : Int) (p : MvPolynomial (Fin k) Int) (hp : InBox ds p) :
    Hex.Internal.packDigits base (digits ds p) =
      MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => base ^ (makeStrides 1 ds).getD i.val 0) p := by
  classical
  rw [digits, packDigits_ofFn, eval₂_eq_code base _ (by simp [hd])]
  simp only [digit, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  let j : Fin (boxSize ds) := ⟨code (makeStrides 1 ds) (List.ofFn fun i => e i), code_lt (hp e he)⟩
  rw [Finset.sum_eq_single j]
  · simp [j]
  · intro i _ hij
    have hn : code (makeStrides 1 ds) (List.ofFn fun i => e i) ≠ i.val := by
      intro hi
      apply hij
      exact Fin.ext hi.symm
    simp [hn]
  · simp

/-- Bounded-box recovery reuses the existing balanced-digit injectivity theorem. -/
theorem balanced_injective {k : Nat} (ds : List Nat) (hd : ds.length = k)
    (p q : MvPolynomial (Fin k) Int) (hp : InBox ds p) (hq : InBox ds q)
    (H K : Nat) (hpH : norm₁ p ≤ H) (hqH : norm₁ q ≤ H) (hK : 2 * H < 2 ^ K)
    (h : MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => ((2 : Int) ^ K) ^ (makeStrides 1 ds).getD i.val 0) p =
      MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => ((2 : Int) ^ K) ^ (makeStrides 1 ds).getD i.val 0) q) : p = q := by
  classical
  have hds : digits ds p = digits ds q := by
    apply Hex.Internal.packDigits_inj K
    · simp [digits]
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      have hb := (digit_bound (makeStrides 1 ds) p i.val).trans hpH
      omega
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      have hb := (digit_bound (makeStrides 1 ds) q i.val).trans hqH
      omega
    · rw [pack_digits ds hd _ p hp, pack_digits ds hd _ q hq]
      exact h
  apply MvPolynomial.ext
  intro e
  by_cases he : e ∈ p.support ∪ q.support
  · have hb : List.Forall₂ (· ≤ ·) (List.ofFn fun i => e i) ds := by
      rcases Finset.mem_union.mp he with he | he
      · exact hp e he
      · exact hq e he
    let j : Fin (boxSize ds) := ⟨code (makeStrides 1 ds) (List.ofFn fun i => e i), code_lt hb⟩
    have hj := congrFun (List.ofFn_injective hds) j
    change digit (makeStrides 1 ds) p j.val = digit (makeStrides 1 ds) q j.val at hj
    simpa only [j, digit_coeff ds p hp e hb, digit_coeff ds q hq e hb] using hj
  · have hp' : e ∉ p.support := fun h => he (Finset.mem_union_left _ h)
    have hq' : e ∉ q.support := fun h => he (Finset.mem_union_right _ h)
    simp [MvPolynomial.notMem_support_iff.mp hp', MvPolynomial.notMem_support_iff.mp hq']

end

end Hex.Kronecker
