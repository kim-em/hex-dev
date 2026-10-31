/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateDivisionCheck
public import HexGroebnerTheory.CertificateReduction

public section

namespace HexGroebnerTheory.Certificate
open Hex.Groebner.Certificate
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

variable {p n : Nat} [Hex.ZMod64.Bounds p] (order : Hex.Groebner.TermOrder)
local notation "denote" => HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n)
local notation "Canonical" => Hex.MvPoly.Kernel.CanonicalMod p n
local notation "m" => toMonomialOrder (order.cmp n)

/-- Accepted irreducibility checks use actual leading exponents after transport. -/
theorem irreducible_sound (divisors : Array Polynomial) (remainder : Polynomial)
    (hd : ∀ a ∈ divisors, Canonical a) (hr : Canonical remainder)
    (h : irreducible order divisors remainder = true) :
    ∀ c ∈ (denote remainder).support, ∀ i : Fin divisors.size,
      denote divisors[i] ≠ 0 → ¬ (m).degree (denote divisors[i]) ≤ c := by
  rw [irreducible_eq] at h
  intro c hc i hn hle
  obtain ⟨term, ht, rfl⟩ := support_term remainder hc
  have test := List.all_eq_true.mp (List.all_eq_true.mp h term ht)
    divisors[i] (Array.mem_def.mp (Array.getElem_mem i.isLt))
  have ci := hd _ (Array.getElem_mem i.isLt)
  cases hi : leading order divisors[i] with
  | none =>
    have zero := (denote_eq_zero_iff (cmp := order.cmp n) ci).mpr (leading_eq_none.mp hi)
    exact hn zero
  | some head =>
    erw [leading_degree order ci hi] at hle
    have hdiv := (divides_mono (ci.1.1 _ (leading_mem hi)) (hr.1.1 _ ht)).mpr hle
    simp only [Fin.getElem_fin] at hi
    simp [hi, hdiv] at test

omit [Hex.ZMod64.Bounds p] in
private theorem remainder_of_sum {σ ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (termOrder : MonomialOrder σ) (f r : MvPolynomial σ K) (b q : ι → MvPolynomial σ K)
    (identity : f = (∑ i, q i * b i) + r)
    (bounds : ∀ i, termOrder.toWithBotSyn (termOrder.withBotDegree (q i * b i)) ≤
      termOrder.toWithBotSyn (termOrder.withBotDegree f))
    (irreducible : ∀ c ∈ r.support, ∀ i, b i ≠ 0 → ¬ termOrder.degree (b i) ≤ c) :
    termOrder.IsRemainder f (Set.range b) r := by
  classical
  rw [MonomialOrder.IsRemainder.isRemainder_range]
  let cof := Finsupp.equivFunOnFinite.symm q
  refine ⟨⟨cof, ?_, ?_⟩, irreducible⟩
  · simpa [cof, Finsupp.linearCombination_apply, Finsupp.sum_fintype] using identity
  · intro i
    change termOrder.toWithBotSyn (termOrder.withBotDegree (b i)) +
      termOrder.toWithBotSyn (termOrder.withBotDegree (q i)) ≤ _
    calc
      _ = termOrder.toWithBotSyn (termOrder.withBotDegree (q i * b i)) := by
        rw [MonomialOrder.withBotDegree_mul, map_add, add_comm]
      _ ≤ _ := bounds i

/-- Acceptance proves reconstruction with the actual supplied quotients and a
standard irreducible remainder, without a Gröbner-basis hypothesis. -/
theorem checkDivision_sound [Fact p.Prime] (divisors : Array Polynomial)
    (dividend : Polynomial) (result : Division)
    (h : checkDivision p n order divisors dividend result = true) :
    (∀ q ∈ result.quotients, Canonical q) ∧ Canonical result.remainder ∧
      result.quotients.size = divisors.size ∧
      denote dividend = (∑ i : Fin divisors.size,
        denote (result.quotients[i.val]?.getD []) * denote divisors[i]) + denote result.remainder ∧
      (m).IsRemainder (denote dividend)
        (Set.range fun i : Fin divisors.size => denote divisors[i]) (denote result.remainder) := by
  simp only [checkDivision] at h
  split at h
  · contradiction
  · rename_i valid
    have checks : result.quotients.size = divisors.size ∧
        divisors.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true ∧
        result.quotients.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true ∧
        Hex.MvPoly.Kernel.isCanonicalMod p n dividend = true ∧
        Hex.MvPoly.Kernel.isCanonicalMod p n result.remainder = true := by
      simpa [and_assoc] using valid
    have hd : ∀ a ∈ divisors, Canonical a := fun a ha =>
      Hex.MvPoly.Kernel.isCanonicalMod_iff.mp
        (List.all_eq_true.mp checks.2.1 a (Array.mem_def.mp ha))
    have hq : ∀ a ∈ result.quotients, Canonical a := fun a ha =>
      Hex.MvPoly.Kernel.isCanonicalMod_iff.mp
        (List.all_eq_true.mp checks.2.2.1 a (Array.mem_def.mp ha))
    have hf := Hex.MvPoly.Kernel.isCanonicalMod_iff.mp checks.2.2.2.1
    have hr := Hex.MvPoly.Kernel.isCanonicalMod_iff.mp checks.2.2.2.2
    have hp := products_canonical divisors result.quotients hd hq
    have accepted := Bool.and_eq_true_iff.mp h
    have left := Bool.and_eq_true_iff.mp accepted.1
    have bounds := Bool.and_eq_true_iff.mp left.1
    have total := (HexMvPolyTheory.Kernel.beq_mod_iff p (cmp := order.cmp n)
      (Hex.MvPoly.Kernel.addMod_canonical p (sum_canonical _ hp) hr) hf).mp accepted.2
    have reconstruction : denote dividend =
        ((products p divisors result.quotients).map denote).sum + denote result.remainder := by
      rw [← total, HexMvPolyTheory.Kernel.denoteMod_addMod p (sum_canonical _ hp) hr,
        sum_denote order _ hp]
    have lookup (i : Nat) : Canonical (result.quotients[i]?.getD []) := by
      cases hi : result.quotients[i]? with
      | none => simp [Hex.MvPoly.Kernel.CanonicalMod, Hex.MvPoly.Kernel.Canonical]
      | some value => simpa [hi] using hq value (Array.mem_of_getElem? hi)
    have product_eq (i : Fin divisors.size) :
        denote (Hex.MvPoly.Kernel.mulMod p (result.quotients[i.val]?.getD []) divisors[i]) =
          denote (result.quotients[i.val]?.getD []) * denote divisors[i] :=
      HexMvPolyTheory.Kernel.denoteMod_mulMod p (lookup i.val) (hd _ (Array.getElem_mem i.isLt))
    simp only [products, List.map_ofFn, List.sum_ofFn] at reconstruction
    change denote dividend = (∑ i : Fin divisors.size,
      denote (Hex.MvPoly.Kernel.mulMod p (result.quotients[i.val]?.getD []) divisors[i])) +
        denote result.remainder at reconstruction
    simp_rw [product_eq] at reconstruction
    refine ⟨hq, hr, checks.1, reconstruction, ?_⟩
    refine remainder_of_sum (σ := Fin n) (K := ZMod p) (m) (denote dividend)
      (denote result.remainder) (fun i : Fin divisors.size => denote divisors[i])
      (fun i => denote (result.quotients[i.val]?.getD [])) reconstruction ?_
      (irreducible_sound order divisors result.remainder hd hr left.2)
    intro i
    rw [← product_eq i]
    apply degreeLE_sound order
      (Hex.MvPoly.Kernel.mulMod_canonical p (lookup i.val) (hd _ (Array.getElem_mem i.isLt))) hf
    exact List.all_eq_true.mp bounds.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

end HexGroebnerTheory.Certificate
