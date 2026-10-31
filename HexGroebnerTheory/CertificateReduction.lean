/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateReduction
public import HexGroebnerTheory.CertificatePair
public import HexGroebnerTheory.Groebner
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.ZMod

public section

namespace HexGroebnerTheory.Certificate
open Hex.Groebner.Certificate
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

variable {p n : Nat} [Hex.ZMod64.Bounds p] (order : Hex.Groebner.TermOrder)
local notation "denote" => HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n)
local notation "Canonical" => Hex.MvPoly.Kernel.CanonicalMod p n
local notation "m" => toMonomialOrder (order.cmp n)

/-- Degree comparison retains the bottom value for zero polynomials. -/
theorem degreeLE_sound {f g : Polynomial} (hf : Canonical f) (hg : Canonical g)
    (h : degreeLE order f g = true) :
    (m).toWithBotSyn ((m).withBotDegree (denote f)) ≤
      (m).toWithBotSyn ((m).withBotDegree (denote g)) := by
  cases ha : leading order f with
  | none =>
    have hz := leading_eq_none.mp ha
    subst f
    simp
  | some a =>
    cases hb : leading order g with
    | none => simp [degreeLE, ha, hb] at h
    | some b =>
      have gn : denote g ≠ 0 := by
        intro hz
        have := (denote_eq_zero_iff hg).mp hz
        subst g
        simp [leading] at hb
      rw [MonomialOrder.withBotDegree_le_withBotDegree_iff_of_ne_zero _ gn,
        leading_degree order hf ha, leading_degree order hg hb]
      apply (compare_le (order.cmp n) _ _).mp
      have hc : (compare order a.1 b.1).isLE := by simpa [degreeLE, ha, hb] using h
      rwa [compare_mono order (hf.1.1 _ (leading_mem ha)) (hg.1.1 _ (leading_mem hb))] at hc

omit [Hex.ZMod64.Bounds p] in
private theorem fold_canonical (rows : List Polynomial) (h : ∀ row ∈ rows, Canonical row)
    (acc : Polynomial) (ha : Canonical acc) :
    Canonical (rows.foldl (Hex.MvPoly.Kernel.addMod p) acc) := by
  induction rows generalizing acc with
  | nil => exact ha
  | cons row rows ih =>
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _
      (Hex.MvPoly.Kernel.addMod_canonical p ha (h row (by simp)))

omit [Hex.ZMod64.Bounds p] in
/-- Summation of canonical serialized polynomials remains canonical. -/
theorem sum_canonical (rows : List Polynomial) (h : ∀ row ∈ rows, Canonical row) :
    Canonical (sum p rows) :=
  fold_canonical rows h [] (by simp [Hex.MvPoly.Kernel.CanonicalMod, Hex.MvPoly.Kernel.Canonical])

private theorem fold_denote (rows : List Polynomial) (h : ∀ row ∈ rows, Canonical row)
    (acc : Polynomial) (ha : Canonical acc) :
    denote (rows.foldl (Hex.MvPoly.Kernel.addMod p) acc) = denote acc + (rows.map denote).sum := by
  induction rows generalizing acc with
  | nil => simp
  | cons row rows ih =>
    rw [List.foldl_cons,
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _
        (Hex.MvPoly.Kernel.addMod_canonical p ha (h row (by simp))),
      HexMvPolyTheory.Kernel.denoteMod_addMod p ha (h row (by simp))]
    simp only [List.map_cons, List.sum_cons, add_assoc]

/-- Serialized summation transports to ordinary polynomial summation. -/
theorem sum_denote (rows : List Polynomial) (h : ∀ row ∈ rows, Canonical row) :
    denote (sum p rows) = (rows.map denote).sum := by
  simpa [sum] using fold_denote order rows h []
    (by simp [Hex.MvPoly.Kernel.CanonicalMod, Hex.MvPoly.Kernel.Canonical])

omit [Hex.ZMod64.Bounds p] in
private theorem lookup_canonical (values : Array Polynomial)
    (h : ∀ value ∈ values, Canonical value) (i : Nat) :
    Canonical (values[i]?.getD []) := by
  cases hv : values[i]? with
  | none => simp [Hex.MvPoly.Kernel.CanonicalMod, Hex.MvPoly.Kernel.Canonical]
  | some value => simpa [hv] using h value (Array.mem_of_getElem? hv)

omit [Hex.ZMod64.Bounds p] in
/-- Every cofactor-times-divisor product has canonical serialization. -/
theorem products_canonical (basis cofactors : Array Polynomial)
    (hb : ∀ value ∈ basis, Canonical value) (hc : ∀ value ∈ cofactors, Canonical value) :
    ∀ row ∈ products p basis cofactors, Canonical row := by
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  exact Hex.MvPoly.Kernel.mulMod_canonical p (lookup_canonical cofactors hc i.val)
    (hb _ (Array.getElem_mem i.isLt))

omit [Hex.ZMod64.Bounds p] in
private theorem representation_remainder {σ ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (termOrder : MonomialOrder σ) (f : MvPolynomial σ K) (b q : ι → MvPolynomial σ K)
    (identity : f = ∑ i, q i * b i)
    (bounds : ∀ i, termOrder.toWithBotSyn (termOrder.withBotDegree (q i * b i)) ≤
      termOrder.toWithBotSyn (termOrder.withBotDegree f)) :
    termOrder.IsRemainder f (Set.range b) 0 := by
  classical
  rw [MonomialOrder.IsRemainder.isRemainder_range]
  let cof := Finsupp.equivFunOnFinite.symm q
  refine ⟨⟨cof, ?_, ?_⟩, by simp⟩
  · simpa [cof, Finsupp.linearCombination_apply, Finsupp.sum_fintype] using identity
  · intro i
    change termOrder.toWithBotSyn (termOrder.withBotDegree (b i)) +
      termOrder.toWithBotSyn (termOrder.withBotDegree (q i)) ≤ _
    calc
      _ = termOrder.toWithBotSyn (termOrder.withBotDegree (q i * b i)) := by
        rw [MonomialOrder.withBotDegree_mul, map_add, add_comm]
      _ ≤ _ := bounds i

/-- Acceptance gives a bounded zero-remainder representation. In particular,
applying this theorem to all final S-polynomials supplies Buchberger's actual
criterion rather than unrestricted ideal membership. -/
theorem checkReduction_sound [Fact p.Prime] (basis cofactors : Array Polynomial)
    (target : Polynomial) (h : checkReduction p n order basis cofactors target = true) :
    (m).IsRemainder (denote target)
      (Set.range fun i : Fin basis.size => denote basis[i]) 0 := by
  simp only [checkReduction] at h
  split at h
  · contradiction
  · rename_i valid
    have checks : basis.size = cofactors.size ∧
        basis.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true ∧
        cofactors.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true ∧
        Hex.MvPoly.Kernel.isCanonicalMod p n target = true := by
      simpa [and_assoc] using valid
    have hb : ∀ value ∈ basis, Canonical value := fun value hv =>
      Hex.MvPoly.Kernel.isCanonicalMod_iff.mp
        (List.all_eq_true.mp checks.2.1 value (Array.mem_def.mp hv))
    have hc : ∀ value ∈ cofactors, Canonical value := fun value hv =>
      Hex.MvPoly.Kernel.isCanonicalMod_iff.mp
        (List.all_eq_true.mp checks.2.2.1 value (Array.mem_def.mp hv))
    have ht := Hex.MvPoly.Kernel.isCanonicalMod_iff.mp checks.2.2.2
    have hp := products_canonical basis cofactors hb hc
    have accepted : (products p basis cofactors).all (fun row => degreeLE order row target) = true ∧
        Hex.MvPoly.Kernel.beq (sum p (products p basis cofactors)) target = true := by
      simpa only [Bool.and_eq_true] using h
    have identity := (HexMvPolyTheory.Kernel.beq_mod_iff p
      (cmp := order.cmp n) (sum_canonical _ hp) ht).mp accepted.2
    have sum_identity := identity.symm.trans (sum_denote order _ hp)
    have product_eq (i : Fin basis.size) :
        denote (Hex.MvPoly.Kernel.mulMod p (cofactors[i.val]?.getD []) basis[i]) =
          denote (cofactors[i.val]?.getD []) * denote basis[i] :=
      HexMvPolyTheory.Kernel.denoteMod_mulMod p (lookup_canonical cofactors hc i.val)
        (hb _ (Array.getElem_mem i.isLt))
    simp only [products, List.map_ofFn, List.sum_ofFn] at sum_identity
    change denote target = ∑ i : Fin basis.size,
      denote (Hex.MvPoly.Kernel.mulMod p (cofactors[i.val]?.getD []) basis[i]) at sum_identity
    simp_rw [product_eq] at sum_identity
    refine representation_remainder (σ := Fin n) (K := ZMod p) (m) (denote target)
      (fun i : Fin basis.size => denote basis[i])
      (fun i => denote (cofactors[i.val]?.getD [])) sum_identity ?_
    intro i
    rw [← product_eq i]
    apply degreeLE_sound order
      (Hex.MvPoly.Kernel.mulMod_canonical p (lookup_canonical cofactors hc i.val)
        (hb _ (Array.getElem_mem i.isLt))) ht
    exact List.all_eq_true.mp accepted.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

end HexGroebnerTheory.Certificate
