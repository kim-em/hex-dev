/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Certificate
public import HexMvPolyTheory.KernelResidue
public import Mathlib.RingTheory.Ideal.Span

public section

namespace HexGroebnerTheory
open scoped HexMvPolyTheory HexModArithTheory.ZMod64
namespace Certificate
open Hex.Groebner.Certificate

variable (p n : Nat) [Hex.ZMod64.Bounds p]
  {cmp : Hex.Mono n → Hex.Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
local notation "denote" => HexMvPolyTheory.Kernel.denoteMod p (n := n) (cmp := cmp)
local notation "Canonical" => Hex.MvPoly.Kernel.CanonicalMod p n

/-- Every computed row is canonical and belongs to the original generated ideal. -/
@[expose] def Valid (generators : Array Polynomial) (a : Polynomial) : Prop :=
  Canonical a ∧ denote a ∈ Ideal.span (Set.range fun i : Fin generators.size => denote generators[i])

private theorem input_valid (generators : Array Polynomial)
    (hg : ∀ a ∈ generators, Canonical a) {i : Nat} {a : Polynomial}
    (ha : generators[i]? = some a) : Valid p n (cmp := cmp) generators a := by
  have hi : i < generators.size := by
    by_contra h
    simp [Array.getElem?_eq_none (by omega : generators.size ≤ i)] at ha
  have heq : generators[i] = a := by simpa [hi] using ha
  subst a
  exact ⟨hg _ (Array.getElem_mem hi), Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩⟩

/-- A local arithmetic identity preserves both canonicality and ideal membership. -/
theorem evaluate_valid (generators values : Array Polynomial)
    (hg : ∀ a ∈ generators, Canonical a)
    (hv : ∀ a ∈ values, Valid p n (cmp := cmp) generators a)
    {node : Node} {a : Polynomial}
    (ha : evaluate p n generators values node = some a) : Valid p n (cmp := cmp) generators a := by
  have lookup {i : Nat} {v : Polynomial} (h : values[i]? = some v) : Valid p n (cmp := cmp) generators v := by
    apply hv v
    exact Array.mem_of_getElem? h
  cases node with
  | zero =>
    simp only [evaluate, Option.some.injEq] at ha
    subst a
    exact ⟨by simp [Hex.MvPoly.Kernel.CanonicalMod, Hex.MvPoly.Kernel.Canonical], by simp⟩
  | generator i => exact input_valid p n (cmp := cmp) generators hg ha
  | add i j =>
    cases hl : values[i]? with
    | none => simp [evaluate, hl] at ha
    | some left =>
      cases hr : values[j]? with
      | none => simp [evaluate, hl, hr] at ha
      | some right =>
        simp [evaluate, hl, hr, bind, Option.bind] at ha
        subst a
        obtain ⟨hcl, hil⟩ := lookup hl
        obtain ⟨hcr, hir⟩ := lookup hr
        exact ⟨Hex.MvPoly.Kernel.addMod_canonical p hcl hcr, by
          rw [HexMvPolyTheory.Kernel.denoteMod_addMod p hcl hcr]
          exact Ideal.add_mem _ hil hir⟩
  | scale c i =>
    by_cases hc : c ≥ p
    · simp [evaluate, hc] at ha
    · cases hv : values[i]? with
      | none => simp [evaluate, hc, hv] at ha
      | some v =>
        simp [evaluate, hc, hv, bind, Option.bind] at ha
        subst a
        obtain ⟨hcv, hiv⟩ := lookup hv
        exact ⟨Hex.MvPoly.Kernel.smulMod_canonical p c hcv, by
          rw [HexMvPolyTheory.Kernel.denoteMod_smulMod p c hcv]
          exact Ideal.mul_mem_left _ _ hiv⟩
  | multiply factor i =>
    by_cases hf : Hex.MvPoly.Kernel.isCanonicalMod p n factor = true
    · cases hv : values[i]? with
      | none => simp [evaluate, hf, hv] at ha
      | some v =>
        simp [evaluate, hf, hv, bind, Option.bind] at ha
        subst a
        obtain ⟨hcv, hiv⟩ := lookup hv
        have hcf := Hex.MvPoly.Kernel.isCanonicalMod_iff.mp hf
        exact ⟨Hex.MvPoly.Kernel.mulMod_canonical p hcf hcv, by
          rw [HexMvPolyTheory.Kernel.denoteMod_mulMod p hcf hcv]
          exact Ideal.mul_mem_left _ _ hiv⟩
    · simp [evaluate, hf] at ha

/-- Replay preserves the original ideal across every shared derivation node. -/
theorem replay_valid (generators : Array Polynomial)
    (hg : ∀ a ∈ generators, Canonical a) (nodes : List Node)
    {values result : Array Polynomial}
    (hv : ∀ a ∈ values, Valid p n (cmp := cmp) generators a)
    (hr : replay p n generators nodes values = some result) :
    ∀ a ∈ result, Valid p n (cmp := cmp) generators a := by
  induction nodes generalizing values with
  | nil =>
    simp only [replay, Option.some.injEq] at hr
    subst result
    exact hv
  | cons node nodes ih =>
    cases he : evaluate p n generators values node with
    | none => simp [replay, he, bind, Option.bind] at hr
    | some value =>
      simp [replay, he, bind, Option.bind] at hr
      apply ih _ hr
      intro a ha
      rcases Array.mem_push.mp ha with ha | rfl
      · exact hv a ha
      · exact evaluate_valid p n (cmp := cmp) generators values hg hv he

end Certificate
/-- The existing residue carrier's bounds follow from explicit prime metadata. -/
theorem fieldBounds (field : Hex.Groebner.PrimeField) :
    Hex.ZMod64.Bounds field.modulus.toNat where
  pPos := by have := field.prime.two_le; omega
  pLtR := field.bound

/-- Explicit executable primality evidence satisfies Mathlib's prime criterion. -/
theorem fieldPrime (field : Hex.Groebner.PrimeField) : Nat.Prime field.modulus.toNat :=
  Nat.prime_def.mpr field.prime

/-- Interpret a certificate polynomial through the existing residue equivalence. -/
@[expose] noncomputable def denote (context : Hex.Groebner.Context)
    (a : Hex.Groebner.Certificate.Polynomial) :
    MvPolynomial (Fin context.variables) (ZMod context.field.modulus.toNat) :=
  letI := fieldBounds context.field
  HexMvPolyTheory.Kernel.denoteMod context.field.modulus.toNat
    (n := context.variables) (cmp := context.order.cmp context.variables) a

/-- Positive certificate acceptance proves formal polynomial ideal membership,
without any assumption about the producer or a Gröbner basis. -/
theorem checkDerivation_sound (context : Hex.Groebner.Context)
    (generators : Array Hex.Groebner.Certificate.Polynomial)
    (target : Hex.Groebner.Certificate.Polynomial)
    (certificate : Hex.Groebner.Certificate.Derivation)
    (h : Hex.Groebner.checkDerivation context generators target certificate = true) :
    denote context target ∈ Ideal.span
      (Set.range fun i : Fin generators.size => denote context generators[i]) := by
  let := fieldBounds context.field
  simp only [Hex.Groebner.checkDerivation] at h
  split at h
  · contradiction
  · rename_i hc
    have canon : generators.toList.all (Hex.MvPoly.Kernel.isCanonicalMod context.field.modulus.toNat context.variables) = true ∧
        Hex.MvPoly.Kernel.isCanonicalMod context.field.modulus.toNat context.variables target = true := by
      simpa using hc
    cases hr : Hex.Groebner.Certificate.replay context.field.modulus.toNat context.variables
        generators certificate.nodes #[] with
    | none => simp [hr] at h
    | some values =>
      simp only [hr] at h
      cases hv : values[certificate.root]? with
      | none => simp [hv] at h
      | some value =>
        simp only [hv] at h
        have hg : ∀ a ∈ generators,
            Hex.MvPoly.Kernel.CanonicalMod context.field.modulus.toNat context.variables a := by
          intro a ha
          exact Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (List.all_eq_true.mp canon.1 a (Array.mem_def.mp ha))
        have valid := Certificate.replay_valid context.field.modulus.toNat context.variables
          (cmp := context.order.cmp context.variables) generators hg certificate.nodes (values := #[]) (by simp) hr value (Array.mem_of_getElem? hv)
        have heq := HexMvPolyTheory.Kernel.beq_mod_iff context.field.modulus.toNat
          (cmp := context.order.cmp context.variables) valid.1 (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp canon.2) |>.mp h
        simpa only [denote] using heq ▸ valid.2

end HexGroebnerTheory
