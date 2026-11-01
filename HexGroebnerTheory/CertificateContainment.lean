/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateContainment
public import HexGroebnerTheory.Certificate

public section

namespace HexGroebnerTheory.Certificate
open Hex.Groebner.Certificate
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

/-- Shared containment acceptance validates all input representations and
proves each target belongs to the ideal of the supplied generators. -/
theorem checkContainment_sound (p n : Nat) [Hex.ZMod64.Bounds p]
    {cmp : Hex.Mono n → Hex.Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (generators targets : Array Polynomial) (certificate : Containment)
    (h : checkContainment p n generators targets certificate = true) :
    (∀ a ∈ generators, Hex.MvPoly.Kernel.CanonicalMod p n a) ∧
    (∀ a ∈ targets, Hex.MvPoly.Kernel.CanonicalMod p n a) ∧
    ∀ i : Fin targets.size,
      HexMvPolyTheory.Kernel.denoteMod p (cmp := cmp) targets[i] ∈ Ideal.span
        (Set.range fun j : Fin generators.size =>
          HexMvPolyTheory.Kernel.denoteMod p (cmp := cmp) generators[j]) := by
  simp only [checkContainment] at h
  split at h
  · contradiction
  · rename_i valid
    have checks : generators.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true ∧
        targets.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true ∧
        certificate.roots.size = targets.size := by
      simpa [and_assoc] using valid
    have hg : ∀ a ∈ generators, Hex.MvPoly.Kernel.CanonicalMod p n a := fun a ha =>
      Hex.MvPoly.Kernel.isCanonicalMod_iff.mp
        (List.all_eq_true.mp checks.1 a (Array.mem_def.mp ha))
    have ht : ∀ a ∈ targets, Hex.MvPoly.Kernel.CanonicalMod p n a := fun a ha =>
      Hex.MvPoly.Kernel.isCanonicalMod_iff.mp
        (List.all_eq_true.mp checks.2.1 a (Array.mem_def.mp ha))
    refine ⟨hg, ht, ?_⟩
    cases hr : replay p n generators certificate.nodes #[] with
    | none => simp [hr] at h
    | some values =>
      simp only [hr] at h
      intro i
      have hi := List.all_eq_true.mp h i (by simp)
      cases hv : values[certificate.roots[i.val]?.getD values.size]? with
      | none => simp [hv] at hi
      | some value =>
        simp only [hv] at hi
        have validValue := replay_valid p n (cmp := cmp) generators hg certificate.nodes
          (values := #[]) (by simp) hr value (Array.mem_of_getElem? hv)
        have heq := (HexMvPolyTheory.Kernel.beq_mod_iff p (cmp := cmp) validValue.1
          (ht _ (Array.getElem_mem i.isLt))).mp hi
        exact heq ▸ validValue.2

end HexGroebnerTheory.Certificate
