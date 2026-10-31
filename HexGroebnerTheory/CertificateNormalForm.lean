/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateNonmember
public import HexGroebnerTheory.CertificateDivision
public import HexGroebnerTheory.CertificateBasis

public section

namespace HexGroebnerTheory
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

/-- Independent acceptance of a complete basis and a nonzero irreducible
reconstructed remainder proves formal polynomial ideal nonmembership. -/
theorem checkNonmember_sound (context : Hex.Groebner.Context)
    (generators : Array Hex.Groebner.Certificate.Polynomial)
    (target : Hex.Groebner.Certificate.Polynomial) (witness : Hex.Groebner.Certificate.Nonmember)
    (h : Hex.Groebner.checkNonmember context generators target witness = true) :
    denote context target ∉ Ideal.span
      (Set.range fun i : Fin generators.size => denote context generators[i]) := by
  let := fieldBounds context.field
  let : Fact context.field.modulus.toNat.Prime := ⟨fieldPrime context.field⟩
  simp only [Hex.Groebner.checkNonmember, Bool.and_eq_true] at h
  have certified := checkBasis_sound context generators witness.basis witness.certificate h.1.1
  obtain ⟨_, canonical, _, _, division⟩ := Certificate.checkDivision_sound context.order
    witness.basis target witness.division h.1.2
  have groebner := (groebner_iff _ _ _).mp certified.1
  have nonzero : HexMvPolyTheory.Kernel.denoteMod context.field.modulus.toNat
      (cmp := context.order.cmp context.variables) witness.division.remainder ≠ 0 := by
    intro hz
    have zero := (HexMvPolyTheory.Kernel.isZero_mod_iff context.field.modulus.toNat
      (cmp := context.order.cmp context.variables) canonical).mpr hz
    simp [zero] at h
  intro member
  exact nonzero ((MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem_ideal'
    groebner division).mpr member)

/-- Irreducible representatives of one ideal coset are equal for a Gröbner basis. -/
theorem irreducible_unique {σ K : Type*} [Field K] (m : MonomialOrder σ)
    {G : Set (MvPolynomial σ K)} {I : Ideal (MvPolynomial σ K)}
    (basis : IsGroebnerBasis m G I) {r s : MvPolynomial σ K}
    (hr : ∀ c ∈ r.support, ∀ g ∈ G, g ≠ 0 → ¬ m.degree g ≤ c)
    (hs : ∀ c ∈ s.support, ∀ g ∈ G, g ≠ 0 → ¬ m.degree g ≤ c)
    (congruent : r - s ∈ I) : r = s := by
  classical
  apply sub_eq_zero.mp
  by_contra nonzero
  obtain ⟨g, hg, gn, divides⟩ := basis.2 (r - s) congruent nonzero
  have term := m.degree_mem_support nonzero
  have inUnion := term
  apply MvPolynomial.support_sub at inUnion
  rcases Finset.mem_union.mp inUnion with h | h
  · exact hr _ h g hg gn divides
  · exact hs _ h g hg gn divides

/-- An irreducible representative of the input polynomial modulo its original
ideal; no bound on a hypothetical alternate representative is assumed. -/
@[expose] def IsNormalForm (context : Hex.Groebner.Context)
    (generators basis : Array Hex.Groebner.Certificate.Polynomial)
    (target : Hex.Groebner.Certificate.Polynomial)
    (r : MvPolynomial (Fin context.variables) (ZMod context.field.modulus.toNat)) : Prop :=
  denote context target - r ∈ Ideal.span
      (Set.range fun i : Fin generators.size => denote context generators[i]) ∧
    ∀ c ∈ r.support, ∀ g ∈ (Set.range fun i : Fin basis.size => denote context basis[i]),
      g ≠ 0 → ¬ (toMonomialOrder (context.order.cmp context.variables)).degree g ≤ c

/-- An independently checked division by an accepted basis gives the unique
irreducible representative modulo the original input ideal. -/
theorem normalForm_spec (context : Hex.Groebner.Context)
    (generators basis : Array Hex.Groebner.Certificate.Polynomial)
    (certificate : Hex.Groebner.Certificate.Basis)
    (target : Hex.Groebner.Certificate.Polynomial) (result : Hex.Groebner.Certificate.Division)
    (hb : Hex.Groebner.checkBasis context generators basis certificate = true)
    (hd : Hex.Groebner.Certificate.checkDivision context.field.modulus.toNat context.variables
      context.order basis target result = true) :
    IsNormalForm context generators basis target (denote context result.remainder) ∧
      ∀ r, IsNormalForm context generators basis target r → r = denote context result.remainder := by
  let := fieldBounds context.field
  let : Fact context.field.modulus.toNat.Prime := ⟨fieldPrime context.field⟩
  have certified := checkBasis_sound context generators basis certificate hb
  obtain ⟨_, _, _, reconstruction, division⟩ :=
    Certificate.checkDivision_sound context.order basis target result hd
  change denote context target = (∑ i : Fin basis.size,
    denote context (result.quotients[i.val]?.getD []) * denote context basis[i]) +
      denote context result.remainder at reconstruction
  change (toMonomialOrder (context.order.cmp context.variables)).IsRemainder
    (denote context target) (Set.range fun i : Fin basis.size => denote context basis[i])
    (denote context result.remainder) at division
  have congruence : denote context target - denote context result.remainder ∈ Ideal.span
      (Set.range fun i : Fin generators.size => denote context generators[i]) := by
    rw [reconstruction, add_sub_cancel_right]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (certified.1.1 (Set.mem_range_self i))
  refine ⟨⟨congruence, division.2⟩, ?_⟩
  intro r hr
  apply irreducible_unique _ certified.1 hr.2 division.2
  simpa only [sub_sub_sub_cancel_left] using
    Ideal.sub_mem _ congruence hr.1

end HexGroebnerTheory
