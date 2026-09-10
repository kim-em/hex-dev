/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Presentation
public import Mathlib.Data.Sym.NatCard

public section

/-!
# Bounded primitive-element search

The semantic invariant behind the executable maximum-degree shift search.
-/

namespace Hex.AlgebraicPoly.Common

open Module IntermediateField

private theorem exists_primitive_shift
    (F E A : Type*) [Field F] [Infinite F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Field A] [IsAlgClosed A] [Algebra F A]
    (theta alpha : E)
    (hgen : ∀ phi psi : E →ₐ[F] A,
      phi theta = psi theta → phi alpha = psi alpha → phi = psi)
    (scalar : Fin (Nat.choose (finrank F E) 2 + 1) → F)
    (hscalar : Function.Injective scalar) :
    ∃ k, F⟮theta + scalar k • alpha⟯ = ⊤ := by
  classical
  by_contra hprimitive
  push Not at hprimitive
  have hbad (k : Fin (Nat.choose (finrank F E) 2 + 1)) :
      ¬Function.Injective fun phi : E →ₐ[F] A =>
        phi (theta + scalar k • alpha) := by
    intro hinjective
    exact hprimitive k <|
      (Field.primitive_element_iff_algHom_eq_of_eval' F A
        (fun _ => IsAlgClosed.splits _) _).mpr hinjective
  have hwitness (k : Fin (Nat.choose (finrank F E) 2 + 1)) :
      ∃ phi psi : E →ₐ[F] A,
        phi ≠ psi ∧
          phi (theta + scalar k • alpha) =
            psi (theta + scalar k • alpha) := by
    obtain ⟨phi, psi, heq, hne⟩ :=
      Function.not_injective_iff.mp (hbad k)
    exact ⟨phi, psi, hne, heq⟩
  choose phi psi hne heval using hwitness
  let pair (k : Fin (Nat.choose (finrank F E) 2 + 1)) :
      {z : Sym2 (E →ₐ[F] A) // ¬z.IsDiag} :=
    ⟨s(phi k, psi k), by simpa using hne k⟩
  have scalar_unique (phi psi : E →ₐ[F] A) (hphi : phi ≠ psi)
      (c d : F)
      (hc : phi (theta + c • alpha) = psi (theta + c • alpha))
      (hd : phi (theta + d • alpha) = psi (theta + d • alpha)) :
      c = d := by
    have halpha : phi alpha ≠ psi alpha := by
      intro halpha
      apply hphi
      apply hgen phi psi
      · simpa [halpha] using hc
      · exact halpha
    simp only [map_add, Algebra.smul_def, map_mul, AlgHom.commutes] at hc hd
    have hzero :
        algebraMap F A (c - d) * (phi alpha - psi alpha) = 0 := by
      rw [map_sub]
      linear_combination hc - hd
    have hmap : algebraMap F A (c - d) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr halpha)
    apply sub_eq_zero.mp
    apply (algebraMap F A).injective
    simpa using hmap
  have hpair : Function.Injective pair := by
    intro i j hij
    have hpairs : s(phi i, psi i) = s(phi j, psi j) :=
      congrArg Subtype.val hij
    rcases Sym2.eq_iff.mp hpairs with hsame | hswap
    · obtain ⟨hphi, hpsi⟩ := hsame
      have hscalars : scalar i = scalar j := by
        apply scalar_unique (phi i) (psi i) (hne i)
        · exact heval i
        · simpa [hphi, hpsi] using heval j
      exact hscalar hscalars
    · obtain ⟨hphi, hpsi⟩ := hswap
      have hscalars : scalar i = scalar j := by
        apply scalar_unique (phi i) (psi i) (hne i)
        · exact heval i
        · simpa [hphi, hpsi] using (heval j).symm
      exact hscalar hscalars
  have hcard := Fintype.card_le_of_injective pair hpair
  rw [Fintype.card_fin, Sym2.card_subtype_not_diag,
    AlgHom.card F E A] at hcard
  rw [HexRootsMathlib.choose_eq_choose] at hcard
  omega

private theorem finrank_pair_le (theta alpha : AlgebraicNumber) :
    finrank Rat Rat⟮theta.toComplex, alpha.toComplex⟯ ≤
      degree theta * degree alpha := by
  let thetaField : IntermediateField Rat ℂ := Rat⟮theta.toComplex⟯
  let alphaField : IntermediateField Rat ℂ := Rat⟮alpha.toComplex⟯
  have htheta : IsIntegral Rat theta.toComplex := isIntegral_toComplex theta
  have halpha : IsIntegral Rat alpha.toComplex := isIntegral_toComplex alpha
  have hpair : ({theta.toComplex, alpha.toComplex} : Set ℂ) =
      {theta.toComplex} ∪ {alpha.toComplex} := by
    ext z
    simp [or_comm]
  have hfields : Rat⟮theta.toComplex, alpha.toComplex⟯ =
      thetaField ⊔ alphaField := by
    dsimp [thetaField, alphaField]
    rw [hpair, IntermediateField.adjoin_union]
  calc
    finrank Rat Rat⟮theta.toComplex, alpha.toComplex⟯ =
        finrank Rat ↥(thetaField ⊔ alphaField) := by
          rw [hfields]
    _ ≤ finrank Rat thetaField * finrank Rat alphaField :=
      IntermediateField.finrank_sup_le thetaField alphaField
    _ = degree theta * degree alpha := by
      rw [IntermediateField.adjoin.finrank htheta,
        IntermediateField.adjoin.finrank halpha,
        degree_eq_minpoly, degree_eq_minpoly]

private theorem shift_degree_le (theta alpha candidate : AlgebraicNumber)
    (c : Int) (hcandidate : shift? theta alpha c = some candidate) :
    degree candidate ≤
      finrank Rat Rat⟮theta.toComplex, alpha.toComplex⟯ := by
  let K : IntermediateField Rat ℂ :=
    Rat⟮theta.toComplex, alpha.toComplex⟯
  let thetaK : K := IntermediateField.AdjoinPair.gen₁
    Rat theta.toComplex alpha.toComplex
  let alphaK : K := IntermediateField.AdjoinPair.gen₂
    Rat theta.toComplex alpha.toComplex
  let candidateK : K := thetaK + (c : Rat) • alphaK
  let : FiniteDimensional Rat K :=
    IntermediateField.finiteDimensional_adjoin_pair
      (isIntegral_toComplex theta) (isIntegral_toComplex alpha)
  have hvalue : candidate.toComplex = (candidateK : ℂ) := by
    rw [shift?_sound theta alpha c hcandidate]
    simp [candidateK, thetaK, alphaK,
      IntermediateField.AdjoinPair.gen₁,
      IntermediateField.AdjoinPair.gen₂, Algebra.smul_def]
  rw [degree_eq_minpoly, hvalue]
  change (minpoly Rat (K.val candidateK)).natDegree ≤ finrank Rat K
  rw [minpoly.algHom_eq K.val Subtype.val_injective candidateK]
  exact minpoly.natDegree_le candidateK

private theorem exists_shift_degree_eq (theta alpha : AlgebraicNumber) :
    ∃ k < Nat.choose (degree theta * degree alpha) 2 + 1,
      ∃ candidate, shift? theta alpha (signedShift k) = some candidate ∧
        degree candidate =
          finrank Rat Rat⟮theta.toComplex, alpha.toComplex⟯ := by
  classical
  let K : IntermediateField Rat ℂ :=
    Rat⟮theta.toComplex, alpha.toComplex⟯
  let thetaK : K := IntermediateField.AdjoinPair.gen₁
    Rat theta.toComplex alpha.toComplex
  let alphaK : K := IntermediateField.AdjoinPair.gen₂
    Rat theta.toComplex alpha.toComplex
  let : FiniteDimensional Rat K :=
    IntermediateField.finiteDimensional_adjoin_pair
      (isIntegral_toComplex theta) (isIntegral_toComplex alpha)
  have hgen : ∀ phi psi : K →ₐ[Rat] ℂ,
      phi thetaK = psi thetaK → phi alphaK = psi alphaK → phi = psi := by
    intro phi psi htheta halpha
    apply IntermediateField.adjoin_algHom_ext Rat
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htheta
    · exact halpha
  let scalar : Fin (Nat.choose (finrank Rat K) 2 + 1) → Rat :=
    fun k => signedShift k
  have hscalar : Function.Injective scalar := by
    intro i j hij
    apply Fin.ext
    apply signedShift_injective
    change (signedShift (i : Nat) : Rat) =
      (signedShift (j : Nat) : Rat) at hij
    exact_mod_cast hij
  obtain ⟨k, hprimitive⟩ := exists_primitive_shift
    Rat K ℂ thetaK alphaK hgen scalar hscalar
  let candidateK : K := thetaK + scalar k • alphaK
  have hdegreeK : (minpoly Rat candidateK).natDegree = finrank Rat K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq Rat candidateK).mp
      hprimitive
  obtain ⟨candidate, hcandidate⟩ := Option.isSome_iff_exists.mp
    (shift?_isSome theta alpha (signedShift k))
  have hvalue : candidate.toComplex = (candidateK : ℂ) := by
    rw [shift?_sound theta alpha (signedShift k) hcandidate]
    simp [candidateK, scalar, thetaK, alphaK,
      IntermediateField.AdjoinPair.gen₁,
      IntermediateField.AdjoinPair.gen₂, Algebra.smul_def]
  have hdegree : degree candidate = finrank Rat K := by
    rw [degree_eq_minpoly, hvalue]
    change (minpoly Rat (K.val candidateK)).natDegree = finrank Rat K
    rw [minpoly.algHom_eq K.val Subtype.val_injective candidateK]
    exact hdegreeK
  have hfinrank : finrank Rat K ≤ degree theta * degree alpha :=
    finrank_pair_le theta alpha
  have hchoose : Nat.choose (finrank Rat K) 2 ≤
      Nat.choose (degree theta * degree alpha) 2 := by
    rw [HexRootsMathlib.choose_eq_choose,
      HexRootsMathlib.choose_eq_choose]
    exact _root_.Nat.choose_le_choose 2 hfinrank
  exact ⟨k, by omega, candidate, hcandidate, hdegree⟩

private theorem extendShiftStep_bounds (theta alpha : AlgebraicNumber)
    (best : Option ShiftCandidate) (k : Nat) (next : ShiftCandidate)
    (hnext : extendShiftStep theta alpha best k = some (some next)) :
    (∀ current, best = some current →
      degree current.value ≤ degree next.value) ∧
      ∀ candidate, shift? theta alpha (signedShift k) = some candidate →
        degree candidate ≤ degree next.value := by
  obtain ⟨candidate, hcandidate⟩ := Option.isSome_iff_exists.mp
    (shift?_isSome theta alpha (signedShift k))
  simp only [extendShiftStep, hcandidate] at hnext
  cases best with
  | none =>
      have hvalue := Option.some.inj hnext
      have hcandidateNext := Option.some.inj hvalue
      subst next
      constructor
      · intro current hcurrent
        simp at hcurrent
      · intro shifted hshifted
        have heq : shifted = candidate :=
          Option.some.inj (hshifted.symm.trans hcandidate)
        exact le_of_eq (congrArg degree heq)
  | some current =>
      by_cases hdegree : degree current.value < degree candidate
      · simp [hdegree] at hnext
        subst next
        constructor
        · intro previous hprevious
          have heq : previous = current :=
            (Option.some.inj hprevious).symm
          subst previous
          exact le_of_lt hdegree
        · intro shifted hshifted
          have heq : shifted = candidate :=
            Option.some.inj (hshifted.symm.trans hcandidate)
          exact le_of_eq (congrArg degree heq)
      · simp [hdegree] at hnext
        subst next
        constructor
        · intro previous hprevious
          exact le_of_eq
            (congrArg (fun a => degree a.value)
              (Option.some.inj hprevious)).symm
        · intro shifted hshifted
          have heq : shifted = candidate :=
            Option.some.inj (hshifted.symm.trans hcandidate)
          subst shifted
          exact Nat.le_of_not_gt hdegree

private theorem extendShiftFold_max (theta alpha : AlgebraicNumber)
    (indices : List Nat) (best : Option ShiftCandidate)
    (out : ShiftCandidate)
    (hfold : indices.foldlM (extendShiftStep theta alpha) best =
      some (some out)) :
    (∀ current, best = some current →
      degree current.value ≤ degree out.value) ∧
      ∀ k ∈ indices, ∀ candidate,
        shift? theta alpha (signedShift k) = some candidate →
          degree candidate ≤ degree out.value := by
  induction indices generalizing best with
  | nil =>
      have hbest := Option.some.inj hfold
      constructor
      · intro current hcurrent
        rw [hbest] at hcurrent
        exact le_of_eq (congrArg (fun a => degree a.value)
          (Option.some.inj hcurrent)).symm
      · simp
  | cons k indices ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨nextBest, hstep, htail⟩ :=
        Option.bind_eq_some_iff.mp hfold
      obtain ⟨shifted, hshifted⟩ := Option.isSome_iff_exists.mp
        (shift?_isSome theta alpha (signedShift k))
      have hnextExists : ∃ next, nextBest = some next := by
        simp only [extendShiftStep, hshifted] at hstep
        cases best with
        | none =>
            exact ⟨⟨signedShift k, shifted⟩,
              (Option.some.inj hstep).symm⟩
        | some current =>
            by_cases hdegree : degree current.value < degree shifted
            · exact ⟨⟨signedShift k, shifted⟩,
                by simpa [hdegree] using hstep.symm⟩
            · exact ⟨current, by simpa [hdegree] using hstep.symm⟩
      obtain ⟨next, hnext⟩ := hnextExists
      subst nextBest
      obtain ⟨hnextOut, htailMax⟩ := ih (some next) htail
      obtain ⟨hbestNext, hshiftNext⟩ :=
        extendShiftStep_bounds theta alpha best k next hstep
      constructor
      · intro current hcurrent
        exact (hbestNext current hcurrent).trans
          (hnextOut next rfl)
      · intro index hindex candidate hcandidate
        simp only [List.mem_cons] at hindex
        rcases hindex with rfl | hindex
        · exact (hshiftNext candidate hcandidate).trans
            (hnextOut next rfl)
        · exact htailMax index hindex candidate hcandidate

/-- A successful maximum-degree shift search reaches the full compositum
degree. -/
theorem extend?_degree (theta alpha gamma : AlgebraicNumber)
    (hgamma : extend? theta alpha = some gamma) :
    degree gamma =
      finrank Rat Rat⟮theta.toComplex, alpha.toComplex⟯ := by
  let upper := degree theta * degree alpha
  let count := Nat.choose upper 2 + 1
  obtain ⟨shifted, hshifted⟩ := Option.isSome_iff_exists.mp
    (extendShift?_isSome theta alpha)
  have hvalue : shifted.value = gamma := by
    unfold extend? at hgamma
    rw [hshifted] at hgamma
    exact Option.some.inj hgamma
  subst gamma
  have hselected := hshifted
  unfold extendShift? at hshifted
  change ((List.range count).foldlM
    (extendShiftStep theta alpha) none >>= fun best => best) =
      some shifted at hshifted
  obtain ⟨best, hfold, hbest⟩ :=
    Option.bind_eq_some_iff.mp hshifted
  subst best
  obtain ⟨_, hmaximum⟩ := extendShiftFold_max theta alpha
    (List.range count) none shifted hfold
  obtain ⟨k, hk, candidate, hcandidate, hcandidateDegree⟩ :=
    exists_shift_degree_eq theta alpha
  have hlower :
      finrank Rat Rat⟮theta.toComplex, alpha.toComplex⟯ ≤
        degree shifted.value := by
    rw [← hcandidateDegree]
    exact hmaximum k (List.mem_range.mpr hk) candidate hcandidate
  have hsource := extendShift?_source theta alpha shifted hselected
  exact le_antisymm
    (shift_degree_le theta alpha shifted.value shifted.shift hsource)
    hlower

/-- The maximum-degree shift returned by `extend?` generates exactly the
compositum of its two inputs. -/
theorem extend?_field (theta alpha gamma : AlgebraicNumber)
    (hgamma : extend? theta alpha = some gamma) :
    Rat⟮gamma.toComplex⟯ =
      Rat⟮theta.toComplex, alpha.toComplex⟯ := by
  obtain ⟨shifted, hshifted⟩ := Option.isSome_iff_exists.mp
    (extendShift?_isSome theta alpha)
  have hvalue : shifted.value = gamma := by
    unfold extend? at hgamma
    rw [hshifted] at hgamma
    exact Option.some.inj hgamma
  have hshift := extendShift?_source theta alpha shifted hshifted
  rw [hvalue] at hshift
  let K : IntermediateField Rat ℂ :=
    Rat⟮theta.toComplex, alpha.toComplex⟯
  have hmember : gamma.toComplex ∈ K := by
    rw [shift?_sound theta alpha shifted.shift hshift]
    apply K.add_mem
    · exact IntermediateField.mem_adjoin_pair_left
        Rat theta.toComplex alpha.toComplex
    · apply K.mul_mem
      · simp
      · exact IntermediateField.mem_adjoin_pair_right
          Rat theta.toComplex alpha.toComplex
  have hle : Rat⟮gamma.toComplex⟯ ≤ K :=
    IntermediateField.adjoin_simple_le_iff.mpr hmember
  let : FiniteDimensional Rat K :=
    IntermediateField.finiteDimensional_adjoin_pair
      (isIntegral_toComplex theta) (isIntegral_toComplex alpha)
  apply IntermediateField.eq_of_le_of_finrank_eq hle
  rw [IntermediateField.adjoin.finrank (isIntegral_toComplex gamma),
    ← degree_eq_minpoly]
  exact extend?_degree theta alpha gamma hgamma

/-- The shift-retaining maximum-degree candidate generates the same
compositum as the two inputs. -/
theorem extendShift?_field (theta alpha : AlgebraicNumber)
    (shifted : ShiftCandidate)
    (hshifted : extendShift? theta alpha = some shifted) :
    Rat⟮shifted.value.toComplex⟯ =
      Rat⟮theta.toComplex, alpha.toComplex⟯ := by
  have hvalue := extendShift?_value theta alpha
  rw [hshifted] at hvalue
  exact extend?_field theta alpha shifted.value hvalue.symm

private theorem primitiveFold_contains (items : List AlgebraicNumber)
    (initial out : AlgebraicNumber)
    (hfold : items.foldlM extend? initial = some out) :
    initial.toComplex ∈ Rat⟮out.toComplex⟯ ∧
      ∀ a ∈ items, a.toComplex ∈ Rat⟮out.toComplex⟯ := by
  induction items generalizing initial with
  | nil =>
      have heq := Option.some.inj hfold
      subst out
      exact ⟨IntermediateField.mem_adjoin_simple_self Rat initial.toComplex,
        by simp⟩
  | cons a items ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨next, hnext, htail⟩ := Option.bind_eq_some_iff.mp hfold
      obtain ⟨hnextMem, htailMem⟩ := ih next htail
      have hle : Rat⟮next.toComplex⟯ ≤ Rat⟮out.toComplex⟯ :=
        IntermediateField.adjoin_simple_le_iff.mpr hnextMem
      have hfield := extend?_field initial a next hnext
      have hinitialNext : initial.toComplex ∈ Rat⟮next.toComplex⟯ := by
        rw [hfield]
        exact IntermediateField.mem_adjoin_pair_left
          Rat initial.toComplex a.toComplex
      have haNext : a.toComplex ∈ Rat⟮next.toComplex⟯ := by
        rw [hfield]
        exact IntermediateField.mem_adjoin_pair_right
          Rat initial.toComplex a.toComplex
      constructor
      · exact hle hinitialNext
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hle haNext
        · exact htailMem b hb

/-- Every input coefficient belongs to the simple field selected by a
successful primitive-element fold. -/
theorem primitive?_contains (coefficients : Array AlgebraicNumber)
    (gamma a : AlgebraicNumber)
    (hgamma : primitive? coefficients = some gamma) (ha : a ∈ coefficients) :
    a.toComplex ∈ Rat⟮gamma.toComplex⟯ := by
  by_cases hzero : a.isZero = true
  · rw [(AlgebraicNumber.isZero_iff a).mp hzero]
    exact (Rat⟮gamma.toComplex⟯ : IntermediateField Rat ℂ).zero_mem
  have hnonzero : a.isZero = false := by
    cases h : a.isZero <;> simp_all
  let nonzero := coefficients.filter fun value => !value.isZero
  have haNonzero : a ∈ nonzero := by
    simp [nonzero, ha, hnonzero]
  unfold primitive? at hgamma
  change (nonzero[0]? >>= fun first =>
    nonzero.toList.drop 1 |>.foldlM extend? first) = some gamma at hgamma
  obtain ⟨first, hfirst, hfold⟩ :=
    Option.bind_eq_some_iff.mp hgamma
  have hfirstList : nonzero.toList[0]? = some first := by
    simpa using hfirst
  cases hlist : nonzero.toList with
  | nil => simp [hlist] at hfirstList
  | cons head tail =>
      have hhead : head = first := by
        simpa [hlist] using hfirstList
      subst head
      have haList : a ∈ first :: tail := by
        simpa [hlist] using Array.mem_toList_iff.mpr haNonzero
      have hfold' : tail.foldlM extend? first = some gamma := by
        simpa [hlist] using hfold
      obtain ⟨hfirstMem, htailMem⟩ :=
        primitiveFold_contains tail first gamma hfold'
      simp only [List.mem_cons] at haList
      rcases haList with haeq | haTail
      · subst a
        exact hfirstMem
      · exact htailMem a haTail

end Hex.AlgebraicPoly.Common
