/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.FactorGeneric.Yun

public section

/-!
# Totality and certificate replay of the raw factorization pipeline

Assembles the Yun and Trager pieces into whole-pipeline statements: the
squarefree-component factorizer and `Factor.factorRaw?` are total on valid
inputs, the executable irreducibility checker is characterised semantically,
and every produced raw factorization passes the executable certificate
replay `Factor.check`.
-/

namespace Hex.NumberTower

/-- Totality of the squarefree-component factorizer: on a certified
squarefree nonconstant input the bounded shift search and every recursive
call succeed, so `Factor.factorSquarefree?` returns a result. -/
theorem factorSquarefree_isSome :
    ∀ (levels : List Level) (hvalid : LevelsValid levels)
      (hinjective : LevelSemantics.DenoteInjective levels)
      (f : Array (Array Rat)),
      Norm.isSquarefree levels f →
      0 < (Factor.rawPoly levels f).degree?.getD 0 →
      (Factor.factorSquarefree? levels f).isSome := by
  intro levels
  induction levels with
  | nil =>
      intro hvalid hinjective f hcheck hdegree
      have hvalidEq : hvalid = (trivial : LevelsValid []) :=
        Subsingleton.elim _ _
      have hinjectiveEq : hinjective = LevelSemantics.DenoteInjective.nil :=
        Subsingleton.elim _ _
      subst hvalid
      subst hinjective
      letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil
      let ι := LevelSemantics.coeffHom [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil
      letI : CharZero (Arithmetic.Coeff []) :=
        { cast_injective := by
            intro m n hmn
            apply Nat.cast_injective (R := ℂ)
            have hmapped := congrArg ι hmn
            simpa only [map_natCast] using hmapped }
      have hsquarefree := squarefree_toPolynomial_of_check [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil f hcheck
      have hseparable :=
        (PerfectField.separable_iff_squarefree.mpr hsquarefree).map
          (f := LevelSemantics.coeffRatEquiv.toRingHom)
      rw [LevelSemantics.map_rawPoly_nil] at hseparable
      exact factorRat_isSome (Factor.toRatPoly f) hseparable
  | cons level lower ih =>
      intro hvalid hinjectiveTop f hcheck hdegree
      let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
      let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
        hinjectiveLower
      let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
        hinjectiveTop
      letI : Field (Arithmetic.Coeff lower) :=
        Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
      letI : Field (Arithmetic.Coeff (level :: lower)) :=
        Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
      have harrayDegree : 0 < f.size - 1 :=
        array_degree_pos_of_raw_degree_pos (level :: lower) f hdegree
      have hrawSquarefree := (Norm.isSquarefree_iff (level :: lower)
        hvalid hinjectiveTop hinvTop f).mp hcheck
      have hfindSome := Norm.findSquarefreeShift_isSome_of_injective
        level lower hvalid hinjectiveTop f harrayDegree hrawSquarefree
      obtain ⟨pair, hfind⟩ := Option.isSome_iff_exists.mp hfindSome
      rcases pair with ⟨shift, norm⟩
      have hnormCheck : Norm.isSquarefree lower norm :=
        findSquarefreeShift_squarefree level lower f hfind
      have hnormSquarefree : Squarefree
          (HexPolyMathlib.toPolynomial (Factor.rawPoly lower norm)) :=
        squarefree_toPolynomial_of_check lower hvalid.2.2 hinjectiveLower
          hinvLower norm hnormCheck
      have hnormEq : norm = Norm.oneLevel level lower f shift :=
        findSquarefreeShift_norm level lower f hfind
      have hnormDegree : 0 < (Factor.rawPoly lower norm).degree?.getD 0 := by
        rw [hnormEq]
        exact oneLevel_degree_pos level lower hvalid hinjectiveTop f shift
          hdegree (by simpa [hnormEq] using hnormSquarefree)
      have hlowerSome := ih hvalid.2.2 hinjectiveLower norm hnormCheck
        hnormDegree
      obtain ⟨lowerFactors, hlower⟩ :=
        Option.isSome_iff_exists.mp hlowerSome
      let factors := Factor.recover level lower shift f lowerFactors
      have hlowerSound : ∀ lowerFactor ∈ lowerFactors,
          Factor.polyCoords (Factor.rawPoly lower lowerFactor) = lowerFactor ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly lower lowerFactor)) := by
        exact factorSquarefree_mem_sound lower hvalid.2.2 hinjectiveLower norm
          hlower
      have htragerSquarefree : Squarefree
          (HexPolyMathlib.toPolynomial
            (tragerNorm level lower
              (Factor.rawPoly (level :: lower)
                (Factor.shiftTop level lower f shift)))) := by
        rw [tragerNorm_shiftTop level lower hvalid hinjectiveTop, ← hnormEq]
        exact hnormSquarefree
      have hfactorsSound : ∀ factor ∈ factors,
          Factor.polyCoords (Factor.rawPoly (level :: lower) factor) = factor ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) factor)) := by
        exact recover_mem_sound level lower hvalid hinjectiveTop f shift
          lowerFactors htragerSquarefree hlowerSound
      have hnormNe : Factor.rawPoly lower norm ≠ 0 := by
        intro hzero
        apply hnormSquarefree.ne_zero
        rw [hzero, HexPolyMathlib.toPolynomial_zero]
      have hlowerProduct := factorSquarefree_product lower hvalid.2.2
        hinjectiveLower norm hnormNe hlower
      have hfNe : Factor.rawPoly (level :: lower) f ≠ 0 := by
        intro hzero
        rw [hzero] at hdegree
        simp at hdegree
      have hfactorsProduct :
          (factors.toList.map fun factor => HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) factor)).prod =
            HexPolyMathlib.toPolynomial
              (Norm.monic (Factor.rawPoly (level :: lower) f)) := by
        exact recover_product level lower hvalid hinjectiveTop f norm shift
          lowerFactors hfNe hnormSquarefree hnormEq
            (fun lowerFactor hlowerFactor =>
              (hlowerSound lowerFactor hlowerFactor).1)
            hlowerProduct
            (fun factor hfactor => (hfactorsSound factor hfactor).2)
      have hfactorsDegree : factors.all (fun factor =>
          0 < (Factor.rawPoly (level :: lower) factor).degree?.getD 0) =
          true := by
        rw [Array.all_eq_true_iff_forall_mem]
        intro factor hfactor
        have hirreducible := (hfactorsSound factor hfactor).2
        have hnatDegree :
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) factor)).natDegree ≠ 0 := by
          intro hzero
          apply hirreducible.not_isUnit
          apply Polynomial.isUnit_iff_degree_eq_zero.mpr
          rw [Polynomial.degree_eq_natDegree hirreducible.ne_zero, hzero]
          rfl
        rw [HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
        exact decide_eq_true (Nat.pos_of_ne_zero hnatDegree)
      have hproduct : factors.foldl
          (fun product factor =>
            product * Factor.rawPoly (level :: lower) factor) 1 =
          Norm.monic (Factor.rawPoly (level :: lower) f) := by
        apply (HexPolyMathlib.equiv
          (R := Arithmetic.Coeff (level :: lower))).injective
        change HexPolyMathlib.toPolynomial
            (factors.foldl (fun product factor =>
              product * Factor.rawPoly (level :: lower) factor) 1) =
          HexPolyMathlib.toPolynomial
            (Norm.monic (Factor.rawPoly (level :: lower) f))
        rw [← Array.foldl_toList,
          rawFactorFoldl (level :: lower) hvalid hinjectiveTop hinvTop,
          hfactorsProduct]
        simp
      have hresult : Factor.factorSquarefree? (level :: lower) f =
          some factors := by
        simp only [Factor.factorSquarefree?, hcheck, if_true]
        rw [hfind]
        change (do
          let lowerFactors ← Factor.factorSquarefree? lower norm
          let factors' := Factor.recover level lower shift f lowerFactors
          let p := Norm.monic (Factor.rawPoly (level :: lower) f)
          let product := factors'.foldl (fun product factor =>
            product * Factor.rawPoly (level :: lower) factor) 1
          if factors'.all (fun factor =>
              0 < (Factor.rawPoly (level :: lower) factor).degree?.getD 0) &&
              product = p then some factors' else none) = some factors
        rw [hlower]
        change (if factors.all (fun factor =>
            0 < (Factor.rawPoly (level :: lower) factor).degree?.getD 0) &&
            factors.foldl (fun product factor =>
              product * Factor.rawPoly (level :: lower) factor) 1 =
              Norm.monic (Factor.rawPoly (level :: lower) f) then
            some factors else none) = some factors
        rw [hfactorsDegree, hproduct]
        simp
      exact Option.isSome_iff_exists.mpr ⟨factors, hresult⟩

private theorem list_foldlM_isSome {A B : Type*}
    {step : B → A → Option B} {items : List A} (init : B)
    (hstep : ∀ state item, item ∈ items → (step state item).isSome) :
    (items.foldlM step init).isSome := by
  induction items generalizing init with
  | nil => simp
  | cons item items ih =>
      obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp
        (hstep init item (by simp))
      rw [List.foldlM_cons, hnext]
      exact ih next fun state tail htail =>
        hstep state tail (by simp [htail])

private theorem array_foldlM_isSome {A B : Type*}
    {step : B → A → Option B} {items : Array A} (init : B)
    (hstep : ∀ state item, item ∈ items.toList →
      (step state item).isSome) :
    (items.foldlM step init).isSome := by
  rw [← Array.foldlM_toList]
  exact list_foldlM_isSome init hstep

private theorem ratListLess_iff : ∀ a b : List Rat,
    Factor.ratListLess a b = true ↔ a < b := by
  intro a
  induction a with
  | nil =>
      intro b
      cases b <;> simp [Factor.ratListLess, List.lt_iff_lex_lt]
  | cons a as ih =>
      intro b
      cases b with
      | nil => simp [Factor.ratListLess, List.lt_iff_lex_lt]
      | cons b bs =>
          by_cases hab : a < b
          · rw [Factor.ratListLess, if_pos hab]
            constructor
            · intro _
              exact List.Lex.rel hab
            · intro _
              rfl
          · rw [Factor.ratListLess, if_neg hab]
            by_cases hba : b < a
            · rw [if_pos hba]
              constructor
              · intro hfalse
                contradiction
              · intro hlt
                exact ((not_le_of_gt hba) (List.head_le_of_lt hlt)).elim
            · rw [if_neg hba]
              have heq : a = b :=
                le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
              subst b
              rw [ih]
              constructor
              · exact List.Lex.cons
              · intro hlt
                cases hlt with
                | rel haa => exact (lt_irrefl a haa).elim
                | cons htail => exact htail

private theorem flattenList_injective : Function.Injective
    (fun f : List (Array Rat) =>
      f.flatMap fun coefficient =>
        (coefficient.size : Rat) :: coefficient.toList) := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons coefficient tail => simp at h
  | cons coefficient tail ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons other rest =>
          simp only [List.flatMap_cons, List.cons_append] at h
          have hhead : (coefficient.size : Rat) = other.size :=
            (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          have hsize : coefficient.size = other.size := by
            exact_mod_cast hhead
          have hlength : coefficient.toList.length = other.toList.length := by
            simpa using hsize
          obtain ⟨hcoefficient, hrest⟩ :=
            List.append_inj htail hlength
          have harray : coefficient = other :=
            Array.toList_inj.mp hcoefficient
          subst other
          have htailEq : tail = rest := ih hrest
          subst rest
          rfl

private theorem flattenPoly_injective :
    Function.Injective Factor.flattenPoly := by
  intro a b h
  apply Array.toList_inj.mp
  apply flattenList_injective
  simpa only [Factor.flattenPoly] using h

private theorem factorLess_iff (a b : Array (Array Rat)) :
    Factor.factorLess a b = true ↔
      Factor.flattenPoly a < Factor.flattenPoly b := by
  exact ratListLess_iff _ _

private theorem factor_eq_of_not_less {a b : Array (Array Rat)}
    (hab : Factor.factorLess a b ≠ true)
    (hba : Factor.factorLess b a ≠ true) : a = b := by
  apply flattenPoly_injective
  apply le_antisymm
  · exact le_of_not_gt fun hlt => hba ((factorLess_iff b a).mpr hlt)
  · exact le_of_not_gt fun hlt => hab ((factorLess_iff a b).mpr hlt)

private theorem factorLess_trans {a b c : Array (Array Rat)}
    (hab : Factor.factorLess a b = true)
    (hbc : Factor.factorLess b c = true) :
    Factor.factorLess a c = true :=
  (factorLess_iff a c).mpr
    (lt_trans ((factorLess_iff a b).mp hab)
      ((factorLess_iff b c).mp hbc))

private def FactorEntryLess
    (a b : Array (Array Rat) × Nat) : Prop :=
  Factor.factorLess a.1 b.1 = true

private theorem insertFactor_fst_mem
    (factor entry : Array (Array Rat) × Nat) :
    ∀ factors : List (Array (Array Rat) × Nat),
      entry ∈ Factor.insertFactor factor factors →
      entry.1 = factor.1 ∨
        ∃ original ∈ factors, entry.1 = original.1 := by
  intro factors
  induction factors with
  | nil =>
      intro hentry
      have heq : entry = factor := by
        simpa [Factor.insertFactor] using hentry
      subst entry
      exact Or.inl rfl
  | cons head tail ih =>
      intro hentry
      by_cases hfactor : Factor.factorLess factor.1 head.1 = true
      · rw [Factor.insertFactor, if_pos hfactor] at hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact Or.inl rfl
        · exact Or.inr ⟨entry, hentry, rfl⟩
      · rw [Factor.insertFactor, if_neg hfactor] at hentry
        by_cases hhead : Factor.factorLess head.1 factor.1 = true
        · rw [if_pos hhead] at hentry
          rcases List.mem_cons.mp hentry with hentryHead | hentry
          · subst entry
            exact Or.inr ⟨head, by simp, rfl⟩
          · rcases ih hentry with hfactorEq | ⟨original, horiginal, heq⟩
            · exact Or.inl hfactorEq
            · exact Or.inr ⟨original, by simp [horiginal], heq⟩
        · rw [if_neg hhead] at hentry
          rcases List.mem_cons.mp hentry with hentry | hentry
          · subst entry
            exact Or.inr ⟨head, by simp, rfl⟩
          · exact Or.inr ⟨entry, by simp [hentry], rfl⟩

private theorem insertFactor_pairwise
    (factor : Array (Array Rat) × Nat) :
    ∀ factors : List (Array (Array Rat) × Nat),
      factors.Pairwise FactorEntryLess →
      (Factor.insertFactor factor factors).Pairwise FactorEntryLess := by
  intro factors
  induction factors with
  | nil => simp [Factor.insertFactor]
  | cons head tail ih =>
      intro hsorted
      have hhead := (List.pairwise_cons.mp hsorted).1
      have htail := (List.pairwise_cons.mp hsorted).2
      by_cases hfactor : Factor.factorLess factor.1 head.1 = true
      · rw [Factor.insertFactor, if_pos hfactor,
          List.pairwise_cons]
        refine ⟨?_, hsorted⟩
        intro other hother
        rcases List.mem_cons.mp hother with rfl | hother
        · exact hfactor
        · exact factorLess_trans hfactor (hhead other hother)
      · rw [Factor.insertFactor, if_neg hfactor]
        by_cases hheadFactor : Factor.factorLess head.1 factor.1 = true
        · rw [if_pos hheadFactor, List.pairwise_cons]
          refine ⟨?_, ih htail⟩
          intro other hother
          rcases insertFactor_fst_mem factor other tail hother with
            hfactorEq | ⟨original, horiginal, horiginalEq⟩
          · unfold FactorEntryLess
            rw [hfactorEq]
            exact hheadFactor
          · unfold FactorEntryLess
            rw [horiginalEq]
            exact hhead original horiginal
        · rw [if_neg hheadFactor, List.pairwise_cons]
          refine ⟨?_, htail⟩
          intro other hother
          exact hhead other hother

private theorem foldl_insertFactor_pairwise
    (items state : List (Array (Array Rat) × Nat))
    (hstate : state.Pairwise FactorEntryLess) :
    (items.foldl (fun out factor => Factor.insertFactor factor out) state).Pairwise
      FactorEntryLess := by
  induction items generalizing state with
  | nil => simpa using hstate
  | cons factor items ih =>
      rw [List.foldl_cons]
      exact ih _ (insertFactor_pairwise factor state hstate)

private theorem canonicalFactors_pairwise
    (factors : Array (Array (Array Rat) × Nat)) :
    (Factor.canonicalFactors factors).toList.Pairwise FactorEntryLess := by
  simpa [Factor.canonicalFactors] using
    foldl_insertFactor_pairwise factors.toList [] (by simp)

private theorem canonicalFactors_sorted
    (factors : Array (Array (Array Rat) × Nat)) :
    Factor.factorsSorted (Factor.canonicalFactors factors) = true := by
  simp only [Factor.factorsSorted, decide_eq_true_eq]
  exact canonicalFactors_pairwise factors

private theorem insertFactor_preserves
    (P : Array (Array Rat) → Prop)
    (factor : Array (Array Rat) × Nat) (hfactor : P factor.1)
    (factors : List (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, P entry.1) :
    ∀ entry ∈ Factor.insertFactor factor factors, P entry.1 := by
  intro entry hentry
  rcases insertFactor_fst_mem factor entry factors hentry with
    hfactorEq | ⟨original, horiginal, horiginalEq⟩
  · rw [hfactorEq]
    exact hfactor
  · rw [horiginalEq]
    exact hfactors original horiginal

private theorem foldl_insertFactor_preserves
    (P : Array (Array Rat) → Prop)
    (items state : List (Array (Array Rat) × Nat))
    (hitems : ∀ entry ∈ items, P entry.1)
    (hstate : ∀ entry ∈ state, P entry.1) :
    ∀ entry ∈ items.foldl
      (fun out factor => Factor.insertFactor factor out) state,
      P entry.1 := by
  induction items generalizing state with
  | nil => simpa using hstate
  | cons factor items ih =>
      rw [List.foldl_cons]
      apply ih
      · intro entry hentry
        exact hitems entry (by simp [hentry])
      · exact insertFactor_preserves P factor
          (hitems factor (by simp)) state hstate

private theorem canonicalFactors_preserves
    (P : Array (Array Rat) → Prop)
    (factors : Array (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, P entry.1) :
    ∀ entry ∈ Factor.canonicalFactors factors, P entry.1 := by
  intro entry hentry
  apply foldl_insertFactor_preserves P factors.toList []
  · intro original horiginal
    exact hfactors original (Array.mem_toList_iff.mp horiginal)
  · simp
  · simpa [Factor.canonicalFactors] using hentry

private theorem insertFactor_positive
    (factor : Array (Array Rat) × Nat) (hfactor : 0 < factor.2)
    (factors : List (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, 0 < entry.2) :
    ∀ entry ∈ Factor.insertFactor factor factors, 0 < entry.2 := by
  induction factors with
  | nil => simpa [Factor.insertFactor] using hfactor
  | cons head tail ih =>
      intro entry hentry
      have hhead : 0 < head.2 := hfactors head (by simp)
      have htail : ∀ original ∈ tail, 0 < original.2 := by
        intro original horiginal
        exact hfactors original (by simp [horiginal])
      by_cases hfactorHead : Factor.factorLess factor.1 head.1 = true
      · rw [Factor.insertFactor, if_pos hfactorHead] at hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact hfactor
        · exact hfactors entry hentry
      · rw [Factor.insertFactor, if_neg hfactorHead] at hentry
        by_cases hheadFactor : Factor.factorLess head.1 factor.1 = true
        · rw [if_pos hheadFactor] at hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact hhead
          · exact ih htail entry hentry
        · rw [if_neg hheadFactor] at hentry
          rcases List.mem_cons.mp hentry with hentry | hentry
          · subst entry
            omega
          · exact htail entry hentry

private theorem foldl_insertFactor_positive
    (items state : List (Array (Array Rat) × Nat))
    (hitems : ∀ entry ∈ items, 0 < entry.2)
    (hstate : ∀ entry ∈ state, 0 < entry.2) :
    ∀ entry ∈ items.foldl
      (fun out factor => Factor.insertFactor factor out) state,
      0 < entry.2 := by
  induction items generalizing state with
  | nil => simpa using hstate
  | cons factor items ih =>
      rw [List.foldl_cons]
      apply ih
      · intro entry hentry
        exact hitems entry (by simp [hentry])
      · exact insertFactor_positive factor (hitems factor (by simp))
          state hstate

private theorem canonicalFactors_positive
    (factors : Array (Array (Array Rat) × Nat))
    (hfactors : ∀ entry ∈ factors, 0 < entry.2) :
    ∀ entry ∈ Factor.canonicalFactors factors, 0 < entry.2 := by
  intro entry hentry
  apply foldl_insertFactor_positive factors.toList []
  · intro original horiginal
    exact hfactors original (Array.mem_toList_iff.mp horiginal)
  · simp
  · simpa [Factor.canonicalFactors] using hentry

private theorem insertFactor_prod {M : Type*} [CommMonoid M]
    (value : Array (Array Rat) → M)
    (factor : Array (Array Rat) × Nat) :
    ∀ factors : List (Array (Array Rat) × Nat),
      ((Factor.insertFactor factor factors).map fun entry =>
        value entry.1 ^ entry.2).prod =
      (factors.map fun entry => value entry.1 ^ entry.2).prod *
        value factor.1 ^ factor.2 := by
  intro factors
  induction factors with
  | nil => simp [Factor.insertFactor]
  | cons head tail ih =>
      by_cases hfactorHead : Factor.factorLess factor.1 head.1 = true
      · simp [Factor.insertFactor, hfactorHead, mul_assoc, mul_comm,
          mul_left_comm]
      · by_cases hheadFactor : Factor.factorLess head.1 factor.1 = true
        · simp [Factor.insertFactor, hfactorHead, hheadFactor, ih,
            mul_assoc, mul_comm, mul_left_comm]
        · have heq : head.1 = factor.1 :=
            factor_eq_of_not_less hheadFactor hfactorHead
          have hirrefl :
              Factor.factorLess factor.1 factor.1 ≠ true := by
            intro hless
            exact (lt_irrefl _ ((factorLess_iff factor.1 factor.1).mp
              hless))
          simp [Factor.insertFactor, heq, hirrefl,
            pow_add, mul_assoc, mul_comm, mul_left_comm]

private theorem foldl_insertFactor_prod {M : Type*} [CommMonoid M]
    (value : Array (Array Rat) → M)
    (items state : List (Array (Array Rat) × Nat)) :
    ((items.foldl (fun out factor => Factor.insertFactor factor out) state).map
        fun entry => value entry.1 ^ entry.2).prod =
      (state.map fun entry => value entry.1 ^ entry.2).prod *
        (items.map fun entry => value entry.1 ^ entry.2).prod := by
  induction items generalizing state with
  | nil => simp
  | cons factor items ih =>
      rw [List.foldl_cons, ih, insertFactor_prod]
      simp only [List.map_cons, List.prod_cons]
      ac_rfl

private theorem canonicalFactors_prod {M : Type*} [CommMonoid M]
    (value : Array (Array Rat) → M)
    (factors : Array (Array (Array Rat) × Nat)) :
    ((Factor.canonicalFactors factors).toList.map fun entry =>
        value entry.1 ^ entry.2).prod =
      (factors.toList.map fun entry => value entry.1 ^ entry.2).prod := by
  simpa [Factor.canonicalFactors] using
    foldl_insertFactor_prod value factors.toList []

private theorem factorRat_mem_monic (input : DensePoly Rat)
    {factors : Array (Array (Array Rat))}
    (hresult : Factor.factorRat? input = some factors) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    ∀ factor ∈ factors,
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly [] factor)).Monic := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  intro factor hfactor
  simp only [Factor.factorRat?] at hresult
  split at hresult
  · cases hresult
    simp at hfactor
  · split at hresult
    · cases hresult
      simp at hfactor
    · split at hresult
      · split at hresult
        · cases hresult
          rename_i hinputZero hpZero hgcd hproduct
          obtain ⟨rawFactor, hrawFactor, rfl⟩ := Array.mem_map.mp hfactor
          have hrawList := Array.mem_toList_iff.mpr hrawFactor
          simp only [Array.toList_flatMap, List.mem_flatMap] at hrawList
          obtain ⟨entry, hentryList, hrawReplicate⟩ := hrawList
          have hrawEq : rawFactor = entry.1 := by
            have hrep : entry.2 ≠ 0 ∧ rawFactor = entry.1 := by
              simpa using hrawReplicate
            exact hrep.2
          subst rawFactor
          have hentry : entry ∈
              (ZPoly.factorize
                (ZPoly.ratPolyPrimitivePart
                  (DensePoly.scale input.leadingCoeff⁻¹ input))).factors :=
            Array.mem_toList_iff.mp hentryList
          have hentryNe : entry.1 ≠ 0 :=
            (HexBerlekampZassenhausMathlib.factorize_irreducible_of_nonUnit
              (ZPoly.ratPolyPrimitivePart
                (DensePoly.scale input.leadingCoeff⁻¹ input))
              entry hentry).not_zero
          let q := DensePoly.scale entry.1.toRatPoly.leadingCoeff⁻¹
            entry.1.toRatPoly
          have hqMonic : (HexPolyMathlib.toPolynomial q).Monic :=
            toPolynomial_scale_inv_monic entry.1.toRatPoly
              (toRatPoly_ne_zero hentryNe)
          apply Polynomial.monic_of_injective
            (f := LevelSemantics.coeffRatEquiv.toRingHom)
            LevelSemantics.coeffRatEquiv.injective
          rw [LevelSemantics.map_rawPoly_nil, toRatPoly_ofRatPoly]
          exact hqMonic
        · cases hresult
      · cases hresult

private theorem factorSquarefree_mem_monic
    (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) {factors : Array (Array (Array Rat))}
    (hresult : Factor.factorSquarefree? levels f = some factors) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    ∀ factor ∈ factors,
      (HexPolyMathlib.toPolynomial
        (Factor.rawPoly levels factor)).Monic := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  intro factor hfactor
  cases levels with
  | nil =>
      exact factorRat_mem_monic (Factor.toRatPoly f) hresult factor hfactor
  | cons level lower =>
      have hfull := hresult
      simp only [Factor.factorSquarefree?] at hresult
      split at hresult
      · rename_i hinputSquarefree
        obtain ⟨pair, hfind, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        rcases pair with ⟨shift, norm⟩
        obtain ⟨lowerFactors, hlower, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        split at hresult
        · cases hresult
          obtain ⟨lowerFactor, hlowerFactor, hdegree, hrecovered⟩ :=
            recover_mem level lower shift f lowerFactors hfactor
          let common := Norm.monic
            (DensePoly.gcd
              (Factor.rawPoly (level :: lower)
                (Factor.shiftTop level lower f shift))
              (Factor.rawPoly (level :: lower)
                (Factor.embedLower level lower lowerFactor)))
          let unshifted := Factor.rawPoly (level :: lower)
            (Factor.shiftTop level lower (Factor.polyCoords common) (-shift))
          have hrawEq : Factor.rawPoly (level :: lower) factor =
              Norm.monic unshifted := by
            rw [← hrecovered, rawPoly_polyCoords]
          have hirreducible :=
            (factorSquarefree_mem_sound (level :: lower) hvalid hinjective f
              hfull factor hfactor).2
          have hunshifted : unshifted ≠ 0 := by
            intro hzero
            apply hirreducible.ne_zero
            rw [hrawEq, hzero]
            simp [Norm.monic]
          rw [hrawEq]
          exact toPolynomial_monic_monic (level :: lower) hvalid
            hinjective hinv unshifted hunshifted
        · contradiction
      · contradiction

private theorem foldl_push_labeled
    (factors : Array (Array (Array Rat)))
    (state : Array (Array (Array Rat) × Nat)) (multiplicity : Nat) :
    factors.foldl
      (fun out factor => out.push (factor, multiplicity)) state =
      state ++ factors.map fun factor => (factor, multiplicity) := by
  rw [Array.foldl_push_eq_append (stop := factors.size) rfl]

private theorem labeled_prod_pow {A M : Type*} [CommMonoid M]
    (value : A → M) (items : List A) (n : Nat) :
    ((items.map fun item => (item, n)).map fun entry =>
      value entry.1 ^ entry.2).prod = (items.map value).prod ^ n := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.prod_cons, ih, Prod.fst, Prod.snd]
      exact (_root_.mul_pow (value item) (List.map value items).prod n).symm

private theorem factorFold_sound
    (levels : List Level) (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat))
    (components : List (Array (Array Rat) × Nat))
    (hcomponents : ∀ component ∈ components,
      component ∈ (Factor.yunRaw levels f).toList)
    (state out : Array (Array (Array Rat) × Nat))
    (hfold : components.foldlM (Factor.appendComponent? levels) state =
      some out) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    (∀ entry ∈ state,
      Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)).Monic ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)) ∧
        0 < entry.2) →
    (∀ entry ∈ out,
      Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
        (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)).Monic ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1)) ∧
        0 < entry.2) ∧
      (out.toList.map fun entry =>
        HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels entry.1) ^ entry.2).prod =
        (state.toList.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod *
          (components.map fun component =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) ^ component.2).prod := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  intro hstate
  induction components generalizing state with
  | nil =>
      simp only [List.foldlM_nil, Option.pure_def,
        Option.some.injEq] at hfold
      subst out
      exact ⟨hstate, by simp⟩
  | cons component components ih =>
      rw [List.foldlM_cons] at hfold
      obtain ⟨next, hnext, htail⟩ :=
        Option.bind_eq_some_iff.mp hfold
      simp only [Factor.appendComponent?] at hnext
      obtain ⟨irreducibles, hirreducibles, hnext⟩ :=
        Option.bind_eq_some_iff.mp hnext
      rw [foldl_push_labeled] at hnext
      simp only [Option.pure_def, Option.some.injEq] at hnext
      subst next
      have hcomponentMem : component ∈
          (Factor.yunRaw levels f).toList :=
        hcomponents component (by simp)
      have hpositive := yun_positive hvalid hinjective hinv f component
        hcomponentMem
      have hrawNe : Factor.rawPoly levels component.1 ≠ 0 := by
        intro hzero
        rw [hzero] at hpositive
        simp at hpositive
      have hcomponentMonic :
          (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels component.1)).Monic := by
        rw [Polynomial.Monic.def,
          HexPolyMathlib.leadingCoeff_toPolynomial]
        exact yun_monic hvalid hinjective hinv f component hcomponentMem
      have hnormalized :
          Norm.monic (Factor.rawPoly levels component.1) =
            Factor.rawPoly levels component.1 :=
        monic_eq_self levels hvalid hinjective hinv _ hcomponentMonic
      have hirreducibleProduct :
          (irreducibles.toList.map fun factor =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels factor)).prod =
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) := by
        rw [← hnormalized]
        exact factorSquarefree_product levels hvalid hinjective component.1
          hrawNe hirreducibles
      have hnextSound : ∀ entry ∈
          state ++ irreducibles.map fun factor => (factor, component.2),
          Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels entry.1)).Monic ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels entry.1)) ∧
            0 < entry.2 := by
        intro entry hentry
        rw [Array.mem_append] at hentry
        rcases hentry with hentry | hentry
        · exact hstate entry hentry
        · obtain ⟨factor, hfactor, rfl⟩ := Array.mem_map.mp hentry
          have hsound := factorSquarefree_mem_sound levels hvalid hinjective
            component.1 hirreducibles factor hfactor
          have hmonic := factorSquarefree_mem_monic levels hvalid hinjective
            component.1 hirreducibles factor hfactor
          exact ⟨hsound.1, hmonic, hsound.2, hpositive.2⟩
      have hnextProduct :
          ((state ++ irreducibles.map fun factor =>
              (factor, component.2)).toList.map fun entry =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels entry.1) ^ entry.2).prod =
            (state.toList.map fun entry =>
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly levels entry.1) ^ entry.2).prod *
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly levels component.1) ^ component.2 := by
        rw [Array.toList_append, Array.toList_map, List.map_append,
          List.prod_append]
        congr 1
        have hlabels := labeled_prod_pow
          (fun factor : Array (Array Rat) =>
            HexPolyMathlib.toPolynomial (Factor.rawPoly levels factor))
          irreducibles.toList component.2
        rw [hirreducibleProduct] at hlabels
        exact hlabels
      have htailComponents : ∀ tail ∈ components,
          tail ∈ (Factor.yunRaw levels f).toList := by
        intro tail htailMem
        exact hcomponents tail (by simp [htailMem])
      have hind := ih htailComponents
        (state ++ irreducibles.map fun factor => (factor, component.2))
        htail hnextSound
      refine ⟨hind.1, ?_⟩
      rw [hind.2, hnextProduct]
      simp only [List.map_cons, List.prod_cons]
      ring

/-- The complete raw Yun/Trager factorization pipeline cannot fail when
coefficient denotation is injective. -/
theorem factorRaw_isSome (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) :
    (Factor.factorRaw? levels f).isSome := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let components := Factor.yunRaw levels f
  have hcheck : Factor.checkYun levels f components :=
    checkYun_yunRaw hvalid hinjective hinv f
  let step := fun (out : Array (Array (Array Rat) × Nat))
      (component : Array (Array Rat) × Nat) => do
    let irreducibles ← Factor.factorSquarefree? levels component.1
    pure <| irreducibles.foldl
      (fun (out : Array (Array (Array Rat) × Nat))
        (factor : Array (Array Rat)) => out.push (factor, component.2)) out
  have hfold : (components.foldlM step #[]).isSome := by
    apply array_foldlM_isSome #[]
    intro out component hcomponent
    have hsquarefree := yun_squarefree hvalid hinjective hinv f
      (by
        by_cases hzero : (Factor.rawPoly levels f).degree?.getD 0 = 0
        · have hempty : components = #[] := by
            simp [components, Factor.yunRaw, hzero]
          rw [hempty] at hcomponent
          simp at hcomponent
        · exact Nat.pos_of_ne_zero hzero)
      component hcomponent
    have hdegree :=
      (yun_positive hvalid hinjective hinv f component hcomponent).1
    have hsome := factorSquarefree_isSome levels hvalid hinjective
      component.1 hsquarefree hdegree
    obtain ⟨irreducibles, hirreducibles⟩ :=
      Option.isSome_iff_exists.mp hsome
    exact Option.isSome_iff_exists.mpr ⟨irreducibles.foldl
      (fun (out : Array (Array (Array Rat) × Nat))
        (factor : Array (Array Rat)) => out.push (factor, component.2)) out, by
      simp only [step]
      rw [hirreducibles]
      rfl⟩
  obtain ⟨factors, hfactors⟩ := Option.isSome_iff_exists.mp hfold
  unfold Factor.factorRaw?
  dsimp only
  rw [show Factor.checkYun levels f (Factor.yunRaw levels f) = true by
    simpa only [components] using hcheck]
  change (do
    let factors' ← components.foldlM step #[]
    some (Factor.RawFactorization.mk
      (Factor.rawPoly levels f).leadingCoeff.data
      (Factor.canonicalFactors factors'))).isSome
  rw [hfactors]
  simp

/-- Over the empty tower the executable irreducibility checker accepts
exactly the monic inputs whose interpretation is irreducible. -/
theorem isIrreducible_nil_iff (f : Array (Array Rat)) :
    letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
      LevelSemantics.DenoteInjective.nil
      LevelSemantics.coeffDenote_inv_nil
    Factor.isIrreducible [] f ↔
      (Factor.rawPoly [] f).leadingCoeff = 1 ∧
        Irreducible (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)) := by
  letI : Field (Arithmetic.Coeff []) := Norm.coeffFieldPoly [] trivial
    LevelSemantics.DenoteInjective.nil
    LevelSemantics.coeffDenote_inv_nil
  constructor
  · intro hcheck
    have hcheckRaw := hcheck
    simp only [Factor.isIrreducible, Bool.and_eq_true] at hcheck
    exact ⟨of_decide_eq_true hcheck.1.1.2,
      LevelSemantics.isIrreducible_nil_toMathlib f hcheckRaw⟩
  · rintro ⟨hmonic, hirreducible⟩
    have hdegree : 0 < (Factor.rawPoly [] f).degree?.getD 0 := by
      have hne := hirreducible.ne_zero
      have hnatDegree :
          (HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).natDegree ≠ 0 := by
        intro hzero
        apply hirreducible.not_isUnit
        apply Polynomial.isUnit_iff_degree_eq_zero.mpr
        rw [Polynomial.degree_eq_natDegree hne, hzero]
        rfl
      rw [HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
      omega
    have hsquarefree : Norm.isSquarefree [] f := by
      apply (Norm.isSquarefree_iff [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil f).mpr
      letI : CharZero (Arithmetic.Coeff []) :=
        { cast_injective := by
            intro m n hmn
            apply Nat.cast_injective (R := ℂ)
            have hmapped := congrArg
              (LevelSemantics.coeffHom [] trivial
                LevelSemantics.DenoteInjective.nil
                LevelSemantics.coeffDenote_inv_nil) hmn
            simpa using hmapped }
      have hseparable := hirreducible.separable
      have hmapped := hseparable.map
        (f := LevelSemantics.coeffHom [] trivial
          LevelSemantics.DenoteInjective.nil
          LevelSemantics.coeffDenote_inv_nil)
      rw [← Norm.rawPolynomialHom_apply [] trivial
        LevelSemantics.DenoteInjective.nil
        LevelSemantics.coeffDenote_inv_nil]
      exact hmapped.squarefree
    let raw := Factor.toRatPoly f
    let primitive := ZPoly.ratPolyPrimitivePart raw
    have hirreducibleRaw :
        Irreducible (HexPolyMathlib.toPolynomial raw) := by
      have hmapped := (MulEquiv.irreducible_iff
        (f := (Polynomial.mapEquiv
          LevelSemantics.coeffRatEquiv).toMulEquiv)).mpr hirreducible
      change Irreducible
        ((HexPolyMathlib.toPolynomial (Factor.rawPoly [] f)).map
          LevelSemantics.coeffRatEquiv.toRingHom) at hmapped
      rw [LevelSemantics.map_rawPoly_nil] at hmapped
      exact hmapped
    obtain ⟨unit, hunit⟩ :=
      ZPoly.ratPolyPrimitivePart_rational_associate raw
    have hunitNe : unit ≠ 0 := by
      intro hzero
      apply hirreducibleRaw.ne_zero
      rw [hunit, hzero]
      simp
    have hassociate : HexPolyMathlib.toPolynomial raw =
        Polynomial.C unit * HexPolyZMathlib.toPolyℚ primitive := by
      rw [hunit, HexPolyMathlib.toPolynomial_scale,
        HexPolyZMathlib.toPolynomial_toRatPoly]
    have hirreducibleRat :
        Irreducible (HexPolyZMathlib.toPolyℚ primitive) := by
      rw [hassociate, mul_comm] at hirreducibleRaw
      exact (irreducible_mul_isUnit
        (Polynomial.isUnit_C.mpr hunitNe.isUnit)).mp hirreducibleRaw
    have hprimitiveNe : primitive ≠ 0 := by
      intro hzero
      apply hirreducibleRat.ne_zero
      rw [hzero]
      change (HexPolyZMathlib.toPolynomial 0).map
        (Int.castRingHom ℚ) = 0
      rw [HexPolyZMathlib.toPolynomial_zero, Polynomial.map_zero]
    have hprimitive :
        (HexPolyZMathlib.toPolynomial primitive).IsPrimitive :=
      HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive primitive
        (ZPoly.ratPolyPrimitivePart_primitive raw
          (HexPolyZMathlib.content_ne_zero primitive hprimitiveNe))
    have hirreducibleInt :
        Irreducible (HexPolyZMathlib.toPolynomial primitive) :=
      (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
        hprimitive).mpr hirreducibleRat
    have hchecker : ZPoly.isIrreducible primitive = true :=
      (ZPoly.isIrreducible_iff primitive).mpr
        ((ZPoly.Irreducible_iff_polynomialIrreducible primitive).mpr
          hirreducibleInt)
    simp only [Factor.isIrreducible, Bool.and_eq_true]
    exact ⟨⟨⟨of_decide_eq_true (by simpa using hdegree),
      of_decide_eq_true (by simpa using hmonic)⟩, hsquarefree⟩, hchecker⟩

private theorem list_eq_singleton_of_prod_irreducible
    {R : Type*} [CommMonoidWithZero R] (items : List R)
    (hnonunit : ∀ item ∈ items, ¬ IsUnit item)
    (hprod : Irreducible items.prod) : ∃ item, items = [item] := by
  cases items with
  | nil =>
      simpa using hprod.not_isUnit
  | cons item tail =>
      cases tail with
      | nil => exact ⟨item, rfl⟩
      | cons next rest =>
          exfalso
          rcases hprod.isUnit_or_isUnit rfl with hitem | htail
          · exact (hnonunit item (by simp)) hitem
          · have hnextDvd : next ∣ (next :: rest).prod := by
              exact dvd_mul_right next rest.prod
            have hnextUnit : IsUnit next :=
              isUnit_iff_dvd_one.mpr
                (hnextDvd.trans (isUnit_iff_dvd_one.mp htail))
            exact (hnonunit next (by simp)) hnextUnit

/-- With coefficient-denotation injectivity supplied explicitly, the recursive
Boolean checker is exactly monic polynomial irreducibility.  This generic form
breaks the logical cycle used when validating the tower itself. -/
theorem isIrreducible_iff_of_injective (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat)) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Factor.isIrreducible levels f ↔
      (Factor.rawPoly levels f).leadingCoeff = 1 ∧
        Irreducible (HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels f)) := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  cases levels with
  | nil =>
      have hvalidEq : hvalid = (trivial : LevelsValid []) :=
        Subsingleton.elim _ _
      have hinjectiveEq : hinjective = LevelSemantics.DenoteInjective.nil :=
        Subsingleton.elim _ _
      subst hvalid
      subst hinjective
      exact isIrreducible_nil_iff f
  | cons level lower =>
      constructor
      · intro hchecker
        have hparts := hchecker
        simp only [Factor.isIrreducible, Bool.and_eq_true] at hparts
        refine ⟨of_decide_eq_true hparts.1.1.2, ?_⟩
        split at hparts
        · rename_i factors hresult
          have hfactors : factors =
              #[Factor.polyCoords (Factor.rawPoly (level :: lower) f)] :=
            of_decide_eq_true hparts.2
          have hmember : Factor.polyCoords
              (Factor.rawPoly (level :: lower) f) ∈ factors := by
            rw [hfactors]
            simp
          have hsound := factorSquarefree_mem_sound (level :: lower) hvalid
            hinjective f hresult _ hmember
          rw [rawPoly_polyCoords] at hsound
          exact hsound.2
        · simp at hparts
      · rintro ⟨hmonic, hirreducible⟩
        have hdegree :
            0 < (Factor.rawPoly (level :: lower) f).degree?.getD 0 := by
          have hnatDegree : (HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) f)).natDegree ≠ 0 := by
            intro hzero
            apply hirreducible.not_isUnit
            apply Polynomial.isUnit_iff_degree_eq_zero.mpr
            rw [Polynomial.degree_eq_natDegree hirreducible.ne_zero, hzero]
            rfl
          rw [HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
          exact Nat.pos_of_ne_zero hnatDegree
        let ι := LevelSemantics.coeffHom (level :: lower) hvalid
          hinjective hinv
        letI : CharZero (Arithmetic.Coeff (level :: lower)) :=
          { cast_injective := by
              intro m n hmn
              apply Nat.cast_injective (R := ℂ)
              have hmapped := congrArg ι hmn
              simpa only [map_natCast] using hmapped }
        have hsquarefree : Norm.isSquarefree (level :: lower) f := by
          apply (Norm.isSquarefree_iff (level :: lower) hvalid hinjective
            hinv f).mpr
          have hseparable := hirreducible.separable.map (f := ι)
          rw [← Norm.rawPolynomialHom_apply (level :: lower) hvalid
            hinjective hinv]
          exact hseparable.squarefree
        have hsome := factorSquarefree_isSome (level :: lower) hvalid
          hinjective f hsquarefree hdegree
        obtain ⟨factors, hresult⟩ := Option.isSome_iff_exists.mp hsome
        have hsound : ∀ factor ∈ factors,
            Factor.polyCoords
                (Factor.rawPoly (level :: lower) factor) = factor ∧
              Irreducible (HexPolyMathlib.toPolynomial
                (Factor.rawPoly (level :: lower) factor)) :=
          factorSquarefree_mem_sound (level :: lower) hvalid hinjective f
            hresult
        have hfNe : Factor.rawPoly (level :: lower) f ≠ 0 := by
          intro hzero
          apply hirreducible.ne_zero
          rw [hzero, HexPolyMathlib.toPolynomial_zero]
        have hproduct := factorSquarefree_product (level :: lower) hvalid
          hinjective f hfNe hresult
        have hmonicPoly : (HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) f)).Monic := by
          rw [Polynomial.Monic.def,
            HexPolyMathlib.leadingCoeff_toPolynomial, hmonic]
        rw [monic_eq_self (level :: lower) hvalid hinjective hinv _
          hmonicPoly] at hproduct
        have hsingleton := list_eq_singleton_of_prod_irreducible
          (factors.toList.map fun factor => HexPolyMathlib.toPolynomial
            (Factor.rawPoly (level :: lower) factor))
          (by
            intro factor hfactor
            simp only [List.mem_map] at hfactor
            obtain ⟨rawFactor, hrawFactor, rfl⟩ := hfactor
            exact (hsound rawFactor
              (Array.mem_toList_iff.mp hrawFactor)).2.not_isUnit)
          (by simpa [hproduct] using hirreducible)
        obtain ⟨factorPoly, hfactorPolys⟩ := hsingleton
        have hfactorsSize : factors.size = 1 := by
          have hlength := congrArg List.length hfactorPolys
          simpa using hlength
        obtain ⟨factor, hfactor⟩ : ∃ factor, factors = #[factor] := by
          have hzeroLt : 0 < factors.size := by omega
          refine ⟨factors[0], ?_⟩
          apply Array.ext
          · simp [hfactorsSize]
          · intro i hi₁ hi₂
            have hi : i = 0 := by simpa [hfactorsSize] using hi₁
            subst i
            simp
        have hfactorMem : factor ∈ factors := by rw [hfactor]; simp
        have hfactorEq : factor =
            Factor.polyCoords (Factor.rawPoly (level :: lower) f) := by
          have hpolyEq : HexPolyMathlib.toPolynomial
              (Factor.rawPoly (level :: lower) factor) =
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly (level :: lower) f) := by
            rw [hfactor] at hproduct
            simpa using hproduct
          have hrawEq : Factor.rawPoly (level :: lower) factor =
              Factor.rawPoly (level :: lower) f :=
            (HexPolyMathlib.equiv
              (R := Arithmetic.Coeff (level :: lower))).injective hpolyEq
          rw [← (hsound factor hfactorMem).1, hrawEq]
        have hfactors : factors =
            #[Factor.polyCoords (Factor.rawPoly (level :: lower) f)] := by
          rw [hfactor, hfactorEq]
        simp only [Factor.isIrreducible, Bool.and_eq_true]
        refine ⟨⟨⟨decide_eq_true hdegree, decide_eq_true hmonic⟩,
          hsquarefree⟩, ?_⟩
        rw [hresult]
        exact decide_eq_true hfactors

private theorem toPolynomial_polyPow (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : DensePoly (Arithmetic.Coeff levels)) (n : Nat) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    HexPolyMathlib.toPolynomial (Factor.polyPow f n) =
      HexPolyMathlib.toPolynomial f ^ n := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Factor.polyPow]
      · rw [Factor.polyPow, if_neg hn]
        have hhalf : n / 2 < n :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        dsimp only
        by_cases heven : n % 2 = 0
        · rw [if_pos heven, HexPolyMathlib.toPolynomial_mul,
            ih (n / 2) hhalf]
          rw [← pow_add]
          congr 1
          omega
        · rw [if_neg heven, HexPolyMathlib.toPolynomial_mul,
            HexPolyMathlib.toPolynomial_mul, ih (n / 2) hhalf]
          rw [← pow_add, ← pow_succ]
          congr 1
          omega

private theorem toPolynomial_factorFold (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (entries : List (Array (Array Rat) × Nat))
    (acc : DensePoly (Arithmetic.Coeff levels)) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    HexPolyMathlib.toPolynomial
        (entries.foldl (fun product entry =>
          product * Factor.polyPow
            (Factor.rawPoly levels entry.1) entry.2) acc) =
      HexPolyMathlib.toPolynomial acc *
        (entries.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  induction entries generalizing acc with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, ih, HexPolyMathlib.toPolynomial_mul,
        toPolynomial_polyPow levels hvalid hinjective]
      simp only [List.map_cons, List.prod_cons]
      ring

private theorem leadingCoeff_mul_monic (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (p : DensePoly (Arithmetic.Coeff levels)) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    Polynomial.C p.leadingCoeff *
        HexPolyMathlib.toPolynomial (Norm.monic p) =
      HexPolyMathlib.toPolynomial p := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  rw [Norm.monic]
  split
  · rename_i hzero
    have hpzero : p = 0 :=
      (DensePoly.size_eq_zero_iff p).mp
        ((DensePoly.isZero_eq_true_iff p).mp hzero)
    subst p
    simp
  · rename_i hnonzero
    rw [HexPolyMathlib.toPolynomial_scale, ← mul_assoc,
      ← Polynomial.C_mul]
    have hlc : p.leadingCoeff ≠ 0 :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size p
        ((DensePoly.isZero_eq_false_iff p).mp
          (Bool.eq_false_of_not_eq_true hnonzero))
    rw [mul_inv_cancel₀ hlc]
    simp

private theorem C_leadingCoeff_eq_of_degreeZero (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (p : DensePoly (Arithmetic.Coeff levels))
    (hdegree : p.degree?.getD 0 = 0) :
    let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
    letI : Field (Arithmetic.Coeff levels) :=
      Norm.coeffFieldPoly levels hvalid hinjective hinv
    DensePoly.C p.leadingCoeff = p := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  dsimp only
  apply (HexPolyMathlib.equiv
    (R := Arithmetic.Coeff levels)).injective
  change HexPolyMathlib.toPolynomial (DensePoly.C p.leadingCoeff) =
    HexPolyMathlib.toPolynomial p
  rw [HexPolyMathlib.toPolynomial_C]
  have hnat : (HexPolyMathlib.toPolynomial p).natDegree = 0 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    exact hdegree
  calc
    Polynomial.C p.leadingCoeff =
        Polynomial.C (HexPolyMathlib.toPolynomial p).leadingCoeff := by
      rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    _ = Polynomial.C ((HexPolyMathlib.toPolynomial p).coeff 0) := by
      rw [Polynomial.leadingCoeff, hnat]
    _ = HexPolyMathlib.toPolynomial p :=
      (Polynomial.eq_C_of_natDegree_eq_zero hnat).symm

/-- Every raw candidate produced by the complete Yun/Trager pipeline passes
the executable certificate replay, provided the input coordinate array is in
the canonical image of `rawPoly`. -/
theorem factorRaw_check (levels : List Level)
    (hvalid : LevelsValid levels)
    (hinjective : LevelSemantics.DenoteInjective levels)
    (f : Array (Array Rat))
    (hcanonical :
      Factor.polyCoords (Factor.rawPoly levels f) = f)
    {raw : Factor.RawFactorization}
    (hresult : Factor.factorRaw? levels f = some raw) :
    Factor.check levels f raw.scalar raw.factors = true := by
  let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
  letI : Field (Arithmetic.Coeff levels) :=
    Norm.coeffFieldPoly levels hvalid hinjective hinv
  let p := Factor.rawPoly levels f
  have hresult' := hresult
  simp only [Factor.factorRaw?] at hresult'
  split at hresult'
  · obtain ⟨factors, hfold, hraw⟩ :=
      Option.bind_eq_some_iff.mp hresult'
    have hfoldList :
        (Factor.yunRaw levels f).toList.foldlM
          (Factor.appendComponent? levels) #[] = some factors := by
      rw [Array.foldlM_toList]
      exact hfold
    have hsound := factorFold_sound levels hvalid hinjective f
      (Factor.yunRaw levels f).toList
      (by intro component hcomponent; exact hcomponent)
      #[] factors hfoldList (by simp)
    have hpre := hsound.1
    have hpreProduct :
        (factors.toList.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod =
          ((Factor.yunRaw levels f).toList.map fun component =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) ^ component.2).prod := by
      simpa using hsound.2
    cases hraw
    have hproperties : ∀ entry ∈ Factor.canonicalFactors factors,
        Factor.polyCoords (Factor.rawPoly levels entry.1) = entry.1 ∧
          (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1)).Monic ∧
          Irreducible (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1)) := by
      apply canonicalFactors_preserves
        (fun factor =>
          Factor.polyCoords (Factor.rawPoly levels factor) = factor ∧
            (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels factor)).Monic ∧
            Irreducible (HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels factor)))
      intro entry hentry
      have h := hpre entry hentry
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    have hpositive : ∀ entry ∈ Factor.canonicalFactors factors,
        0 < entry.2 :=
      canonicalFactors_positive factors fun entry hentry =>
        (hpre entry hentry).2.2.2
    have hcoords :
        (Factor.canonicalFactors factors).all (fun entry =>
          Factor.polyCoords (Factor.rawPoly levels entry.1) =
            entry.1) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro entry hentry
      exact decide_eq_true (hproperties entry hentry).1
    have hchecks :
        (Factor.canonicalFactors factors).all (fun entry =>
          0 < entry.2 && Factor.isIrreducible levels entry.1) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro entry hentry
      simp only [Bool.and_eq_true]
      refine ⟨decide_eq_true (hpositive entry hentry), ?_⟩
      apply (isIrreducible_iff_of_injective levels hvalid hinjective
        entry.1).mpr
      have hentrySound := hproperties entry hentry
      refine ⟨?_, hentrySound.2.2⟩
      simpa only [Polynomial.Monic.def,
        HexPolyMathlib.leadingCoeff_toPolynomial] using hentrySound.2.1
    have hcanonicalProduct :
        ((Factor.canonicalFactors factors).toList.map fun entry =>
          HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels entry.1) ^ entry.2).prod =
          ((Factor.yunRaw levels f).toList.map fun component =>
            HexPolyMathlib.toPolynomial
              (Factor.rawPoly levels component.1) ^ component.2).prod :=
      (canonicalFactors_prod
        (fun factor => HexPolyMathlib.toPolynomial
          (Factor.rawPoly levels factor)) factors).trans hpreProduct
    have hreconstruct : Factor.factorProduct levels
        p.leadingCoeff.data (Factor.canonicalFactors factors) = f := by
      by_cases hdegree : p.degree?.getD 0 = 0
      · have hcomponents : Factor.yunRaw levels f = #[] := by
          simp [Factor.yunRaw, p, hdegree]
        have hfactors : factors = #[] := by
          rw [hcomponents] at hfold
          simpa using hfold
        subst factors
        change Factor.polyCoords
          (DensePoly.C (Arithmetic.Coeff.ofData levels
            p.leadingCoeff.data)) = f
        rw [LevelSemantics.coeff_ofData_data,
          C_leadingCoeff_eq_of_degreeZero levels hvalid hinjective p
            hdegree,
          hcanonical]
      · have hdegreePositive : 0 < p.degree?.getD 0 :=
          Nat.pos_of_ne_zero hdegree
        have hyun := yun_product hvalid hinjective hinv f hdegreePositive
        have hyunDense := congrArg (Factor.rawPoly levels) hyun
        unfold Factor.yunProduct at hyunDense
        simp only [rawPoly_polyCoords] at hyunDense
        rw [← Array.foldl_toList] at hyunDense
        have hcomponentProduct :
            ((Factor.yunRaw levels f).toList.map fun component =>
              HexPolyMathlib.toPolynomial
                (Factor.rawPoly levels component.1) ^ component.2).prod =
              HexPolyMathlib.toPolynomial (Norm.monic p) := by
          have hsemantic := toPolynomial_factorFold levels hvalid hinjective
            (Factor.yunRaw levels f).toList
            (1 : DensePoly (Arithmetic.Coeff levels))
          simp only [HexPolyMathlib.toPolynomial_one, one_mul] at hsemantic
          rw [← hsemantic]
          exact congrArg HexPolyMathlib.toPolynomial hyunDense
        unfold Factor.factorProduct
        rw [← hcanonical]
        apply congrArg Factor.polyCoords
        apply (HexPolyMathlib.equiv
          (R := Arithmetic.Coeff levels)).injective
        change HexPolyMathlib.toPolynomial
            ((Factor.canonicalFactors factors).foldl
              (fun product factor => product * Factor.polyPow
                (Factor.rawPoly levels factor.1) factor.2)
              (DensePoly.C (Arithmetic.Coeff.ofData levels
                p.leadingCoeff.data))) =
          HexPolyMathlib.toPolynomial p
        rw [← Array.foldl_toList,
          toPolynomial_factorFold levels hvalid hinjective,
          HexPolyMathlib.toPolynomial_C,
          LevelSemantics.coeff_ofData_data,
          hcanonicalProduct, hcomponentProduct]
        exact leadingCoeff_mul_monic levels hvalid hinjective p
    simp only [Factor.check, Bool.and_eq_true]
    exact ⟨⟨⟨hcoords, decide_eq_true hreconstruct⟩,
      canonicalFactors_sorted factors⟩, hchecks⟩
  · contradiction

private theorem relation_eq_rawPoly (level : Level) (lower : List Level)
    (hvalid : LevelsValid (level :: lower)) :
    Arithmetic.Coeff.relation level lower =
      Factor.rawPoly lower (level.polynomial lower) := by
  rw [Arithmetic.Coeff.relation, Factor.rawPoly, Level.polynomial]
  congr 1
  rw [Array.map_push]
  have hbase :
      ((List.range level.degree).map fun i =>
        Arithmetic.Coeff.ofData lower
          (level.defining.getD i #[])).toArray =
        level.defining.map (Arithmetic.Coeff.ofData lower) := by
    apply Array.ext
    · simp [hvalid.1.2]
    · intro i hi₁ hi₂
      have hi : i < level.degree := by simpa [hvalid.1.2] using hi₂
      have hidefining : i < level.defining.size := by
        simpa [hvalid.1.2] using hi
      simp [Array.getD, hi, hidefining]
  rw [hbase]
  have hone : Arithmetic.Coeff.ofData lower
      (Arithmetic.fixedCoeffs (levelsDim lower) #[1]) =
        (1 : Arithmetic.Coeff lower) := by
    exact LevelSemantics.coeff_ofData_data lower
      (1 : Arithmetic.Coeff lower)
  rw [hone]

/-- Structural validity plus the recursive checker certificates imply
injectivity of raw coefficient denotation at every tower depth. -/
theorem denoteInjective_of_valid : ∀ (levels : List Level),
    LevelsValid levels → LevelSemantics.DenoteInjective levels := by
  intro levels
  induction levels with
  | nil =>
      intro hvalid
      exact LevelSemantics.DenoteInjective.nil
  | cons level lower ih =>
      intro hvalid
      have hinjectiveLower := ih hvalid.2.2
      let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
        hinjectiveLower
      letI : Field (Arithmetic.Coeff lower) :=
        Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
      have hrelation : Irreducible (HexPolyMathlib.toPolynomial
          (Arithmetic.Coeff.relation level lower)) := by
        cases hvalid.2.1 with
        | rational hrat =>
            have hlower : lower = [] := hrat.1
            subst lower
            exact LevelSemantics.relation_irreducible_rational level
              hvalid.1 hrat
        | relative _ hchecker _ =>
            have hraw := (isIrreducible_iff_of_injective lower hvalid.2.2
              hinjectiveLower (level.polynomial lower)).mp hchecker
            rw [relation_eq_rawPoly level lower hvalid]
            exact hraw.2
      exact LevelSemantics.DenoteInjective.cons level lower hvalid
        (LevelSemantics.separates_of_irreducible level lower hvalid
          hinjectiveLower hinvLower hrelation)

end Hex.NumberTower
