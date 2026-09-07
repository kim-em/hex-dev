/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.FactorGeneric.Product

public section

/-!
# Soundness of recursive Trager factorization

The singleton shortcut agrees with gcd recovery, whose product and
irreducibility theorems establish recursive factorization soundness.
-/

namespace Hex.NumberTower

/-- Soundness of the squarefree-component factorizer at every tower height:
each returned factor is a canonical coordinate array interpreting to an
irreducible polynomial, by induction through the recursive one-level Trager
step with the Berlekamp-Zassenhaus base case. -/
theorem factorSquarefree_mem_sound :
    ∀ (levels : List Level) (hvalid : LevelsValid levels)
      (hinjective : LevelSemantics.DenoteInjective levels)
      (f : Array (Array Rat)) {factors : Array (Array (Array Rat))},
      Factor.factorSquarefree? levels f = some factors →
      let hinv := LevelSemantics.coeffDenote_inv levels hvalid hinjective
      letI : Field (Arithmetic.Coeff levels) :=
        Norm.coeffFieldPoly levels hvalid hinjective hinv
      ∀ factor ∈ factors,
        Factor.polyCoords (Factor.rawPoly levels factor) = factor ∧
          Irreducible (HexPolyMathlib.toPolynomial
            (Factor.rawPoly levels factor)) := by
  intro levels
  induction levels with
  | nil =>
      intro hvalid hinjective f factors hresult
      let hinv := LevelSemantics.coeffDenote_inv [] hvalid hinjective
      let : Field (Arithmetic.Coeff []) :=
        Norm.coeffFieldPoly [] hvalid hinjective hinv
      have hvalidEq : hvalid = (trivial : LevelsValid []) :=
        Subsingleton.elim _ _
      have hinjectiveEq : hinjective = LevelSemantics.DenoteInjective.nil :=
        Subsingleton.elim _ _
      subst hvalid
      subst hinjective
      exact factorRat_mem_sound (Factor.toRatPoly f) hresult
  | cons level lower ih =>
      intro hvalid hinjectiveTop f factors hresult
      let hinjectiveLower := hinjectiveTop.tail level lower hvalid.1.1
      let hinvLower := LevelSemantics.coeffDenote_inv lower hvalid.2.2
        hinjectiveLower
      let hinvTop := LevelSemantics.coeffDenote_inv (level :: lower) hvalid
        hinjectiveTop
      let : Field (Arithmetic.Coeff lower) :=
        Norm.coeffFieldPoly lower hvalid.2.2 hinjectiveLower hinvLower
      let : Field (Arithmetic.Coeff (level :: lower)) :=
        Norm.coeffFieldPoly (level :: lower) hvalid hinjectiveTop hinvTop
      dsimp only
      simp only [Factor.factorSquarefree?] at hresult
      split at hresult
      · rename_i hinputSquarefree
        obtain ⟨pair, hfind, hresult⟩ := Option.bind_eq_some_iff.mp hresult
        rcases pair with ⟨shift, norm⟩
        obtain ⟨lowerFactors, hlower, hresult⟩ :=
          Option.bind_eq_some_iff.mp hresult
        let chosen := if lowerFactors.size = 1 then
          #[Factor.polyCoords (Norm.monic (Factor.rawPoly (level :: lower) f))]
          else Factor.recover level lower shift f lowerFactors
        change (if chosen.all (fun factor =>
            0 < (Factor.rawPoly (level :: lower) factor).natDegree) &&
            chosen.foldl (fun product factor =>
              product * Factor.rawPoly (level :: lower) factor) 1 =
              Norm.monic (Factor.rawPoly (level :: lower) f) then
            some chosen else none) = some factors at hresult
        split at hresult
        · rename_i hcheck
          have heq := Option.some.inj hresult
          subst factors
          intro factor hfactor
          have hlower' : Factor.factorSquarefree? lower norm =
              some lowerFactors := by simpa using hlower
          have hlowerSound : ∀ lowerFactor ∈ lowerFactors,
              Factor.polyCoords (Factor.rawPoly lower lowerFactor) =
                  lowerFactor ∧
                Irreducible (HexPolyMathlib.toPolynomial
                  (Factor.rawPoly lower lowerFactor)) := by
            exact ih hvalid.2.2 hinjectiveLower norm hlower'
          have hnormCheck : Norm.isSquarefree lower norm :=
            findSquarefreeShift_squarefree level lower f (by simpa using hfind)
          have hnormSquarefree : Squarefree
              (HexPolyMathlib.toPolynomial
                (Factor.rawPoly lower norm)) :=
            squarefree_toPolynomial_of_check lower hvalid.2.2
              hinjectiveLower hinvLower norm hnormCheck
          have hnormEq : norm = Norm.oneLevel level lower f shift :=
            findSquarefreeShift_norm level lower f (by simpa using hfind)
          have htragerSquarefree : Squarefree
              (HexPolyMathlib.toPolynomial
                (tragerNorm level lower
                  (Factor.rawPoly (level :: lower)
                    (Factor.shiftTop level lower f shift)))) := by
            rw [tragerNorm_shiftTop level lower hvalid hinjectiveTop,
              ← hnormEq]
            exact hnormSquarefree
          have hrecoverSound := recover_mem_sound level lower hvalid
            hinjectiveTop f shift lowerFactors htragerSquarefree hlowerSound
          have hchosen : chosen = Factor.recover level lower shift f lowerFactors := by
            by_cases hsingle : lowerFactors.size = 1
            · have hdegree :
                  0 < (Norm.monic (Factor.rawPoly (level :: lower) f)).natDegree := by
                have hc := hcheck
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                simpa [chosen, hsingle, rawPoly_polyCoords] using hc.1
              have hfNe : Factor.rawPoly (level :: lower) f ≠ 0 := by
                intro hzero
                simp [hzero, Norm.monic] at hdegree
              have hnormNe : Factor.rawPoly lower norm ≠ 0 := by
                intro hzero
                apply hnormSquarefree.ne_zero
                simp [hzero]
              have hlowerProduct := factorSquarefree_product lower hvalid.2.2
                hinjectiveLower norm hnormNe hlower'
              have hproduct := recover_product level lower hvalid hinjectiveTop
                f norm shift lowerFactors hfNe hnormSquarefree hnormEq
                (fun q hq => (hlowerSound q hq).1) hlowerProduct
                (fun q hq => (hrecoverSound q hq).2)
              simpa only [chosen, hsingle, ite_true] using
                (recover_singleton level lower hvalid hinjectiveTop f shift
                  lowerFactors hsingle hdegree hproduct).symm
            · simp only [chosen, hsingle, ite_false]
          exact hrecoverSound factor (hchosen ▸ hfactor)
        · contradiction
      · contradiction

end Hex.NumberTower
