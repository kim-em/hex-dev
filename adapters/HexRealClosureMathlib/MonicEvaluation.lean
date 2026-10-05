/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Ideal.Maps
public import HexRealClosureMathlib.CoefficientMap

public section

namespace Hex.RealClosure.Specialize.Algebraic

variable {F K G : Type*} [Field F] [Field K] [CommRing G] [Algebra F K]

/-- Polynomial evaluation in the original algebraic extension, restricted to
the coefficient subring on which specialization is defined. -/
def source (domain : Subring F) (root : K) : Polynomial domain →+* K :=
  Polynomial.eval₂RingHom ((algebraMap F K).comp domain.subtype) root

/-- Evaluate the actual polynomial before passing to its image subring. -/
theorem source_apply (domain : Subring F) (root : K) (p : Polynomial domain) :
    source domain root p = p.eval₂ ((algebraMap F K).comp domain.subtype) root := by
  simp only [source, Polynomial.coe_eval₂RingHom]

/-- A monic lift of the actual minimal polynomial controls all identities
over the coefficient subring. Specialization needs its selected root, rather
than an interpretation on the whole original coefficient field. -/
theorem kernel (domain : Subring F) (value : domain →+* G) (root : K) (selected : G)
    (minimal : Polynomial domain) (monic : minimal.Monic)
    (original : minimal.map domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ value selected = 0)
    (p : Polynomial domain) (zero : source domain root p = 0) :
    p.eval₂ value selected = 0 := by
  have originalZero : Polynomial.aeval root (p.map domain.subtype) = 0 := by
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_map, source,
      Polynomial.coe_eval₂RingHom] using zero
  have divides : minimal ∣ p := by
    apply (Polynomial.modByMonic_eq_zero_iff_dvd monic).mp
    apply Polynomial.map_injective domain.subtype Subtype.val_injective
    rw [Polynomial.map_zero, Polynomial.map_modByMonic domain.subtype monic, original]
    have monicOriginal : (minpoly F root).Monic := by
      rw [← original]
      exact monic.map domain.subtype
    exact (Polynomial.modByMonic_eq_zero_iff_dvd monicOriginal).mpr
      (minpoly.dvd F root originalZero)
  obtain ⟨q, rfl⟩ := divides
  rw [Polynomial.eval₂_mul, chosen, zero_mul]

/-- Evaluation on the actual polynomial image of the original generator.
The kernel theorem makes this independent of the representing polynomial. -/
noncomputable def evaluation (domain : Subring F) (value : domain →+* G)
    (root : K) (selected : G) (minimal : Polynomial domain) (monic : minimal.Monic)
    (original : minimal.map domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ value selected = 0) : (source domain root).range →+* G :=
  (source domain root).rangeRestrict.liftOfSurjective
    (source domain root).rangeRestrict_surjective
    ⟨Polynomial.eval₂RingHom value selected, by
      intro p hp
      apply RingHom.mem_ker.mpr
      apply kernel domain value root selected minimal monic original chosen p
      exact congrArg Subtype.val (RingHom.mem_ker.mp hp)⟩

/-- Evaluation agrees with every polynomial presentation, including ones
whose coefficients were formed by preceding arithmetic in the subring. -/
theorem evaluation_apply (domain : Subring F) (value : domain →+* G)
    (root : K) (selected : G) (minimal : Polynomial domain) (monic : minimal.Monic)
    (original : minimal.map domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ value selected = 0) (p : Polynomial domain) :
    evaluation domain value root selected minimal monic original chosen
      ((source domain root).rangeRestrict p) = p.eval₂ value selected := by
  exact RingHom.liftOfSurjective_comp_apply _ _ _ _

/-- The original generator is mapped to the selected specialized root. -/
theorem evaluation_root (domain : Subring F) (value : domain →+* G)
    (root : K) (selected : G) (minimal : Polynomial domain) (monic : minimal.Monic)
    (original : minimal.map domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ value selected = 0) :
    evaluation domain value root selected minimal monic original chosen
      ((source domain root).rangeRestrict Polynomial.X) = selected := by
  rw [evaluation_apply, Polynomial.eval₂_X]

/-- Previously interpreted coefficients retain their values in the algebraic
extension's evaluation. -/
theorem evaluation_coefficient (domain : Subring F) (value : domain →+* G)
    (root : K) (selected : G) (minimal : Polynomial domain) (monic : minimal.Monic)
    (original : minimal.map domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ value selected = 0) (a : domain) :
    evaluation domain value root selected minimal monic original chosen
      ((source domain root).rangeRestrict (Polynomial.C a)) = value a := by
  rw [evaluation_apply, Polynomial.eval₂_C]

/-- info: 'Hex.RealClosure.Specialize.Algebraic.evaluation_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.Algebraic.evaluation_apply

end Hex.RealClosure.Specialize.Algebraic

namespace Hex.RealClosure.CoefficientMap

variable {F K G : Type} [Field F] [Field K] [Field G] [Algebra F K]
variable [DecidableEq F] [DecidableEq K] [DecidableEq G]

/-- Extend a coefficient interpretation over the polynomial image of an
algebraic generator, using the selected zero of its lifted minimal polynomial. -/
noncomputable def algebraic (interpretation : CoefficientMap F G) (root : K) (selected : G)
    (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ interpretation.value selected = 0) : CoefficientMap K G where
  domain := (Specialize.Algebraic.source interpretation.domain root).range
  value := Specialize.Algebraic.evaluation interpretation.domain interpretation.value
    root selected minimal monic original chosen

/-- The interpreted algebraic domain contains its original selected generator. -/
theorem algebraic_mem (interpretation : CoefficientMap F G) (root : K) (selected : G)
    (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ interpretation.value selected = 0) :
    root ∈ (interpretation.algebraic root selected minimal monic original chosen).domain := by
  refine ⟨Polynomial.X, ?_⟩
  simp [Specialize.Algebraic.source]

/-- The actual source generator is evaluated at the selected specialized root. -/
theorem algebraic_root (interpretation : CoefficientMap F G) (root : K) (selected : G)
    (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ interpretation.value selected = 0) :
    (interpretation.algebraic root selected minimal monic original chosen).map root = selected := by
  rw [map_mem _ _ (algebraic_mem interpretation root selected minimal monic original chosen)]
  let extended := interpretation.algebraic root selected minimal monic original chosen
  have bound : (Specialize.Algebraic.source interpretation.domain root).rangeRestrict Polynomial.X =
      (⟨root, algebraic_mem interpretation root selected minimal monic original chosen⟩ :
        extended.domain) := by
    apply Subtype.ext
    change Specialize.Algebraic.source interpretation.domain root Polynomial.X = root
    simp [Specialize.Algebraic.source]
  change Specialize.Algebraic.evaluation interpretation.domain interpretation.value
    root selected minimal monic original chosen _ = selected
  rw [← bound]
  exact Specialize.Algebraic.evaluation_root _ _ _ _ _ _ _ _

/-- info: 'Hex.RealClosure.CoefficientMap.algebraic_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.algebraic_root

/-- Every polynomial in the original generator lies in the interpreted
domain, and its specialized value is independent of its presentation. -/
theorem algebraic_polynomial (interpretation : CoefficientMap F G) (root : K) (selected : G)
    (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ interpretation.value selected = 0)
    (p : Polynomial interpretation.domain) :
    Specialize.Algebraic.source interpretation.domain root p ∈
        (interpretation.algebraic root selected minimal monic original chosen).domain ∧
      (interpretation.algebraic root selected minimal monic original chosen).map
        (Specialize.Algebraic.source interpretation.domain root p) =
          p.eval₂ interpretation.value selected := by
  let member : Specialize.Algebraic.source interpretation.domain root p ∈
      (interpretation.algebraic root selected minimal monic original chosen).domain := ⟨p, rfl⟩
  refine ⟨member, ?_⟩
  rw [map_mem _ _ member]
  change Specialize.Algebraic.evaluation interpretation.domain interpretation.value
    root selected minimal monic original chosen
      ((Specialize.Algebraic.source interpretation.domain root).rangeRestrict p) = _
  exact Specialize.Algebraic.evaluation_apply _ _ _ _ _ _ _ _ p

/-- Adjoining the specialized root preserves every previously interpreted
coefficient through the original ambient field inclusion. -/
theorem algebraic_map (interpretation : CoefficientMap F G) (root : K) (selected : G)
    (minimal : Polynomial interpretation.domain) (monic : minimal.Monic)
    (original : minimal.map interpretation.domain.subtype = minpoly F root)
    (chosen : minimal.eval₂ interpretation.value selected = 0)
    (a : F) (member : a ∈ interpretation.domain) :
    (interpretation.algebraic root selected minimal monic original chosen).map
      (algebraMap F K a) = interpretation.map a := by
  have evaluated := interpretation.algebraic_polynomial root selected minimal monic original chosen
    (Polynomial.C ⟨a, member⟩)
  have source : Specialize.Algebraic.source interpretation.domain root (Polynomial.C ⟨a, member⟩) =
      algebraMap F K a := by
    rw [Specialize.Algebraic.source_apply, Polynomial.eval₂_C]
    rfl
  rw [source, Polynomial.eval₂_C] at evaluated
  exact evaluated.2.trans (interpretation.map_mem a member).symm

/-- info: 'Hex.RealClosure.CoefficientMap.algebraic_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.algebraic_map

end Hex.RealClosure.CoefficientMap
