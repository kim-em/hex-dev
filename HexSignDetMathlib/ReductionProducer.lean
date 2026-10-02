/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Reduction
public import HexSturmMathlib.Domain

public section

/-! Acceptance of produced positive-scaled moment reductions. The shared
pseudo-division and normalization correspondence supplies the arithmetic; no
Sturm–Tarski or Thom foundation is required. -/
namespace Hex.SignDet

open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [Neg E] [Inv E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0) (h1 : f (1 : E) = 1)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (sign : E → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)
variable (hneg : ∀ a, sign a < 0 ↔ f a < 0)

include hz h1 ha hs hm hn hi hpos hneg in
/-- The actual one-step producer supplies its positive scales, exact identity,
factor index and remainder degree bound. -/
theorem ReductionStep.build_checks (p prev factor : DensePoly E) (index : Nat) (hp : p ≠ 0) :
    (ReductionStep.build sign p prev factor index).check sign p prev factor index = true := by
  have hmpos := positive_multiplier f hz h1 ha hs hm hn sign hneg (prev * factor) p hp
  have hrec := positive_reconstruct f hz h1 ha hs hm hn sign (prev * factor) p
  have hdeg := positive_remainder_degree f hz hs sign (prev * factor) p hp
  unfold ReductionStep.build
  dsimp only
  split
  · rename_i hr
    simp only [ReductionStep.check, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      and_assoc]
    refine ⟨True.intro, (hpos _).mpr hmpos, (hpos _).mpr (by rw [h1]; exact zero_lt_one),
      Or.inl hr, ?_⟩
    apply (sub_isZero f hz hs _ _).mpr
    simpa only [interpret_scale f hz hm, interpret_mul f hz ha hm, interpret_add f hz ha,
      h1, Polynomial.C_1, one_mul] using hrec
  · rename_i hr
    have hrne : (DensePoly.positivePseudoDiv sign (prev * factor) p).remainder ≠ 0 := by
      intro he
      apply hr
      rw [he]
      rfl
    have hnorm := HexSturmMathlib.normalize_eq f hz hm sign hneg hn hi _ hrne
    have hd := congrArg Polynomial.natDegree hnorm.2
    rw [Polynomial.natDegree_C_mul (ne_of_gt hnorm.1)] at hd
    simp only [natDegree_interpret] at hd
    have hsmall : (Sturm.normalize sign
        (DensePoly.positivePseudoDiv sign (prev * factor) p).remainder).2.natDegree < p.natDegree := by
      rcases hdeg with hzero | hlt
      · exact False.elim (hrne ((interpret_eq_zero f hz _).mp hzero))
      · simpa only [natDegree_interpret, hd] using hlt
    simp only [ReductionStep.check, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      and_assoc]
    refine ⟨True.intro, (hpos _).mpr hmpos, (hpos _).mpr hnorm.1, Or.inr hsmall, ?_⟩
    apply (sub_isZero f hz hs _ _).mpr
    simp only [interpret_scale f hz hm, interpret_mul f hz ha hm, interpret_add f hz ha]
    rw [hnorm.2]
    simpa only [interpret_mul f hz ha hm] using hrec

include hz h1 ha hs hm hn hi hpos hneg in
/-- Every finite produced chain passes replay, including an empty factor list. -/
theorem Reduction.buildFrom_checks (p prev : DensePoly E) (fs : List (Nat × DensePoly E))
    (hp : p ≠ 0) :
    checkFrom sign p prev fs (buildFrom sign p prev fs).steps (buildFrom sign p prev fs).result = true := by
  induction fs generalizing prev with
  | nil =>
    exact (sub_isZero f hz hs prev prev).mpr rfl
  | cons item fs ih =>
    obtain ⟨index, factor⟩ := item
    simp only [buildFrom, checkFrom, Bool.and_eq_true]
    exact ⟨ReductionStep.build_checks f hz h1 ha hs hm hn hi sign hpos hneg p prev factor index hp,
      ih _⟩

include hz h1 ha hs hm hn hi hpos hneg in
/-- The actual reduced-moment producer passes its checker on the declared
positive-degree input and well-formed exponent vector. -/
theorem Reduction.build_checks (p : DensePoly E) (qs : List (DensePoly E)) (es : List Nat)
    (hp : 0 < p.natDegree) (hlen : qs.length = es.length) (he : es.all (· ≤ 2) = true) :
    (build sign p qs es).check sign p qs es = true := by
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hp
  simp only [check, build, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hp, hlen⟩, he⟩,
    buildFrom_checks f hz h1 ha hs hm hn hi sign hpos hneg p 1 (factors qs es) hpne⟩

end Hex.SignDet
