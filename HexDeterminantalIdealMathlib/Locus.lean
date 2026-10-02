/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealMathlib.Rank
public import HexDeterminantalIdealMathlib.Ideal
public import HexMvPolyMathlib
public import HexRankMathlib.Extension
public import Mathlib.RingTheory.Nullstellensatz

public section

/-!
Rank loci of polynomial matrices. Both theorems are the headline theorem of
`Rank` with `φ` the executable evaluation `HexMvPolyMathlib.aeval p` as a
ring homomorphism: `rankAt_lt_iff_inLocus` reads it through `MvPoly.eval`,
which is how the executable `rankAt` and `InLocus` are defined, and
`mem_zeroLocus_iff_rank_lt` reads it through `MvPolynomial.aeval` after
`HexMvPolyMathlib.equiv`, which is how membership in `MvPolynomial.zeroLocus`
is stated.
-/

namespace HexDeterminantalIdealMathlib

open HexMatrixMathlib
open scoped HexMvPolyMathlib

universe u v

section Generators

variable {C : Type u} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
  {F : Type v} {k n m : Nat}
  {cmp : Hex.Mono k → Hex.Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- The generators vanish under an interpretation precisely below the rank
threshold, allowing different coefficient and value fields. -/
theorem gens_vanish_iff_rank_lt [Field F]
    (ι : C →+* F) (A : Hex.Matrix (Hex.MvPoly k C cmp) n m)
    (v : Fin k → F) (r : Nat) :
    (∀ g ∈ Hex.Matrix.detIdealGens r A,
      MvPolynomial.eval₂ ι v (HexMvPolyMathlib.equiv g) = 0) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.eval₂MathlibHom ι v)).rank < r :=
  (rank_lt_iff_gens_map_zero (HexMvPolyMathlib.eval₂MathlibHom ι v) A r).symm

/-- Pass to the fraction field to read generator vanishing as a rank
condition over any integral domain. -/
theorem gens_vanish_iff_rank_lt_of_domain [CommRing F] [IsDomain F]
    (ι : C →+* F) (A : Hex.Matrix (Hex.MvPoly k C cmp) n m)
    (v : Fin k → F) (r : Nat) :
    (∀ g ∈ Hex.Matrix.detIdealGens r A,
      MvPolynomial.eval₂ ι v (HexMvPolyMathlib.equiv g) = 0) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.eval₂MathlibHom ι v)).rank < r := by
  let φ := HexMvPolyMathlib.eval₂MathlibHom (cmp := cmp) ι v
  let j := algebraMap F (FractionRing F)
  have h : (∀ g ∈ Hex.Matrix.detIdealGens r A, (j.comp φ) g = 0) ↔
      ((matrixEquiv A).map (j.comp φ)).rank < r :=
    (rank_lt_iff_gens_map_zero (j.comp φ) A r).symm
  have hm : (matrixEquiv A).map (j.comp φ) = ((matrixEquiv A).map φ).map j := rfl
  rw [hm, HexMatrixMathlib.rank_map_eq] at h
  simpa only [RingHom.comp_apply, j, IsFractionRing.to_map_eq_zero_iff, φ,
    HexMvPolyMathlib.eval₂MathlibHom_apply, HexMvPolyMathlib.equiv_apply,
    HexMvPolyMathlib.eval₂_toMvPolynomial] using h

end Generators

section Mapped

variable {C : Type u} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C]
  {D : Type v} [CommRing D] {K : Type*} [Field K] {σ : Type*} {k n m : Nat}
  {cmp : Hex.Mono k → Hex.Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Evaluation after coefficient mapping and variable renaming is evaluation
at the composed coefficient map and point. -/
theorem gens_map_vanish_iff_rank_lt (ι : C →+* D) (f : Fin k → σ)
    (A : Hex.Matrix (Hex.MvPoly k C cmp) n m) (r : Nat) (ψ : D →+* K) (p : σ → K) :
    (∀ g ∈ (Hex.Matrix.detIdealGens r A).map
      (MvPolynomial.rename f ∘ MvPolynomial.map ι ∘ HexMvPolyMathlib.equiv),
      MvPolynomial.eval₂ ψ p g = 0) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.eval₂MathlibHom (ψ.comp ι) (p ∘ f))).rank < r := by
  rw [List.forall_mem_map]
  simpa only [Function.comp_apply, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_map] using
    gens_vanish_iff_rank_lt (ψ.comp ι) A (p ∘ f) r

private theorem span_map_list {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (xs : List R) :
    Ideal.span {x | x ∈ xs.map φ} = Ideal.map φ (Ideal.span {x | x ∈ xs}) := by
  rw [Ideal.map_span]
  congr 1
  ext x
  simp

/-- The mapped generators span the mapped determinantal ideal. -/
theorem span_gens_map_eq (ι : C →+* D) (f : Fin k → σ)
    (A : Hex.Matrix (Hex.MvPoly k C cmp) n m) (r : Nat) :
    Ideal.span {g | g ∈ (Hex.Matrix.detIdealGens r A).map
      (MvPolynomial.rename f ∘ MvPolynomial.map ι ∘ HexMvPolyMathlib.equiv)} =
      Ideal.map (MvPolynomial.rename f).toRingHom
        (Ideal.map (MvPolynomial.map ι)
          (Ideal.span {g | g ∈ (Hex.Matrix.minors r A).map HexMvPolyMathlib.equiv})) := by
  have hmap (xs : List (Hex.MvPoly k C cmp)) :
      xs.map (MvPolynomial.rename f ∘ MvPolynomial.map ι ∘ HexMvPolyMathlib.equiv) =
        ((xs.map HexMvPolyMathlib.equiv.toRingHom).map (MvPolynomial.map ι)).map
          (MvPolynomial.rename f).toRingHom := by simp only [List.map_map]; rfl
  have hs : Ideal.span {x | x ∈ Hex.Matrix.detIdealGens r A} =
      Ideal.span {x | x ∈ Hex.Matrix.minors r A} := span_detIdealGens_eq A r
  have he : Ideal.span {g | g ∈ (Hex.Matrix.minors r A).map HexMvPolyMathlib.equiv} =
      Ideal.map HexMvPolyMathlib.equiv.toRingHom (Ideal.span {g | g ∈ Hex.Matrix.minors r A}) := by
    rw [Ideal.map_span]
    congr 1
    ext g
    simp
  rw [hmap, span_map_list, span_map_list, span_map_list, hs, he]

end Mapped

section ZeroLocus

variable {C : Type u} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C] {D : Type v} [Field D]
  {σ : Type*} {k n m : Nat}
  {cmp : Hex.Mono k → Hex.Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- For field coefficients the pointwise generator theorem is a zero-locus statement. -/
theorem mem_zeroLocus_map_iff_rank_lt (ι : C →+* D) (f : Fin k → σ)
    (A : Hex.Matrix (Hex.MvPoly k C cmp) n m) (r : Nat) (p : σ → D) :
    p ∈ MvPolynomial.zeroLocus D (Ideal.span {g | g ∈ (Hex.Matrix.detIdealGens r A).map
      (MvPolynomial.rename f ∘ MvPolynomial.map ι ∘ HexMvPolyMathlib.equiv)}) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.eval₂MathlibHom ι (p ∘ f))).rank < r := by
  rw [MvPolynomial.mem_zeroLocus_iff]
  have h := gens_map_vanish_iff_rank_lt ι f A r (RingHom.id D) p
  simp only [RingHom.id_comp] at h
  rw [← h]
  constructor
  · intro h g hg
    exact h g (Ideal.subset_span hg)
  · intro h g hg
    have hle : Ideal.span {g | g ∈ (Hex.Matrix.detIdealGens r A).map
        (MvPolynomial.rename f ∘ MvPolynomial.map ι ∘ HexMvPolyMathlib.equiv)} ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id D) p) := by
      rw [Ideal.span_le]
      exact h
    exact hle hg

end ZeroLocus

variable {k : Nat} {F : Type u} [Field F] [DecidableEq F]
  {cmp : Hex.Mono k → Hex.Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {n m : Nat}

/-- The evaluation algebra homomorphism is `MvPoly.eval` as a function. -/
private theorem coe_aeval_eq_eval (p : Fin k → F) :
    (⇑(HexMvPolyMathlib.aeval p).toRingHom : Hex.MvPoly k F cmp → F) = Hex.MvPoly.eval p := by
  funext q
  exact HexMvPolyMathlib.aeval_eq_eval p q

/-- The rank of a polynomial matrix at a point is below `r` exactly when the
point lies in the zero set of `I_r(A)`. -/
theorem rankAt_lt_iff_inLocus (A : Hex.Matrix (Hex.MvPoly k F cmp) n m) (p : Fin k → F)
    (r : Nat) :
    Hex.Matrix.rankAt A p < r ↔ Hex.Matrix.InLocus r A p := by
  have h := rank_lt_iff_minors_map_eq_zero (HexMvPolyMathlib.aeval p).toRingHom A r
  rw [coe_aeval_eq_eval, ← matrixEquiv_map] at h
  rw [Hex.Matrix.inLocus_iff, Hex.Matrix.rankAt_eq,
    show Hex.Matrix.rowReduce_rank (Hex.Matrix.specialize A p) =
      (Hex.Matrix.rowReduce (A.map (Hex.MvPoly.eval p))).rank from rfl,
    rank_eq (Hex.Matrix.rowReduce_isRowReduced _)]
  exact h

/-- The zero set of `I_r(A)` is the locus where the rank drops below `r`. -/
theorem mem_zeroLocus_iff_rank_lt (A : Hex.Matrix (Hex.MvPoly k F cmp) n m) (p : Fin k → F)
    (r : Nat) :
    p ∈ MvPolynomial.zeroLocus F
        (Ideal.span (HexMvPolyMathlib.equiv '' {M | M ∈ Hex.Matrix.minors r A})) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.aeval p)).rank < r := by
  rw [MvPolynomial.mem_zeroLocus_iff,
    show (matrixEquiv A).map (HexMvPolyMathlib.aeval p) =
      (matrixEquiv A).map (HexMvPolyMathlib.aeval p).toRingHom from rfl,
    rank_lt_iff_minors_map_eq_zero]
  constructor
  · intro h M hM
    have hq := h (HexMvPolyMathlib.equiv M) (Ideal.subset_span ⟨M, hM, rfl⟩)
    rw [HexMvPolyMathlib.equiv_apply, ← HexMvPolyMathlib.aeval_apply] at hq
    exact hq
  · intro h q hq
    have hle : Ideal.span (HexMvPolyMathlib.equiv '' {M | M ∈ Hex.Matrix.minors r A}) ≤
        RingHom.ker (MvPolynomial.aeval p : MvPolynomial (Fin k) F →ₐ[F] F) := by
      rw [Ideal.span_le]
      rintro _ ⟨M, hM, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, HexMvPolyMathlib.equiv_apply,
        ← HexMvPolyMathlib.aeval_apply]
      exact h M hM
    exact RingHom.mem_ker.mp (hle hq)

end HexDeterminantalIdealMathlib
