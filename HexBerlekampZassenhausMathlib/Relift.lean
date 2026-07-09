/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.IntReductionMod
import all HexBerlekampZassenhausMathlib.IntReductionMod
import all HexBerlekampZassenhausMathlib.ModPFactorization
import all HexBerlekampZassenhausMathlib.HenselFactorProps

public section
set_option backward.proofsInPublic true

/-!
Certification of the recursive per-remainder re-lift (#8625, deliverable 2).

The computational recursion `classicalCoreFactorsRecursive` certifies each
returned factor either through a floor call to `classicalCoreFactorsWithBound`
at the piece's own `ModPFactorization` bundle (whose coverage theorem was
re-keyed to the bundle) or through the two leaf certificates (linear pieces
and mod-p-irreducible pieces). This module proves the leaves, the shape
facts the induction threads through the sub-floor scan (positive leading
coefficient, primitivity, divisibility of the node target), and the main
per-factor irreducibility induction.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-- A primitive integer polynomial of executable degree `1` is irreducible:
any factorization has a constant side, and a constant divisor of a primitive
polynomial is a unit. -/
theorem irreducible_toPolynomial_of_primitive_of_degree_one
    {g : Hex.ZPoly} (hprim : Hex.ZPoly.Primitive g)
    (hdeg : g.degree?.getD 0 = 1) :
    Irreducible (HexPolyZMathlib.toPolynomial g) := by
  have hnd : (HexPolyZMathlib.toPolynomial g).natDegree = 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    exact hdeg
  have hprim_poly : (HexPolyZMathlib.toPolynomial g).IsPrimitive :=
    IntReductionMod.toPolynomial_isPrimitive_of_zpoly_primitive hprim
  have hg_ne : HexPolyZMathlib.toPolynomial g ≠ 0 := by
    intro h0
    rw [h0] at hnd
    simp at hnd
  constructor
  · intro hunit
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro a b hab
    have ha_ne : a ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hab
      exact hg_ne hab
    have hb_ne : b ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hab
      exact hg_ne hab
    have hsum : a.natDegree + b.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul ha_ne hb_ne, ← hab]
      exact hnd
    rcases (by omega : a.natDegree = 0 ∨ b.natDegree = 0) with h0 | h0
    · obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h0
      exact Or.inl (Polynomial.isUnit_C.mpr
        (hprim_poly c (Dvd.intro b hab.symm)))
    · obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h0
      exact Or.inr (Polynomial.isUnit_C.mpr
        (hprim_poly c (Dvd.intro_left a hab.symm)))

/-- `toMathlibPolynomial` sends the zero polynomial to zero. -/
private theorem toMathlibPolynomial_zero'
    {p : Nat} [Hex.ZMod64.Bounds p] :
    HexBerlekampMathlib.toMathlibPolynomial (0 : Hex.FpPoly p) = 0 := by
  apply Polynomial.ext
  intro n
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial, Polynomial.coeff_zero]
  have h0 : (0 : Hex.FpPoly p).coeff n = 0 := Hex.DensePoly.coeff_zero n
  rw [h0]
  exact HexModArithMathlib.ZMod64.toZMod_zero

/-- Transport Mathlib `Irreducible` back to executable `FpPoly.Irreducible`:
a factorization with both sides of positive executable degree would map to a
factorization by non-units. -/
theorem fpPolyIrreducible_of_irreducible_toMathlibPolynomial
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (_root_.Nat.Prime p)]
    {f : Hex.FpPoly p}
    (hirr : Irreducible (HexBerlekampMathlib.toMathlibPolynomial f)) :
    Hex.FpPoly.Irreducible f := by
  constructor
  · intro h0
    apply hirr.ne_zero
    rw [h0]
    exact toMathlibPolynomial_zero'
  · intro a b hab
    have hmap :
        HexBerlekampMathlib.toMathlibPolynomial a *
            HexBerlekampMathlib.toMathlibPolynomial b =
          HexBerlekampMathlib.toMathlibPolynomial f := by
      rw [show HexBerlekampMathlib.toMathlibPolynomial a *
            HexBerlekampMathlib.toMathlibPolynomial b =
          HexBerlekampMathlib.toMathlibPolynomial (a * b) from
        (map_mul (HexBerlekampMathlib.fpPolyEquiv (p := p)) a b).symm, hab]
    have hcases := hirr.isUnit_or_isUnit hmap.symm
    -- A unit image forces executable degree `some 0`.
    have hdeg_of_unit :
        ∀ g : Hex.FpPoly p,
          IsUnit (HexBerlekampMathlib.toMathlibPolynomial g) →
          g.degree? = some 0 := by
      intro g hunit
      have hg_ne : g ≠ 0 := by
        intro h0
        apply hunit.ne_zero
        rw [h0]
        exact toMathlibPolynomial_zero'
      have hsize_pos : 0 < g.size := by
        by_contra hs
        have : g.size = 0 := by omega
        exact hg_ne ((Hex.DensePoly.isZero_eq_true_iff g).mp
          (by simp [Hex.DensePoly.isZero, Hex.DensePoly.size,
            Array.isEmpty_iff_size_eq_zero] at this ⊢; omega) |>
            fun h => by
              apply Hex.DensePoly.ext_coeff
              intro n
              rw [Hex.DensePoly.coeff_zero]
              exact Hex.DensePoly.coeff_eq_zero_of_size_le g (by omega))
      have htop_ne : g.coeff (g.size - 1) ≠ 0 :=
        Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hsize_pos
      have hnd0 : (HexBerlekampMathlib.toMathlibPolynomial g).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hunit
      have hsize1 : g.size = 1 := by
        by_contra hs1
        have h2 : 2 ≤ g.size := by omega
        have hcoeff_ne :
            (HexBerlekampMathlib.toMathlibPolynomial g).coeff (g.size - 1) ≠ 0 := by
          rw [HexBerlekampMathlib.coeff_toMathlibPolynomial]
          intro h
          apply htop_ne
          have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
          apply hinj
          rw [HexModArithMathlib.ZMod64.equiv_apply, h,
            ← HexModArithMathlib.ZMod64.toZMod_zero,
            ← HexModArithMathlib.ZMod64.equiv_apply]
        have hle := Polynomial.le_natDegree_of_ne_zero hcoeff_ne
        omega
      unfold Hex.DensePoly.degree?
      rw [dif_neg (by omega : ¬ g.size = 0), hsize1]
    rcases hcases with h | h
    · exact Or.inl (hdeg_of_unit a h)
    · exact Or.inr (hdeg_of_unit b h)

/-! ### Shape facts threaded through the sub-floor scan -/

/-- Every peel candidate is either monic (fast path) or the sign-normalized
primitive part of some polynomial (slow path). -/
theorem subFloorPeelSize_cand_shape {p : Nat} [Hex.ZMod64.Bounds p]
    (coreLc : Int) (target : Hex.ZPoly) (modulus qbound : Nat) :
    ∀ (l : List (List (Hex.ZPoly × Hex.FpPoly p) ×
        List (Hex.ZPoly × Hex.FpPoly p)))
      {cand : Hex.ZPoly} {seeds : List (Hex.FpPoly p)} {quot : Hex.ZPoly}
      {rest : List (Hex.ZPoly × Hex.FpPoly p)},
      Hex.subFloorPeelSize coreLc target modulus qbound l =
        some (cand, seeds, quot, rest) →
      Hex.DensePoly.Monic cand ∨
        ∃ X : Hex.ZPoly,
          cand = Hex.normalizeFactorSign (Hex.ZPoly.primitivePart X)
  | [], _, _, _, _, h => by simp [Hex.subFloorPeelSize] at h
  | sc :: tail, cand, seeds, quot, rest, h => by
      simp only [Hex.subFloorPeelSize] at h
      split at h
      · exact subFloorPeelSize_cand_shape coreLc target modulus qbound tail h
      · split at h
        · rename_i hfast
          split at h
          · split at h
            · rename_i quotient hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hcand, -, -, -⟩ := h
              subst hcand
              left
              rw [Bool.and_eq_true] at hfast
              exact beq_iff_eq.mp hfast.2
            · exact subFloorPeelSize_cand_shape coreLc target modulus qbound tail h
          · exact subFloorPeelSize_cand_shape coreLc target modulus qbound tail h
        · split at h
          · split at h
            · rename_i quotient hq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hcand, -, -, -⟩ := h
              subst hcand
              right
              exact ⟨_, rfl⟩
            · exact subFloorPeelSize_cand_shape coreLc target modulus qbound tail h
          · exact subFloorPeelSize_cand_shape coreLc target modulus qbound tail h

/-- The shape transfers along the size levels. -/
theorem subFloorPeel?_cand_shape {p : Nat} [Hex.ZMod64.Bounds p]
    (coreLc : Int) (target : Hex.ZPoly) (modulus qbound : Nat)
    (pairs : List (Hex.ZPoly × Hex.FpPoly p)) :
    ∀ (sizes : List Nat)
      {cand : Hex.ZPoly} {seeds : List (Hex.FpPoly p)} {quot : Hex.ZPoly}
      {rest : List (Hex.ZPoly × Hex.FpPoly p)},
      Hex.subFloorPeel? coreLc target modulus qbound pairs sizes =
        some (cand, seeds, quot, rest) →
      Hex.DensePoly.Monic cand ∨
        ∃ X : Hex.ZPoly,
          cand = Hex.normalizeFactorSign (Hex.ZPoly.primitivePart X)
  | [], _, _, _, _, h => by simp [Hex.subFloorPeel?] at h
  | d :: ds, cand, seeds, quot, rest, h => by
      simp only [Hex.subFloorPeel?] at h
      generalize hlev : Hex.subFloorPeelSize coreLc target modulus qbound
        (Hex.subsetsOfSizeWithComplement pairs d) = res at h
      cases res with
      | none => exact subFloorPeel?_cand_shape coreLc target modulus qbound pairs ds h
      | some r =>
          cases h
          exact subFloorPeelSize_cand_shape coreLc target modulus qbound _ hlev

/-- `toPolynomial` reflects zero. -/
private theorem zpoly_eq_zero_of_toPolynomial_eq_zero
    {f : Hex.ZPoly} (h : HexPolyZMathlib.toPolynomial f = 0) : f = 0 := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_zero]
  have := congrArg (fun q => Polynomial.coeff q n) h
  simpa [HexPolyZMathlib.coeff_toPolynomial] using this

/-- Positive leading coefficient and primitivity for a peel candidate, from
its shape and nonzero-ness. -/
private theorem cand_lc_pos_and_primitive
    (cand : Hex.ZPoly) (hcand_ne : cand ≠ 0)
    (hshape : Hex.DensePoly.Monic cand ∨
      ∃ X : Hex.ZPoly,
        cand = Hex.normalizeFactorSign (Hex.ZPoly.primitivePart X)) :
    0 < Hex.DensePoly.leadingCoeff cand ∧ Hex.ZPoly.Primitive cand := by
  rcases hshape with hmonic | ⟨X, rfl⟩
  · refine ⟨?_, zpoly_primitive_of_monic hmonic⟩
    rw [show Hex.DensePoly.leadingCoeff cand = 1 from hmonic]
    exact Int.one_pos
  · have hpp_ne : Hex.ZPoly.primitivePart X ≠ 0 := by
      intro h0
      apply hcand_ne
      rw [h0]
      rfl
    have hcontent_ne : Hex.ZPoly.content X ≠ 0 := by
      intro h0
      exact hpp_ne (Hex.DensePoly.primitivePart_eq_zero_of_content_eq_zero X h0)
    have hprim : Hex.ZPoly.Primitive (Hex.ZPoly.primitivePart X) :=
      Hex.ZPoly.primitivePart_primitive X hcontent_ne
    refine ⟨?_, Hex.normalizeFactorSign_primitive _ hprim⟩
    have hnonneg := leadingCoeff_normalizeFactorSign_nonneg
      (Hex.ZPoly.primitivePart X)
    have hlc_ne : Hex.DensePoly.leadingCoeff
        (Hex.normalizeFactorSign (Hex.ZPoly.primitivePart X)) ≠ 0 := by
      intro h0
      apply hcand_ne
      have hsize0 : (Hex.normalizeFactorSign
          (Hex.ZPoly.primitivePart X)).size = 0 := by
        by_contra hs
        have hpos : 0 < (Hex.normalizeFactorSign
            (Hex.ZPoly.primitivePart X)).size := Nat.pos_of_ne_zero hs
        have := Hex.DensePoly.coeff_last_ne_zero_of_pos_size _ hpos
        rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last _ hpos] at this
        exact this h0
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le _ (by omega)
    omega

/-- Positive leading coefficient, primitivity, nonzero-ness, and divisibility
of the node target, for every piece the greedy rung scan emits. -/
theorem subFloorScan_piece_facts {p : Nat} [Hex.ZMod64.Bounds p]
    (coreLc : Int) (modulus cap qbound : Nat) (g₀ : Hex.ZPoly) :
    ∀ (fuel : Nat) (target : Hex.ZPoly)
      (pairs : List (Hex.ZPoly × Hex.FpPoly p))
      (acc : Array (Hex.ZPoly × List (Hex.FpPoly p)))
      {piece : Hex.ZPoly} {seeds : List (Hex.FpPoly p)},
      (piece, seeds) ∈
        Hex.subFloorScan coreLc modulus cap qbound fuel target pairs acc →
      (∀ pc ∈ acc,
        (0 < Hex.DensePoly.leadingCoeff pc.1 ∧ Hex.ZPoly.Primitive pc.1) ∧
          pc.1 ≠ 0 ∧ pc.1 ∣ g₀) →
      0 < Hex.DensePoly.leadingCoeff target →
      Hex.ZPoly.Primitive target →
      target ≠ 0 →
      target ∣ g₀ →
      (0 < Hex.DensePoly.leadingCoeff piece ∧ Hex.ZPoly.Primitive piece) ∧
        piece ≠ 0 ∧ piece ∣ g₀
  | 0, target, pairs, acc, piece, seeds, hmem, hacc, hlc, hprim, hne, hdvd => by
      simp only [Hex.subFloorScan] at hmem
      rcases Array.mem_push.mp hmem with hmem | hmem
      · exact hacc _ hmem
      · have hpiece : piece = target := congrArg Prod.fst hmem
        subst hpiece
        exact ⟨⟨hlc, hprim⟩, hne, hdvd⟩
  | fuel + 1, target, pairs, acc, piece, seeds, hmem, hacc, hlc, hprim, hne, hdvd => by
      simp only [Hex.subFloorScan] at hmem
      generalize hpeel : Hex.subFloorPeel? coreLc target modulus qbound pairs
        ((List.range (min cap (pairs.length / 2))).map (· + 1)) = res at hmem
      cases res with
      | none =>
          rcases Array.mem_push.mp hmem with hmem | hmem
          · exact hacc _ hmem
          · have hpiece : piece = target := congrArg Prod.fst hmem
            subst hpiece
            exact ⟨⟨hlc, hprim⟩, hne, hdvd⟩
      | some r =>
          obtain ⟨cand, cseeds, quot, rest⟩ := r
          have hqc : quot * cand = target :=
            Hex.subFloorPeel?_product coreLc target modulus qbound pairs _ hpeel
          -- Mathlib-side product identity for sign and nonzero reasoning.
          have hqc_poly :
              HexPolyZMathlib.toPolynomial quot *
                  HexPolyZMathlib.toPolynomial cand =
                HexPolyZMathlib.toPolynomial target := by
            rw [← HexPolyZMathlib.toPolynomial_mul, hqc]
          have htarget_poly_ne : HexPolyZMathlib.toPolynomial target ≠ 0 := by
            intro h0
            exact hne (zpoly_eq_zero_of_toPolynomial_eq_zero h0)
          have hcand_ne : cand ≠ 0 := by
            intro h0
            apply htarget_poly_ne
            rw [← hqc_poly, h0, HexPolyZMathlib.toPolynomial_zero, mul_zero]
          have hquot_ne : quot ≠ 0 := by
            intro h0
            apply htarget_poly_ne
            rw [← hqc_poly, h0, HexPolyZMathlib.toPolynomial_zero, zero_mul]
          -- Candidate facts.
          have hcand_shape := subFloorPeel?_cand_shape coreLc target modulus
            qbound pairs _ hpeel
          obtain ⟨hcand_lc, hcand_prim⟩ :=
            cand_lc_pos_and_primitive cand hcand_ne hcand_shape
          have hcand_dvd_t : cand ∣ target :=
            ⟨quot, by rw [← hqc, Hex.DensePoly.mul_comm_poly]⟩
          have hquot_dvd_t : quot ∣ target := ⟨cand, hqc.symm⟩
          obtain ⟨w, hw⟩ := hdvd
          have hcand_dvd : cand ∣ g₀ := by
            rcases hcand_dvd_t with ⟨y, hy⟩
            exact ⟨y * w, by
              rw [hw, hy, Hex.DensePoly.mul_assoc_poly]⟩
          have hquot_dvd : quot ∣ g₀ := by
            rcases hquot_dvd_t with ⟨y, hy⟩
            exact ⟨y * w, by
              rw [hw, hy, Hex.DensePoly.mul_assoc_poly]⟩
          -- Quotient sign: over `ℤ[X]` leading coefficients multiply.
          have hlc_quot : 0 < Hex.DensePoly.leadingCoeff quot := by
            have hmul := Polynomial.leadingCoeff_mul
              (HexPolyZMathlib.toPolynomial quot)
              (HexPolyZMathlib.toPolynomial cand)
            rw [hqc_poly, HexPolyMathlib.leadingCoeff_toPolynomial,
              HexPolyMathlib.leadingCoeff_toPolynomial,
              HexPolyMathlib.leadingCoeff_toPolynomial] at hmul
            by_contra hq
            push_neg at hq
            have hprod_nonpos :
                Hex.DensePoly.leadingCoeff quot *
                  Hex.DensePoly.leadingCoeff cand ≤ 0 :=
              mul_nonpos_iff.mpr (Or.inr ⟨hq, le_of_lt hcand_lc⟩)
            rw [← hmul] at hprod_nonpos
            omega
          have hquot_prim : Hex.ZPoly.Primitive quot :=
            zpoly_primitive_of_dvd_primitive_basic hprim hquot_dvd_t
          -- Recurse on the peeled state.
          refine subFloorScan_piece_facts coreLc modulus cap qbound g₀ fuel quot
            rest (acc.push (cand, cseeds)) hmem ?_ hlc_quot hquot_prim
            hquot_ne hquot_dvd
          intro pc hpc
          rcases Array.mem_push.mp hpc with hpc | hpc
          · exact hacc _ hpc
          · have h1 : pc.1 = cand := congrArg Prod.fst hpc
            rw [h1]
            exact ⟨⟨hcand_lc, hcand_prim⟩, hcand_ne, hcand_dvd⟩

/-- Ladder-level piece facts: every piece of a successful sub-floor split is
nonzero, primitive, has positive leading coefficient, and divides the node
target. -/
theorem reliftLadder_piece_facts
    (pd : Hex.PrimeChoiceData) (cap : Nat) (g : Hex.ZPoly)
    (floorK qbound : Nat)
    (hg_lc : 0 < Hex.DensePoly.leadingCoeff g)
    (hg_prim : Hex.ZPoly.Primitive g)
    (hg_ne : g ≠ 0) :
    ∀ (k fuel : Nat) {pieces} {piece : Hex.ZPoly}
      {seeds :
        letI := pd.bounds
        List (Hex.FpPoly pd.p)},
      Hex.reliftLadder pd cap g floorK qbound k fuel = some pieces →
      (piece, seeds) ∈ pieces →
      (0 < Hex.DensePoly.leadingCoeff piece ∧ Hex.ZPoly.Primitive piece) ∧
        piece ≠ 0 ∧ piece ∣ g
  | k, 0, pieces, piece, seeds, h, _ => by simp [Hex.reliftLadder] at h
  | k, fuel + 1, pieces, piece, seeds, h, hmem => by
      letI := pd.bounds
      simp only [Hex.reliftLadder] at h
      split at h
      · split at h
        · cases h
          exact subFloorScan_piece_facts (Hex.DensePoly.leadingCoeff g)
            (pd.p ^ k) cap qbound g _ g _ #[] hmem (by simp) hg_lc hg_prim
            hg_ne (Hex.DensePoly.dvd_refl_poly g)
        · exact reliftLadder_piece_facts pd cap g floorK qbound hg_lc hg_prim
            hg_ne (2 * k) fuel h hmem
      · simp at h

/-- The r = 1 leaf: a node whose bundle records a single mod-p factor is
irreducible — the monic transform is irreducible mod `p`, hence over `ℤ`,
hence so is the node. -/
theorem node_irreducible_of_singleton_factor
    {g : Hex.ZPoly} {pd : Hex.PrimeChoiceData}
    (hval : ModPFactorization (Hex.ZPoly.toMonic g).monic pd)
    (hsize : pd.factorsModP.size = 1)
    (hg_lc : 0 < Hex.DensePoly.leadingCoeff g)
    (hg_prim : Hex.ZPoly.Primitive g)
    (hg_deg : 2 ≤ g.degree?.getD 0) :
    Irreducible (HexPolyZMathlib.toPolynomial g) := by
  letI := pd.bounds
  haveI : Fact (_root_.Nat.Prime pd.p) := ⟨natPrime_of_hexNatPrime hval.prime⟩
  have hp1 : 1 < pd.p := by have := hval.prime.two_le; omega
  set f := (Hex.ZPoly.toMonic g).monic with hf_def
  have hg_pos : 0 < g.degree?.getD 0 := by omega
  have hmonicT : Hex.DensePoly.Monic f :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree g hg_lc hg_pos
  -- The single factor equals the modular image of the monic transform.
  set u := pd.factorsModP[0]'(by omega) with hu_def
  have harr : pd.factorsModP = #[u] := by
    apply Array.ext
    · simp [hsize]
    · intro i hi₁ hi₂
      simp at hi₂
      subst hi₂
      rfl
  have hcongr := hval.product_congr_target hmonicT
  rw [harr] at hcongr
  have hprod_eq :
      Array.polyProduct ((#[u] : Array _).map Hex.FpPoly.liftToZ) =
        Hex.FpPoly.liftToZ u := by
    rw [show (#[u] : Array _).map Hex.FpPoly.liftToZ =
        #[Hex.FpPoly.liftToZ u] by simp]
    exact Hex.ZPoly.polyProduct_singleton _
  rw [hprod_eq] at hcongr
  have hu_eq : u = Hex.ZPoly.modP pd.p f := by
    have hmod := Hex.ZPoly.modP_eq_of_congr pd.p _ _ hcongr
    rwa [Hex.FpPoly.modP_liftToZ] at hmod
  -- Mathlib irreducibility of the factor, transported to the executable side.
  have hirr_u : Irreducible
      (HexBerlekampMathlib.toMathlibPolynomial u) := by
    have := hval.irreducible ⟨0, by omega⟩
    simpa [modPFactor, hu_def] using this
  have hirr_fp : Hex.FpPoly.Irreducible (Hex.ZPoly.modP pd.p f) := by
    rw [← hu_eq]
    exact fpPolyIrreducible_of_irreducible_toMathlibPolynomial hirr_u
  -- Descend to `ℤ`-irreducibility of the transform, then of the node.
  have hf_deg : f.degree?.getD 0 = g.degree?.getD 0 := by
    rw [hf_def]
    simpa [Hex.ZPoly.toMonic_degree] using
      Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree g hg_lc hg_pos
  have hf_size : 1 < f.size := by
    have hne : f.size ≠ 0 := by
      intro h0
      have : f.degree?.getD 0 = 0 := by
        unfold Hex.DensePoly.degree?
        rw [dif_pos h0]
        rfl
      omega
    have : f.degree?.getD 0 = f.size - 1 := by
      unfold Hex.DensePoly.degree?
      rw [dif_neg hne]
      rfl
    omega
  have hadm : Hex.leadingCoeffAdmissible f pd.p := by
    show Hex.ZPoly.leadingCoeffModP f pd.p ≠ 0
    unfold Hex.ZPoly.leadingCoeffModP
    rw [show Hex.DensePoly.leadingCoeff f = 1 from hmonicT]
    intro h0
    have hnat := congrArg Hex.ZMod64.toNat h0
    have hint : Hex.ZPoly.intModNat (1 : Int) pd.p = 1 := by
      show Int.toNat ((1 : Int) % Int.ofNat pd.p) = 1
      have : (1 : Int) % Int.ofNat pd.p = 1 :=
        Int.emod_eq_of_lt (by decide) (Int.ofNat_lt.mpr hp1)
      rw [this]
      rfl
    rw [Hex.ZMod64.toNat_ofNat, hint,
      show (0 : Hex.ZMod64 pd.p) = Hex.ZMod64.zero from rfl,
      Hex.ZMod64.toNat_zero, Nat.mod_eq_of_lt hp1] at hnat
    exact one_ne_zero hnat
  have hf_irr : Hex.ZPoly.Irreducible f :=
    Hex.ZPoly.Irreducible_of_modP_irreducible_of_primitive_of_admissible
      f pd.p hval.prime (zpoly_primitive_of_monic hmonicT) hadm hf_size hirr_fp
  have hg_irr : Hex.ZPoly.Irreducible g :=
    zpolyIrreducible_of_toMonicMonic_irreducible g hg_lc hg_pos hg_prim hf_irr
  exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible g).mp hg_irr

/-- Per-member irreducibility from the bundle's per-index field. -/
theorem ModPFactorization.irreducible_mem
    {f : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (h : ModPFactorization f data) :
    letI := data.bounds
    ∀ u ∈ data.factorsModP,
      Irreducible (HexBerlekampMathlib.toMathlibPolynomial u) := by
  letI := data.bounds
  intro u hu
  obtain ⟨i, hi, hieq⟩ := Array.mem_iff_getElem.mp hu
  have := h.irreducible ⟨i, hi⟩
  simpa [modPFactor, hieq] using this

/-- A successful recursion node has positive degree (the degree-0 branch
declines). -/
theorem classicalCoreFactorsRecursiveAux_some_deg_pos
    {cap fuel : Nat} {g : Hex.ZPoly} {B? : Option Nat}
    {pd : Hex.PrimeChoiceData} {out : Array Hex.ZPoly}
    (h : Hex.classicalCoreFactorsRecursiveAux cap fuel g B? pd = some out) :
    0 < g.degree?.getD 0 := by
  cases fuel with
  | zero => simp [Hex.classicalCoreFactorsRecursiveAux] at h
  | succ fuel =>
      simp only [Hex.classicalCoreFactorsRecursiveAux] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hdeg0
        omega
      all_goals
        rename_i hdeg0 _
        omega

/-- Folding the recursion step over `none` stays `none`. -/
private theorem foldl_relift_step_none
    {q : Nat} [Hex.ZMod64.Bounds q] (cap fuel : Nat) (lcg : Int) :
    ∀ (l : List (Hex.ZPoly × List (Hex.FpPoly q))),
      l.foldl (fun acc? piece => acc?.bind fun acc =>
        (Hex.piecePrimeData? piece.1
            (lcg / Hex.DensePoly.leadingCoeff piece.1) piece.2).bind
          fun pdPiece =>
            (Hex.classicalCoreFactorsRecursiveAux cap fuel piece.1 none
              pdPiece).map (acc ++ ·)) none = none
  | [] => rfl
  | pc :: l => by
      rw [List.foldl_cons]
      exact foldl_relift_step_none cap fuel lcg l

/-- Folding the per-piece certification step: if every piece certifies its
output and the accumulator is certified, the fold's output is certified. -/
private theorem fold_pieces_irreducible
    {q : Nat} [Hex.ZMod64.Bounds q]
    (cap fuel : Nat) (lcg : Int)
    (Irr : Hex.ZPoly → Prop)
    (GoodPiece : Hex.ZPoly × List (Hex.FpPoly q) → Prop)
    (hchild : ∀ (piece : Hex.ZPoly) (seeds : List (Hex.FpPoly q))
        (pdP : Hex.PrimeChoiceData) (out : Array Hex.ZPoly),
      Hex.piecePrimeData? piece (lcg / Hex.DensePoly.leadingCoeff piece)
        seeds = some pdP →
      Hex.classicalCoreFactorsRecursiveAux cap fuel piece none pdP = some out →
      GoodPiece (piece, seeds) →
      ∀ f ∈ out.toList, Irr f) :
    ∀ (l : List (Hex.ZPoly × List (Hex.FpPoly q))) (acc : Array Hex.ZPoly)
      {cf : Array Hex.ZPoly},
      l.foldl (fun acc? piece => acc?.bind fun acc =>
        (Hex.piecePrimeData? piece.1
            (lcg / Hex.DensePoly.leadingCoeff piece.1) piece.2).bind
          fun pdPiece =>
            (Hex.classicalCoreFactorsRecursiveAux cap fuel piece.1 none
              pdPiece).map (acc ++ ·)) (some acc) = some cf →
      (∀ f ∈ acc.toList, Irr f) →
      (∀ pc ∈ l, GoodPiece pc) →
      ∀ f ∈ cf.toList, Irr f
  | [], acc, cf, h, hacc, _ => by
      simp only [List.foldl_nil, Option.some.injEq] at h
      subst h
      exact hacc
  | pc :: l, acc, cf, h, hacc, hgood => by
      rw [List.foldl_cons] at h
      generalize hpdP : Hex.piecePrimeData? pc.1
        (lcg / Hex.DensePoly.leadingCoeff pc.1) pc.2 = resP at h
      cases resP with
      | none =>
          simp only [Option.bind_some, Option.bind_none] at h
          rw [foldl_relift_step_none cap fuel lcg l] at h
          exact absurd h (by simp)
      | some pdP =>
          simp only [Option.bind_some] at h
          generalize hout : Hex.classicalCoreFactorsRecursiveAux cap fuel pc.1
            none pdP = resO at h
          cases resO with
          | none =>
              simp only [Option.map_none] at h
              rw [foldl_relift_step_none cap fuel lcg l] at h
              exact absurd h (by simp)
          | some out =>
              simp only [Option.map_some] at h
              refine fold_pieces_irreducible cap fuel lcg Irr GoodPiece hchild
                l (acc ++ out) h ?_
                (fun pc' hpc' => hgood pc' (List.mem_cons_of_mem pc hpc'))
              intro f hf
              rw [Array.toList_append, List.mem_append] at hf
              rcases hf with hf | hf
              · exact hacc f hf
              · exact hchild pc.1 pc.2 pdP out hpdP hout
                  (hgood pc List.mem_cons_self) f hf

/-- **Per-factor irreducibility for the recursive per-remainder re-lift.**
Every factor the recursion returns for a primitive, positive-lc, squarefree
node with a semantic mod-p factorization bundle is irreducible over `ℤ`. -/
theorem classicalCoreFactorsRecursiveAux_factor_irreducible (cap : Nat) :
    ∀ (fuel : Nat) (g : Hex.ZPoly) (B? : Option Nat)
      (pd : Hex.PrimeChoiceData) {cf : Array Hex.ZPoly},
      Hex.classicalCoreFactorsRecursiveAux cap fuel g B? pd = some cf →
      ModPFactorization (Hex.ZPoly.toMonic g).monic pd →
      Hex.ZPoly.Primitive g →
      0 < Hex.DensePoly.leadingCoeff g →
      Squarefree (HexPolyZMathlib.toPolynomial g) →
      (∀ B, B? = some B → B ≠ 0 ∧ ∃ B' : Nat,
        (Hex.DensePoly.leadingCoeff g).natAbs ≤ B' ∧
        (∀ d : Hex.ZPoly, d ∣ g → ∀ i, (d.coeff i).natAbs ≤ B') ∧
        2 * B' < pd.p ^ Hex.precisionForCoeffBound
          (Hex.ZPoly.exhaustiveLiftBound g B) pd.p) →
      ∀ f ∈ cf.toList, Irreducible (HexPolyZMathlib.toPolynomial f)
  | 0, g, B?, pd, cf, h, _, _, _, _, _ => by
      simp [Hex.classicalCoreFactorsRecursiveAux] at h
  | fuel + 1, g, B?, pd, cf, h, hval, hprim, hlc, hsq, hB => by
      letI := pd.bounds
      have hg_ne : g ≠ 0 := zpoly_ne_zero_of_pos_lc hlc
      simp only [Hex.classicalCoreFactorsRecursiveAux] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hdeg0
        split at h
        · -- degree-1 leaf
          rename_i hdeg1
          rw [Option.some.injEq] at h
          subst h
          intro f hf
          rw [show (#[g] : Array Hex.ZPoly).toList = [g] from rfl,
            List.mem_singleton] at hf
          subst hf
          exact irreducible_toPolynomial_of_primitive_of_degree_one hprim hdeg1
        · rename_i hdeg1
          split at h
          · -- r = 1 leaf
            rename_i hsize
            rw [Option.some.injEq] at h
            subst h
            intro f hf
            rw [show (#[g] : Array Hex.ZPoly).toList = [g] from rfl,
              List.mem_singleton] at hf
            subst hf
            exact node_irreducible_of_singleton_factor hval
              (by simpa using hsize) hlc hprim (by omega)
          · -- ladder / floor
            rename_i hsize
            have hg_pos : 0 < g.degree?.getD 0 := by omega
            split at h
            · -- sub-floor split: certify each piece recursively
              rename_i pieces hladder
              rw [← Array.foldl_toList] at h
              refine fold_pieces_irreducible cap fuel
                (Hex.DensePoly.leadingCoeff g) _
                (fun pc => ((0 < Hex.DensePoly.leadingCoeff pc.1 ∧
                    Hex.ZPoly.Primitive pc.1) ∧ pc.1 ≠ 0 ∧ pc.1 ∣ g) ∧
                  ∀ u ∈ pc.2, u ∈ pd.factorsModP)
                ?_ pieces.toList #[] h (by simp) ?_
              · intro piece seeds pdP out hpdP hout hgoodpc
                obtain ⟨⟨⟨hpc_lc, hpc_prim⟩, hpc_ne, hpc_dvd⟩, hseeds⟩ := hgoodpc
                have hpc_pos : 0 < piece.degree?.getD 0 :=
                  classicalCoreFactorsRecursiveAux_some_deg_pos hout
                have hmonicT :
                    Hex.DensePoly.Monic (Hex.ZPoly.toMonic piece).monic :=
                  Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree piece hpc_lc
                    hpc_pos
                have hpc_sq : Squarefree (HexPolyZMathlib.toPolynomial piece) :=
                  Squarefree.squarefree_of_dvd
                    (HexPolyMathlib.toPolynomial_dvd hpc_dvd) hsq
                have hbundle :
                    ModPFactorization (Hex.ZPoly.toMonic piece).monic pdP :=
                  modPFactorization_of_piecePrimeData hval.prime hmonicT
                    (fun u hu => hval.irreducible_mem u (hseeds u hu)) hpdP
                exact classicalCoreFactorsRecursiveAux_factor_irreducible cap
                  fuel piece none pdP hout hbundle hpc_prim hpc_lc hpc_sq
                  (fun B hB' => by cases hB')
              · intro pc hpc
                have hpc_arr : pc ∈ pieces := by
                  rwa [← Array.mem_toList_iff]
                obtain ⟨piece, seeds⟩ := pc
                refine ⟨reliftLadder_piece_facts pd cap g _ _ hlc hprim hg_ne
                  _ _ hladder hpc_arr, ?_⟩
                intro u hu
                exact Hex.reliftLadder_seeds_mem pd cap g _ _ _ _ hladder
                  hpc_arr u hu
            · -- floor: today's full scan at the node's own bundle
              cases hBo : B? with
              | some B =>
                  rw [hBo] at h
                  obtain ⟨hB_ne, B', hlc_le, hvalid, hprecision⟩ := hB B hBo
                  exact
                    classicalCoreFactorsWithBound_factor_irreducible_of_validBound
                      g B pd (by simpa using h) hval hg_ne hprim hlc hsq hg_pos
                      hB_ne B' hlc_le hvalid hprecision
              | none =>
                  rw [hBo] at h
                  have hdfb_pos : 0 < Hex.ZPoly.defaultFactorCoeffBound g :=
                    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hg_ne
                  have hB_ne : Hex.ZPoly.defaultFactorCoeffBound g ≠ 0 := by
                    omega
                  have hp2 : 2 ≤ pd.p := hval.prime.two_le
                  have hprecision :
                      2 * Hex.ZPoly.defaultFactorCoeffBound g <
                        pd.p ^ Hex.precisionForCoeffBound
                          (Hex.ZPoly.exhaustiveLiftBound g
                            (Hex.ZPoly.defaultFactorCoeffBound g)) pd.p := by
                    have hle : Hex.ZPoly.defaultFactorCoeffBound g ≤
                        Hex.ZPoly.exhaustiveLiftBound g
                          (Hex.ZPoly.defaultFactorCoeffBound g) :=
                      Hex.ZPoly.le_exhaustiveLiftBound g _
                    have hspec := Hex.precisionForCoeffBound_spec hp2
                      (Hex.ZPoly.exhaustiveLiftBound g
                        (Hex.ZPoly.defaultFactorCoeffBound g))
                    omega
                  exact
                    classicalCoreFactorsWithBound_factor_irreducible_of_validBound
                      g (Hex.ZPoly.defaultFactorCoeffBound g) pd
                      (by simpa using h) hval hg_ne hprim hlc hsq hg_pos hB_ne
                      (Hex.ZPoly.defaultFactorCoeffBound g)
                      (defaultFactorCoeffBound_leadingCoeff_natAbs_le hg_ne)
                      (defaultFactorCoeffBound_valid g hg_ne) hprecision

/-- **Entry-point irreducibility for `classicalCoreFactorsRecursive`.**
Mirror of `classicalCoreFactorsWithBound_factor_irreducible`, keyed to the
node's semantic bundle. -/
theorem classicalCoreFactorsRecursive_factor_irreducible_of_validBound
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {cf : Array Hex.ZPoly}
    (hclassical :
      Hex.classicalCoreFactorsRecursive core B primeData = some cf)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne : B ≠ 0)
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ d : Hex.ZPoly, d ∣ core → ∀ i, (d.coeff i).natAbs ≤ B')
    (hprecision : 2 * B' <
      primeData.p ^ Hex.precisionForCoeffBound
        (Hex.ZPoly.exhaustiveLiftBound core B) primeData.p) :
    ∀ g ∈ cf.toList, Irreducible (HexPolyZMathlib.toPolynomial g) := by
  unfold Hex.classicalCoreFactorsRecursive at hclassical
  rw [if_neg hB_ne] at hclassical
  exact classicalCoreFactorsRecursiveAux_factor_irreducible
    Hex.reliftSubFloorCap _ core (some B) primeData hclassical hval
    hcore_primitive hcore_lc_pos hcore_sqfree
    (fun B'' hB'' => by
      cases hB''
      exact ⟨hB_ne, B', hcore_lc_le, hvalid, hprecision⟩)

theorem classicalCoreFactorsRecursive_factor_irreducible
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {cf : Array Hex.ZPoly}
    (hclassical :
      Hex.classicalCoreFactorsRecursive core B primeData = some cf)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hbound_le : Hex.ZPoly.defaultFactorCoeffBound core ≤ B) :
    ∀ g ∈ cf.toList, Irreducible (HexPolyZMathlib.toPolynomial g) := by
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hdfb_pos : 0 < Hex.ZPoly.defaultFactorCoeffBound core :=
    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
  have hB_ne : B ≠ 0 := by omega
  have hp2 : 2 ≤ primeData.p := hval.prime.two_le
  have hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        primeData.p ^ Hex.precisionForCoeffBound
          (Hex.ZPoly.exhaustiveLiftBound core B) primeData.p := by
    have hle : Hex.ZPoly.defaultFactorCoeffBound core ≤
        Hex.ZPoly.exhaustiveLiftBound core B :=
      le_trans hbound_le (Hex.ZPoly.le_exhaustiveLiftBound core B)
    have hspec := Hex.precisionForCoeffBound_spec hp2
      (Hex.ZPoly.exhaustiveLiftBound core B)
    omega
  exact classicalCoreFactorsRecursive_factor_irreducible_of_validBound
    core B primeData hclassical hval hcore_primitive hcore_lc_pos hcore_sqfree
    hB_ne (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
    (defaultFactorCoeffBound_valid core hcore_ne) hprecision

/-! ### Structural companions: product, sign normalization, degree -/

/-- Fold-level product reconstruction: each certified piece's output
multiplies to the piece, so the fold's output multiplies to the accumulator
times the pieces. -/
private theorem fold_pieces_product
    {q : Nat} [Hex.ZMod64.Bounds q] (cap fuel : Nat) (lcg : Int)
    (hchild : ∀ (piece : Hex.ZPoly) (seeds : List (Hex.FpPoly q))
        (pdP : Hex.PrimeChoiceData) (out : Array Hex.ZPoly),
      Hex.piecePrimeData? piece (lcg / Hex.DensePoly.leadingCoeff piece)
        seeds = some pdP →
      Hex.classicalCoreFactorsRecursiveAux cap fuel piece none pdP = some out →
      Array.polyProduct out = piece) :
    ∀ (l : List (Hex.ZPoly × List (Hex.FpPoly q))) (acc : Array Hex.ZPoly)
      {cf : Array Hex.ZPoly},
      l.foldl (fun acc? piece => acc?.bind fun acc =>
        (Hex.piecePrimeData? piece.1
            (lcg / Hex.DensePoly.leadingCoeff piece.1) piece.2).bind
          fun pdPiece =>
            (Hex.classicalCoreFactorsRecursiveAux cap fuel piece.1 none
              pdPiece).map (acc ++ ·)) (some acc) = some cf →
      Array.polyProduct cf =
        Array.polyProduct acc * Array.polyProduct ((l.map (·.1)).toArray)
  | [], acc, cf, h => by
      simp only [List.foldl_nil, Option.some.injEq] at h
      subst h
      simp [Array.polyProduct, Hex.DensePoly.mul_comm_poly (S := Int)]
  | pc :: l, acc, cf, h => by
      rw [List.foldl_cons] at h
      generalize hpdP : Hex.piecePrimeData? pc.1
        (lcg / Hex.DensePoly.leadingCoeff pc.1) pc.2 = resP at h
      cases resP with
      | none =>
          simp only [Option.bind_some, Option.bind_none] at h
          rw [foldl_relift_step_none cap fuel lcg l] at h
          exact absurd h (by simp)
      | some pdP =>
          simp only [Option.bind_some] at h
          generalize hout : Hex.classicalCoreFactorsRecursiveAux cap fuel pc.1
            none pdP = resO at h
          cases resO with
          | none =>
              simp only [Option.map_none] at h
              rw [foldl_relift_step_none cap fuel lcg l] at h
              exact absurd h (by simp)
          | some out =>
              simp only [Option.map_some] at h
              have hrec := fold_pieces_product cap fuel lcg hchild l
                (acc ++ out) h
              have hout_prod : Array.polyProduct out = pc.1 :=
                hchild pc.1 pc.2 pdP out hpdP hout
              rw [hrec, Hex.ZPoly.polyProduct_append, hout_prod,
                List.map_cons, Hex.ZPoly.polyProduct_cons_toArray]
              rw [Hex.DensePoly.mul_assoc_poly]

/-- Product reconstruction for the recursion: the returned factors multiply
back to the node. -/
theorem classicalCoreFactorsRecursiveAux_polyProduct (cap : Nat) :
    ∀ (fuel : Nat) (g : Hex.ZPoly) (B? : Option Nat)
      (pd : Hex.PrimeChoiceData) {cf : Array Hex.ZPoly},
      Hex.classicalCoreFactorsRecursiveAux cap fuel g B? pd = some cf →
      Array.polyProduct cf = g
  | 0, g, B?, pd, cf, h => by
      simp [Hex.classicalCoreFactorsRecursiveAux] at h
  | fuel + 1, g, B?, pd, cf, h => by
      letI := pd.bounds
      simp only [Hex.classicalCoreFactorsRecursiveAux] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · rw [Option.some.injEq] at h
          subst h
          exact Hex.ZPoly.polyProduct_singleton g
        · split at h
          · rw [Option.some.injEq] at h
            subst h
            exact Hex.ZPoly.polyProduct_singleton g
          · split at h
            · rename_i pieces hladder
              rw [← Array.foldl_toList] at h
              have := fold_pieces_product cap fuel
                (Hex.DensePoly.leadingCoeff g)
                (fun piece seeds pdP out _ hout =>
                  classicalCoreFactorsRecursiveAux_polyProduct cap fuel piece
                    none pdP hout)
                pieces.toList #[] h
              rw [this]
              have hladder_prod :
                  Array.polyProduct (pieces.map (·.1)) = g :=
                Hex.reliftLadder_polyProduct pd cap g _ _ _ _ hladder
              rw [show ((pieces.toList.map (·.1)).toArray :
                  Array Hex.ZPoly) = pieces.map (·.1) by
                apply Array.ext'
                simp]
              rw [hladder_prod]
              show (1 : Hex.ZPoly) * g = g
              exact Hex.ZPoly.one_mul_zpoly g
            · exact Hex.classicalCoreFactorsWithBound_polyProduct _ _ _ h

/-- Sign normalization for the recursion's factors. -/
theorem classicalCoreFactorsRecursiveAux_normalizeFactorSign (cap : Nat) :
    ∀ (fuel : Nat) (g : Hex.ZPoly) (B? : Option Nat)
      (pd : Hex.PrimeChoiceData) {cf : Array Hex.ZPoly},
      Hex.classicalCoreFactorsRecursiveAux cap fuel g B? pd = some cf →
      Hex.ZPoly.Primitive g →
      0 < Hex.DensePoly.leadingCoeff g →
      ∀ f ∈ cf.toList, Hex.normalizeFactorSign f = f
  | 0, g, B?, pd, cf, h, _, _ => by
      simp [Hex.classicalCoreFactorsRecursiveAux] at h
  | fuel + 1, g, B?, pd, cf, h, hprim, hlc => by
      letI := pd.bounds
      have hg_ne : g ≠ 0 := zpoly_ne_zero_of_pos_lc hlc
      simp only [Hex.classicalCoreFactorsRecursiveAux] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · rw [Option.some.injEq] at h
          subst h
          intro f hf
          rw [show (#[g] : Array Hex.ZPoly).toList = [g] from rfl,
            List.mem_singleton] at hf
          subst hf
          exact Hex.normalizeFactorSign_eq_self_of_leadingCoeff_nonneg _
            (by omega)
        · split at h
          · rw [Option.some.injEq] at h
            subst h
            intro f hf
            rw [show (#[g] : Array Hex.ZPoly).toList = [g] from rfl,
              List.mem_singleton] at hf
            subst hf
            exact Hex.normalizeFactorSign_eq_self_of_leadingCoeff_nonneg _
              (by omega)
          · split at h
            · rename_i pieces hladder
              rw [← Array.foldl_toList] at h
              refine fold_pieces_irreducible cap fuel
                (Hex.DensePoly.leadingCoeff g)
                (fun f => Hex.normalizeFactorSign f = f)
                (fun pc => (0 < Hex.DensePoly.leadingCoeff pc.1 ∧
                  Hex.ZPoly.Primitive pc.1))
                ?_ pieces.toList #[] h (by simp) ?_
              · intro piece seeds pdP out hpdP hout hgoodpc
                exact classicalCoreFactorsRecursiveAux_normalizeFactorSign cap
                  fuel piece none pdP hout hgoodpc.2 hgoodpc.1
              · intro pc hpc
                have hpc_arr : pc ∈ pieces := by
                  rwa [← Array.mem_toList_iff]
                obtain ⟨piece, seeds⟩ := pc
                obtain ⟨⟨h1, h2⟩, -, -⟩ :=
                  reliftLadder_piece_facts pd cap g _ _ hlc hprim hg_ne
                    _ _ hladder hpc_arr
                exact ⟨h1, h2⟩
            · exact Hex.classicalCoreFactorsWithBound_normalizeFactorSign
                _ _ _ hlc h

/-- Positive degree for the recursion's factors. -/
theorem classicalCoreFactorsRecursiveAux_degree_pos (cap : Nat) :
    ∀ (fuel : Nat) (g : Hex.ZPoly) (B? : Option Nat)
      (pd : Hex.PrimeChoiceData) {cf : Array Hex.ZPoly},
      Hex.classicalCoreFactorsRecursiveAux cap fuel g B? pd = some cf →
      Hex.ZPoly.Primitive g →
      0 < Hex.DensePoly.leadingCoeff g →
      ∀ f ∈ cf.toList, 0 < f.degree?.getD 0
  | 0, g, B?, pd, cf, h, _, _ => by
      simp [Hex.classicalCoreFactorsRecursiveAux] at h
  | fuel + 1, g, B?, pd, cf, h, hprim, hlc => by
      letI := pd.bounds
      have hg_ne : g ≠ 0 := zpoly_ne_zero_of_pos_lc hlc
      simp only [Hex.classicalCoreFactorsRecursiveAux] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hdeg0
        split at h
        · rw [Option.some.injEq] at h
          subst h
          intro f hf
          rw [show (#[g] : Array Hex.ZPoly).toList = [g] from rfl,
            List.mem_singleton] at hf
          subst hf
          omega
        · split at h
          · rw [Option.some.injEq] at h
            subst h
            intro f hf
            rw [show (#[g] : Array Hex.ZPoly).toList = [g] from rfl,
              List.mem_singleton] at hf
            subst hf
            omega
          · split at h
            · rename_i pieces hladder
              rw [← Array.foldl_toList] at h
              refine fold_pieces_irreducible cap fuel
                (Hex.DensePoly.leadingCoeff g)
                (fun f => 0 < f.degree?.getD 0)
                (fun pc => (0 < Hex.DensePoly.leadingCoeff pc.1 ∧
                  Hex.ZPoly.Primitive pc.1))
                ?_ pieces.toList #[] h (by simp) ?_
              · intro piece seeds pdP out hpdP hout hgoodpc
                exact classicalCoreFactorsRecursiveAux_degree_pos cap
                  fuel piece none pdP hout hgoodpc.2 hgoodpc.1
              · intro pc hpc
                have hpc_arr : pc ∈ pieces := by
                  rwa [← Array.mem_toList_iff]
                obtain ⟨piece, seeds⟩ := pc
                obtain ⟨⟨h1, h2⟩, -, -⟩ :=
                  reliftLadder_piece_facts pd cap g _ _ hlc hprim hg_ne
                    _ _ hladder hpc_arr
                exact ⟨h1, h2⟩
            · rename_i hdeg1 hsize hladder
              exact Hex.classicalCoreFactorsWithBound_degree_pos _ _ _
                (by omega) h

/-- Entry-point structural companions. -/
theorem classicalCoreFactorsRecursive_polyProduct
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {cf : Array Hex.ZPoly}
    (h : Hex.classicalCoreFactorsRecursive core B primeData = some cf) :
    Array.polyProduct cf = core := by
  unfold Hex.classicalCoreFactorsRecursive at h
  split at h
  · rw [Option.some.injEq] at h
    subst h
    exact Hex.ZPoly.polyProduct_singleton core
  · exact classicalCoreFactorsRecursiveAux_polyProduct _ _ _ _ _ h

theorem classicalCoreFactorsRecursive_normalizeFactorSign
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_prim : Hex.ZPoly.Primitive core)
    {cf : Array Hex.ZPoly}
    (h : Hex.classicalCoreFactorsRecursive core B primeData = some cf) :
    ∀ f ∈ cf.toList, Hex.normalizeFactorSign f = f := by
  unfold Hex.classicalCoreFactorsRecursive at h
  split at h
  · rw [Option.some.injEq] at h
    subst h
    intro f hf
    rw [show (#[core] : Array Hex.ZPoly).toList = [core] from rfl,
      List.mem_singleton] at hf
    subst hf
    exact Hex.normalizeFactorSign_eq_self_of_leadingCoeff_nonneg _ (by omega)
  · exact classicalCoreFactorsRecursiveAux_normalizeFactorSign _ _ _ _ _ h
      hcore_prim hcore_pos

theorem classicalCoreFactorsRecursive_degree_pos
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_deg : 0 < core.degree?.getD 0)
    (hcore_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_prim : Hex.ZPoly.Primitive core)
    {cf : Array Hex.ZPoly}
    (h : Hex.classicalCoreFactorsRecursive core B primeData = some cf) :
    ∀ f ∈ cf.toList, 0 < f.degree?.getD 0 := by
  unfold Hex.classicalCoreFactorsRecursive at h
  split at h
  · rw [Option.some.injEq] at h
    subst h
    intro f hf
    rw [show (#[core] : Array Hex.ZPoly).toList = [core] from rfl,
      List.mem_singleton] at hf
    subst hf
    exact hcore_deg
  · exact classicalCoreFactorsRecursiveAux_degree_pos _ _ _ _ _ h
      hcore_prim hcore_pos

/-- **Recursive residual-arm irreducibility (public-bound form).** Mirror of
`classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible` for the
recursive tier: the bound is handled at `defaultFactorCoeffBound f` via
divisor validity, so no Mignotte monotonicity is needed. -/
theorem classicalCoreFactorsRecursive_squareFreeCore_factor_zpolyIrreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {cf : Array Hex.ZPoly}
    (hclassical : Hex.classicalCoreFactorsRecursive
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f) primeData = some cf) :
    ∀ g ∈ cf.toList, Hex.ZPoly.Irreducible g := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_primitive : Hex.ZPoly.Primitive core :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core) :=
    IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf_ne
  have hcore_pos : 0 < core.degree?.getD 0 := Nat.pos_of_ne_zero hdeg_ne
  have hp2 : 2 ≤ primeData.p :=
    (Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected).two_le
  have hcore_dvd_f : core ∣ f := Hex.squareFreeCore_dvd_self f hf_ne
  have hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤
      Hex.ZPoly.defaultFactorCoeffBound f := by
    have hsize_pos : 0 < core.size := Hex.ZPoly.size_pos_of_ne_zero core hcore_ne
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last _ hsize_pos]
    exact defaultFactorCoeffBound_valid f hf_ne core hcore_dvd_f (core.size - 1)
  have hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i,
      (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound f := by
    intro g hg i
    exact defaultFactorCoeffBound_valid f hf_ne g (zpoly_dvd_trans hg hcore_dvd_f) i
  have hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound f <
      primeData.p ^
        Hex.precisionForCoeffBound
          (Hex.ZPoly.exhaustiveLiftBound core (Hex.ZPoly.defaultFactorCoeffBound f))
          primeData.p :=
    IntReductionMod.exhaustiveLiftBound_precision core
      (Hex.ZPoly.defaultFactorCoeffBound f) primeData.p hp2
  have hB_ne : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0 :=
    (Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hf_ne).ne'
  have hirr := classicalCoreFactorsRecursive_factor_irreducible_of_validBound core
    (Hex.ZPoly.defaultFactorCoeffBound f) primeData hclassical
    (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos)
    hcore_primitive hcore_lc_pos hcore_sqfree hB_ne
    (Hex.ZPoly.defaultFactorCoeffBound f) hcore_lc_le hvalid hprecision
  intro g hg
  exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible g).mpr (hirr g hg)

/-- **Recursive residual-arm reassembly discharger.** Mirror of
`reassemblyExpansionComplete_classicalCore_of_ne_zero` for the recursive
tier, via the recursion's structural companions. -/
theorem reassemblyExpansionComplete_classicalRecursive_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {cf : Array Hex.ZPoly}
    (hclassical : Hex.classicalCoreFactorsRecursive
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f) primeData = some cf) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) cf := by
  classical
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  have hcore_deg : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
    Nat.pos_of_ne_zero hdeg_ne
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm
    f hf cf
    (classicalCoreFactorsRecursive_squareFreeCore_factor_zpolyIrreducible
      f hf primeData hselected hdeg_ne hclassical)
    (classicalCoreFactorsRecursive_polyProduct _ _ _ hclassical)
    (classicalCoreFactorsRecursive_normalizeFactorSign _ _ _ hcore_pos
      hcore_prim hclassical)
    (classicalCoreFactorsRecursive_degree_pos _ _ _ hcore_deg hcore_pos
      hcore_prim hclassical)

/-- **Classical-branch raw-factor irreducibility.**

Every raw factor of the classical tier's output `factorClassicalFactorsWithBound
f (defaultFactorCoeffBound f)` that passes the recorded-factor filter is
irreducible.  Case-split over the branch: deg-0 constant short-circuit, quadratic
integer-root short-circuit, and the size-ordered recombination residual.

The residual arm composes the recursive-tier irreducibility
`classicalCoreFactorsRecursive_squareFreeCore_factor_zpolyIrreducible` with
the reassembly-completeness discharger
`reassemblyExpansionComplete_classicalRecursive_of_ne_zero` through the lift
`reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`.
The bound is handled at `defaultFactorCoeffBound f` directly (validity from
`core ∣ f`, precision from `exhaustiveLiftBound_precision`), so no
`defaultFactorCoeffBound core ≤ defaultFactorCoeffBound f` monotonicity is needed. -/
theorem factorClassicalFactorsWithBound_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {cf : Array Hex.ZPoly}
    (hcf : Hex.factorClassicalFactorsWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f) = some cf)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ cf.toList)
    (hrec : Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  simp only [Hex.factorClassicalFactorsWithBound] at hcf
  by_cases hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdeg] at hcf
    obtain rfl := Option.some.inj hcf
    have hcomplete := Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdeg
    rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
        _ _ raw hcomplete hmem with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core : raw = (Hex.normalizeForFactor f).squareFreeCore := by
          simpa using hcore
        rw [hraw_core, Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg]
      rw [hraw_one, Hex.normalizeFactorSign_one, Hex.shouldRecordPolynomialFactor_one] at hrec
      exact absurd hrec (by decide)
  · rw [if_neg hdeg] at hcf
    cases hquad :
        Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        simp only [hquad] at hcf
        obtain rfl := Option.some.inj hcf
        refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          _ _ ?_ ?_ hmem
        · exact IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
            f hf hquad
        · intro factor hfmem
          exact Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
            hcore_pos hcore_prim hquad hfmem
    | none =>
        simp only [hquad] at hcf
        cases hsel :
            Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore with
        | none => simp [hsel] at hcf
        | some primeData =>
            simp only [hsel, Option.bind_some] at hcf
            cases hcore :
                Hex.classicalCoreFactorsRecursive (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound f) primeData with
            | none => simp [hcore] at hcf
            | some coreFactors =>
                simp only [hcore, Option.map_some] at hcf
                obtain rfl := Option.some.inj hcf
                -- Residual arm: the size-ordered classical recombination core.
                -- Per-factor irreducibility from #8510, reassembly completeness
                -- from #8511.
                exact
                  Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
                    _ _
                    (reassemblyExpansionComplete_classicalRecursive_of_ne_zero
                      f hf primeData hsel hdeg hcore)
                    (classicalCoreFactorsRecursive_squareFreeCore_factor_zpolyIrreducible
                      f hf primeData hsel hdeg hcore)
                    hmem


end HexBerlekampZassenhausMathlib
