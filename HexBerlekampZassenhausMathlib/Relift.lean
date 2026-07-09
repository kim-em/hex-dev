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

end HexBerlekampZassenhausMathlib
