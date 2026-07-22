/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.WordCld
public import HexBerlekampZassenhaus.Lattice
public import HexModArithMathlib.WordMod
public import HexPolyMathlib.Basic
public import Mathlib.Algebra.Polynomial.Div

public section

/-!
Byte-identical correspondence for the word-sized CLD kernel (issue #8691,
Phase 2): `cldQuotientModWord? f g p a = some (cldQuotientModBignum f g p a)` for a
monic `g` whenever the guard `Odd (p^a) ∧ p^a < 2^64` holds.

The proof transports both quotients' Euclidean reconstructions
(`q · g + r = numerator`, `deg r < deg g`, `g` monic) into `ZMod (p^a)[X]` and
concludes by monic-division uniqueness (`Polynomial.div_modByMonic_unique`).
-/

namespace HexBerlekampZassenhausMathlib

open Hex Polynomial

/-- Coefficient cast of an executable integer polynomial into `ZMod m.toNat[X]`. -/
noncomputable def cZ (m : UInt64) (f : Hex.ZPoly) : Polynomial (ZMod m.toNat) :=
  Polynomial.map (Int.castRingHom (ZMod m.toNat)) (HexPolyMathlib.toPolynomial f)

/-- Coefficient cast of an executable `WordMod` polynomial into `ZMod m.toNat[X]`. -/
noncomputable def cW {m : UInt64} (ctx : _root_.MontCtx m)
    (a : Hex.DensePoly (Hex.WordMod ctx)) : Polynomial (ZMod m.toNat) :=
  Polynomial.map (HexModArithMathlib.WordMod.toZModRingHom (ctx := ctx))
    (HexPolyMathlib.toPolynomial a)

@[simp] theorem cZ_coeff (m : UInt64) (f : Hex.ZPoly) (j : Nat) :
    (cZ m f).coeff j = ((f.coeff j : Int) : ZMod m.toNat) := by
  rw [cZ, Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial]; simp

@[simp] theorem cW_coeff {m : UInt64} (ctx : _root_.MontCtx m)
    (a : Hex.DensePoly (Hex.WordMod ctx)) (j : Nat) :
    (cW ctx a).coeff j = HexModArithMathlib.WordMod.toZMod (a.coeff j) := by
  rw [cW, Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    HexModArithMathlib.WordMod.toZModRingHom_apply]

theorem cZ_mul (m : UInt64) (f g : Hex.ZPoly) : cZ m (f * g) = cZ m f * cZ m g := by
  rw [cZ, cZ, cZ, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]

theorem cZ_add (m : UInt64) (f g : Hex.ZPoly) : cZ m (f + g) = cZ m f + cZ m g := by
  rw [cZ, cZ, cZ, HexPolyMathlib.toPolynomial_add, Polynomial.map_add]

theorem cW_mul {m : UInt64} (ctx : _root_.MontCtx m)
    (a b : Hex.DensePoly (Hex.WordMod ctx)) : cW ctx (a * b) = cW ctx a * cW ctx b := by
  rw [cW, cW, cW, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul]

theorem cW_add {m : UInt64} (ctx : _root_.MontCtx m)
    (a b : Hex.DensePoly (Hex.WordMod ctx)) : cW ctx (a + b) = cW ctx a + cW ctx b := by
  rw [cW, cW, cW, HexPolyMathlib.toPolynomial_add, Polynomial.map_add]

/-- Canonical-representative uniqueness: two integer polynomials with all
coefficients in `[0, m)` that are congruent mod `m` coefficientwise are equal. -/
theorem eq_of_cZ_eq {m : UInt64}
    (x y : Hex.ZPoly)
    (hx : ∀ i, 0 ≤ x.coeff i ∧ x.coeff i < (m.toNat : Int))
    (hy : ∀ i, 0 ≤ y.coeff i ∧ y.coeff i < (m.toNat : Int))
    (h : cZ m x = cZ m y) : x = y := by
  apply Hex.DensePoly.ext_coeff
  intro i
  have hi : ((x.coeff i : Int) : ZMod m.toNat) = ((y.coeff i : Int) : ZMod m.toNat) := by
    have := congrArg (fun q => Polynomial.coeff q i) h
    simpa [cZ_coeff] using this
  have hcong : x.coeff i ≡ y.coeff i [ZMOD (m.toNat : Int)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp hi
  have hc : x.coeff i % (m.toNat : Int) = y.coeff i % (m.toNat : Int) := hcong
  rwa [Int.emod_eq_of_lt (hx i).1 (hx i).2, Int.emod_eq_of_lt (hy i).1 (hy i).2] at hc

open HexPolyMathlib in
/-- Monic division commutes with a coefficient ring hom, in the target `T[X]`:
the mapped executable quotient is the Mathlib monic-division quotient of the
mapped inputs. Uniqueness (`div_modByMonic_unique`) does the work; the caller
supplies the transported monic/degree facts. -/
theorem map_divMod_monic {S : Type*} [CommRing S] [DecidableEq S] [Div S]
    {T : Type*} [CommRing T] (φ : S →+* T)
    (num g : Hex.DensePoly S)
    (hcancel : ∀ a : S, a - a / g.leadingCoeff * g.leadingCoeff = (0 : S))
    (hgmonic : (Polynomial.map φ (toPolynomial g)).Monic)
    (hdegmap : (Polynomial.map φ (toPolynomial g)).degree = (toPolynomial g).degree)
    (hdeg : (toPolynomial (Hex.DensePoly.divMod num g).2).degree < (toPolynomial g).degree) :
    Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).1)
      = Polynomial.map φ (toPolynomial num) /ₘ Polynomial.map φ (toPolynomial g) := by
  have hrec : (Hex.DensePoly.divMod num g).1 * g + (Hex.DensePoly.divMod num g).2 = num :=
    Hex.DensePoly.divMod_reconstruction num g hcancel
  have hrec2 :
      Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).1)
          * Polynomial.map φ (toPolynomial g)
        + Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).2)
        = Polynomial.map φ (toPolynomial num) := by
    have h := congrArg (Polynomial.map φ) (congrArg toPolynomial hrec)
    simp only [toPolynomial_add, toPolynomial_mul, Polynomial.map_add, Polynomial.map_mul] at h
    exact h
  have hrec3 :
      Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).2)
        + Polynomial.map φ (toPolynomial g)
            * Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).1)
        = Polynomial.map φ (toPolynomial num) := by
    rw [mul_comm, add_comm]; exact hrec2
  have hrdeg :
      (Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).2)).degree
        < (Polynomial.map φ (toPolynomial g)).degree := by
    calc (Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).2)).degree
        ≤ (toPolynomial (Hex.DensePoly.divMod num g).2).degree := Polynomial.degree_map_le
      _ < (toPolynomial g).degree := hdeg
      _ = (Polynomial.map φ (toPolynomial g)).degree := hdegmap.symm
  have huniq := Polynomial.div_modByMonic_unique
    (Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).1))
    (Polynomial.map φ (toPolynomial (Hex.DensePoly.divMod num g).2))
    hgmonic ⟨hrec3, hrdeg⟩
  exact huniq.1.symm

/-! ### Coefficient bridges -/

theorem intCast_intModNat (c : Int) (M : Nat) (hM : 0 < M) :
    ((ZPoly.intModNat c M : Nat) : ZMod M) = (c : ZMod M) := by
  have hM0 : (M : Int) ≠ 0 := by exact_mod_cast hM.ne'
  have hnn : 0 ≤ c % (M : Int) := Int.emod_nonneg c hM0
  have h1 : ((ZPoly.intModNat c M : Nat) : Int) = c % (M : Int) := by
    rw [ZPoly.intModNat]
    simp [Int.toNat_of_nonneg hnn]
  calc ((ZPoly.intModNat c M : Nat) : ZMod M)
      = (((ZPoly.intModNat c M : Nat) : Int) : ZMod M) := by rw [Int.cast_natCast]
    _ = ((c % (M : Int) : Int) : ZMod M) := by rw [h1]
    _ = (c : ZMod M) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).mpr (Int.emod_emod_of_dvd c (dvd_refl _))

/-- The word-mapped executable image `toW = ofNat ∘ intModNat`. -/
def toWMap {m : UInt64} (ctx : _root_.MontCtx m) (x : Hex.ZPoly) :
    Hex.DensePoly (Hex.WordMod ctx) :=
  Hex.DensePoly.ofCoeffs (x.toArray.map (fun c => Hex.WordMod.ofNat (ZPoly.intModNat c m.toNat)))

theorem coeff_toWMap {m : UInt64} (ctx : _root_.MontCtx m) (x : Hex.ZPoly) (j : Nat) :
    (toWMap ctx x).coeff j = Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat (x.coeff j) m.toNat) := by
  have htoW0 : Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat 0 m.toNat) = 0 := by
    have : ZPoly.intModNat 0 m.toNat = 0 := by simp [ZPoly.intModNat]
    rw [this]; rfl
  rw [toWMap, Hex.DensePoly.coeff_ofCoeffs]
  show (x.toArray.map (fun c => Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat c m.toNat))).getD j 0
    = Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat (x.coeff j) m.toNat)
  rw [show x.coeff j = x.toArray.getD j 0 from rfl]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases x.toArray[j]? with
  | none => simpa using htoW0.symm
  | some v => simp

/-- `cW` of the `toW`-mapped image of an integer polynomial equals `cZ` of the
original. -/
theorem cW_toWMap_eq_cZ {m : UInt64} (ctx : _root_.MontCtx m) (x : Hex.ZPoly) :
    cW ctx (toWMap ctx x) = cZ m x := by
  apply Polynomial.ext
  intro j
  rw [cW_coeff, cZ_coeff, coeff_toWMap,
    show HexModArithMathlib.WordMod.toZMod
        (Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat (x.coeff j) m.toNat))
      = ((ZPoly.intModNat (x.coeff j) m.toNat : Nat) : ZMod m.toNat) from
    HexModArithMathlib.WordMod.toZMod_natCast _]
  exact intCast_intModNat (x.coeff j) m.toNat ctx.p_pos

/-- Reduction mod `p^a` vanishes under the `ZMod (p^a)` cast. -/
theorem cZ_reduceModPow {m : UInt64} {p a : Nat} (hpos : 0 < m.toNat) (hm : m.toNat = p ^ a)
    (x : Hex.ZPoly) : cZ m (ZPoly.reduceModPow x p a) = cZ m x := by
  apply Polynomial.ext
  intro j
  rw [cZ_coeff, cZ_coeff, ZPoly.coeff_reduceModPow, Int.ofNat_eq_natCast, Int.cast_natCast, ← hm]
  exact intCast_intModNat (x.coeff j) m.toNat hpos

/-- The `ZMod` cast commutes with the executable derivative. -/
theorem cZ_derivative (m : UInt64) (x : Hex.ZPoly) :
    cZ m (Hex.DensePoly.derivative x) = Polynomial.derivative (cZ m x) := by
  simp only [cZ, HexPolyMathlib.toPolynomial_derivative, Polynomial.derivative_map]

theorem cW_derivative {m : UInt64} (ctx : _root_.MontCtx m)
    (a : Hex.DensePoly (Hex.WordMod ctx)) :
    cW ctx (Hex.DensePoly.derivative a) = Polynomial.derivative (cW ctx a) := by
  simp only [cW, HexPolyMathlib.toPolynomial_derivative, Polynomial.derivative_map]

/-! ### Guard correctness -/

theorem powLtWord?_go_eq (p : Nat) : ∀ (n acc r : Nat),
    Hex.powLtWordAux p n acc = some r → r = acc * p ^ n := by
  intro n
  induction n with
  | zero =>
      intro acc r h
      simp only [Hex.powLtWordAux, Option.some.injEq] at h
      subst h; simp
  | succ k ih =>
      intro acc r h
      simp only [Hex.powLtWordAux] at h
      by_cases hlt : acc * p < UInt64.word
      · rw [if_pos hlt] at h
        have := ih (acc * p) r h
        rw [this]; ring
      · rw [if_neg hlt] at h; exact absurd h (by simp)

theorem powLtWord?_go_lt (p : Nat) : ∀ (n acc r : Nat),
    acc < UInt64.word → Hex.powLtWordAux p n acc = some r → r < UInt64.word := by
  intro n
  induction n with
  | zero =>
      intro acc r hacc h
      simp only [Hex.powLtWordAux, Option.some.injEq] at h
      omega
  | succ k ih =>
      intro acc r _ h
      simp only [Hex.powLtWordAux] at h
      by_cases hlt : acc * p < UInt64.word
      · rw [if_pos hlt] at h; exact ih (acc * p) r hlt h
      · rw [if_neg hlt] at h; exact absurd h (by simp)

theorem powLtWord?_eq {p a mval : Nat} (h : Hex.powLtWord? p a = some mval) :
    mval = p ^ a ∧ mval < UInt64.word := by
  have hgo : Hex.powLtWordAux p a 1 = some mval := h
  refine ⟨?_, powLtWord?_go_lt p a 1 mval (by simp [UInt64.word]) hgo⟩
  have := powLtWord?_go_eq p a 1 mval hgo
  simpa using this

/-! ### Degree transport -/

open HexPolyMathlib in
theorem toPoly_degree_lt {S : Type*} [CommRing S] [DecidableEq S] {r g : Hex.DensePoly S}
    (hg0 : toPolynomial g ≠ 0)
    (hlt : r.degree?.getD 0 < g.degree?.getD 0) :
    (toPolynomial r).degree < (toPolynomial g).degree := by
  by_cases hr : toPolynomial r = 0
  · rw [hr, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (fun hb => hg0 (Polynomial.degree_eq_bot.mp hb))
  · rw [Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree hg0,
      natDegree_toPolynomial, natDegree_toPolynomial]
    exact_mod_cast hlt

theorem intModNat_lt (y : Int) (M : Nat) (hM : 0 < M) : ZPoly.intModNat y M < M := by
  have hM0 : (M : Int) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 : y % (M : Int) < M := Int.emod_lt_of_pos y (by exact_mod_cast hM)
  have h2 : 0 ≤ y % (M : Int) := Int.emod_nonneg y hM0
  rw [ZPoly.intModNat, Int.ofNat_eq_natCast]; omega

/-! ### Main equality -/

open HexPolyMathlib in
theorem cldQuotientModWord?_eq (f g : Hex.ZPoly) (p a : Nat)
    (hg : Hex.DensePoly.Monic g) (hgdeg : 0 < g.degree?.getD 0)
    {mval : Nat} (hpow : Hex.powLtWord? p a = some mval)
    (hodd : (UInt64.ofNat mval) % 2 = 1) (hm1 : 1 < mval) :
    Hex.cldQuotientModWord? f g p a = some (cldQuotientModBignum f g p a) := by
  obtain ⟨hmeq, hmlt⟩ := powLtWord?_eq hpow
  have hmtoNat : (UInt64.ofNat mval).toNat = mval := by
    rw [UInt64.toNat_ofNat_mod_word]; exact Nat.mod_eq_of_lt hmlt
  rw [Hex.cldQuotientModWord?, hpow]
  simp only [dif_pos hodd]
  set ctx := _root_.MontCtx.mk (UInt64.ofNat mval) hodd with hctx
  -- the kernel's fW, gW are `toWMap ctx f`, `toWMap ctx g`
  have hgW : Hex.DensePoly.ofCoeffs
      (g.toArray.map (fun c => Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat c mval)))
      = toWMap ctx g := by rw [toWMap]; simp only [hmtoNat]
  have hfW : Hex.DensePoly.ofCoeffs
      (f.toArray.map (fun c => Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat c mval)))
      = toWMap ctx f := by rw [toWMap]; simp only [hmtoNat]
  rw [hfW, hgW]
  set qW := (Hex.DensePoly.divMod (toWMap ctx f * Hex.DensePoly.derivative (toWMap ctx g))
    (toWMap ctx g)).1 with hqW
  refine congrArg some ?_
  refine eq_of_cZ_eq (m := UInt64.ofNat mval) _ _ ?_ ?_ ?_
  · -- word output: coeffs in [0, mval)
    intro i
    have hc : (Hex.DensePoly.ofCoeffs (qW.toArray.map (fun w => Int.ofNat w.toNat))).coeff i
        = Int.ofNat (qW.coeff i).toNat := by
      rw [Hex.DensePoly.coeff_ofCoeffs]
      show (qW.toArray.map (fun w => Int.ofNat w.toNat)).getD i 0 = Int.ofNat (qW.coeff i).toNat
      rw [show qW.coeff i = qW.toArray.getD i 0 from rfl]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases qW.toArray[i]? with
      | none => simp [Hex.WordMod.toNat_zero]
      | some w => simp
    rw [hc, hmtoNat, Int.ofNat_eq_natCast]
    have hlt : (qW.coeff i).toNat < mval := by
      have := (qW.coeff i).toNat_lt; rwa [hmtoNat] at this
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hlt⟩
  · -- cldQuotientModBignum: coeffs in [0, mval)
    intro i
    unfold cldQuotientModBignum
    rw [ZPoly.coeff_reduceModPow, hmtoNat, hmeq, Int.ofNat_eq_natCast]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast intModNat_lt _ (p ^ a) (by omega)⟩
  · -- the cast equality: both quotients are `numerator /ₘ divisor` in `ZMod (p^a)[X]`
    haveI : Fact (1 < (UInt64.ofNat mval).toNat) := ⟨by rw [hmtoNat]; exact hm1⟩
    have hmpa : (UInt64.ofNat mval).toNat = p ^ a := by rw [hmtoNat]; exact hmeq
    have hpapos : 0 < (UInt64.ofNat mval).toNat := by rw [hmtoNat]; omega
    -- `g` is monic in the various images
    have htgm : (toPolynomial g).Monic := by
      have : (toPolynomial g).leadingCoeff = 1 := by
        rw [leadingCoeff_toPolynomial]; exact hg
      exact this
    have hcZgm : (cZ (UInt64.ofNat mval) g).Monic := by rw [cZ]; exact htgm.map _
    have htgne : (toPolynomial g) ≠ 0 := htgm.ne_zero
    -- gW monic / positive degree (the toW-mapped divisor)
    have hgsize2 : 1 < g.size := by
      unfold Hex.DensePoly.degree? at hgdeg
      by_cases hs : g.size = 0
      · rw [dif_pos hs] at hgdeg; simp at hgdeg
      · rw [dif_neg hs] at hgdeg; simp only [Option.getD_some] at hgdeg; omega
    have hgpos : 0 < g.size := by omega
    have hgleading : g.coeff (g.size - 1) = 1 := by
      rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hgpos]; exact hg
    have hi1 : ZPoly.intModNat 1 (UInt64.ofNat mval).toNat = 1 := by
      rw [hmtoNat, ZPoly.intModNat, Int.ofNat_eq_natCast,
        Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hm1)]; rfl
    have htoW1 : Hex.WordMod.ofNat (ctx := ctx) (ZPoly.intModNat 1 (UInt64.ofNat mval).toNat) = 1 := by
      rw [hi1]; rfl
    have h10 : (1 : Hex.WordMod ctx) ≠ 0 := by
      intro h
      have := congrArg HexModArithMathlib.WordMod.toZMod h
      rw [HexModArithMathlib.WordMod.toZMod_one, HexModArithMathlib.WordMod.toZMod_zero] at this
      exact one_ne_zero this
    have hsz : (toWMap ctx g).size = g.size := by
      refine le_antisymm ?_ ?_
      · rw [toWMap]
        calc (Hex.DensePoly.ofCoeffs _).size ≤ (g.toArray.map _).size := Hex.DensePoly.size_ofCoeffs_le _
          _ = g.size := by rw [Array.size_map, Hex.DensePoly.toArray_size]
      · by_contra h
        have hcz : (toWMap ctx g).coeff (g.size - 1) = 0 :=
          Hex.DensePoly.coeff_eq_zero_of_size_le _ (by omega)
        rw [coeff_toWMap, hgleading, htoW1] at hcz
        exact h10 hcz
    have hgWm : Hex.DensePoly.Monic (toWMap ctx g) := by
      show (toWMap ctx g).leadingCoeff = 1
      rw [Hex.DensePoly.leadingCoeff_eq_coeff_last _ (by rw [hsz]; exact hgpos), hsz,
        coeff_toWMap, hgleading, htoW1]
    have hgWd : 0 < (toWMap ctx g).degree?.getD 0 := by
      unfold Hex.DensePoly.degree?
      rw [dif_neg (by rw [hsz]; omega)]
      simp only [Option.getD_some]; rw [hsz]; omega
    -- shared cancellation shape
    have hcancelZ : ∀ c : Int, c - c / g.leadingCoeff * g.leadingCoeff = 0 := by
      intro c; rw [Hex.DensePoly.leadingCoeff_eq_one_of_monic hg]; simp
    have hcancelW : ∀ c : Hex.WordMod ctx,
        c - c / (toWMap ctx g).leadingCoeff * (toWMap ctx g).leadingCoeff = 0 := by
      intro c; rw [Hex.DensePoly.leadingCoeff_eq_one_of_monic hgWm]; simp
    -- Int-side monic division in the image
    have hCM : cZ (UInt64.ofNat mval) (cldQuotientModBignum f g p a)
        = cZ (UInt64.ofNat mval) (ZPoly.reduceModPow (f * Hex.DensePoly.derivative g) p a)
            /ₘ cZ (UInt64.ofNat mval) g := by
      unfold cldQuotientModBignum
      rw [cZ_reduceModPow hpapos hmpa]
      exact map_divMod_monic (Int.castRingHom (ZMod (UInt64.ofNat mval).toNat)) _ g hcancelZ
        (by rw [cZ] at hcZgm; exact hcZgm)
        (by rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero]
            rw [leadingCoeff_toPolynomial, Hex.DensePoly.leadingCoeff_eq_one_of_monic hg]; simp)
        (toPoly_degree_lt htgne
          (Hex.DensePoly.divMod_remainder_degree_lt_of_pos_degree_core _ g hgdeg hcancelZ))
    -- word-side monic division in the image
    have htgWm : (toPolynomial (toWMap ctx g)).Monic := by
      have : (toPolynomial (toWMap ctx g)).leadingCoeff = 1 := by
        rw [leadingCoeff_toPolynomial]; exact hgWm
      exact this
    have htgWne : toPolynomial (toWMap ctx g) ≠ 0 := by
      intro h
      have hnd := natDegree_toPolynomial (toWMap ctx g)
      rw [h, Polynomial.natDegree_zero] at hnd
      omega
    have hqWeq : cW ctx qW
        = cW ctx (toWMap ctx f * Hex.DensePoly.derivative (toWMap ctx g))
            /ₘ cW ctx (toWMap ctx g) := by
      rw [hqW]
      exact map_divMod_monic (HexModArithMathlib.WordMod.toZModRingHom (ctx := ctx)) _ (toWMap ctx g)
        hcancelW
        (htgWm.map _)
        (Polynomial.degree_map_eq_of_leadingCoeff_ne_zero _
          (by rw [leadingCoeff_toPolynomial, Hex.DensePoly.leadingCoeff_eq_one_of_monic hgWm]; simp))
        (toPoly_degree_lt htgWne
          (Hex.DensePoly.divMod_remainder_degree_lt_of_pos_degree_core _ (toWMap ctx g) hgWd hcancelW))
    -- numerator / divisor agreement, then chain
    have hgdiv : cW ctx (toWMap ctx g) = cZ (UInt64.ofNat mval) g := cW_toWMap_eq_cZ ctx g
    have hnum : cW ctx (toWMap ctx f * Hex.DensePoly.derivative (toWMap ctx g))
        = cZ (UInt64.ofNat mval) (ZPoly.reduceModPow (f * Hex.DensePoly.derivative g) p a) := by
      rw [cZ_reduceModPow hpapos hmpa, cW_mul, cW_derivative, cW_toWMap_eq_cZ, cW_toWMap_eq_cZ,
        cZ_mul, cZ_derivative]
    have hWO : cZ (UInt64.ofNat mval)
        (Hex.DensePoly.ofCoeffs (qW.toArray.map (fun w => Int.ofNat w.toNat))) = cW ctx qW := by
      apply Polynomial.ext; intro i
      rw [cZ_coeff, cW_coeff]
      have hc : (Hex.DensePoly.ofCoeffs (qW.toArray.map (fun w => Int.ofNat w.toNat))).coeff i
          = Int.ofNat (qW.coeff i).toNat := by
        rw [Hex.DensePoly.coeff_ofCoeffs]
        show (qW.toArray.map (fun w => Int.ofNat w.toNat)).getD i 0 = Int.ofNat (qW.coeff i).toNat
        rw [show qW.coeff i = qW.toArray.getD i 0 from rfl]
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
        cases qW.toArray[i]? with
        | none => simp [Hex.WordMod.toNat_zero]
        | some w => simp
      rw [hc, Int.ofNat_eq_natCast, Int.cast_natCast]
      rfl
    rw [hWO, hqWeq, hnum, hgdiv, hCM]

/-- The word-sized dispatch in `cldQuotientMod` agrees with the bignum reference
`cldQuotientModBignum` for every input: the guard exactly matches the hypotheses
of `cldQuotientModWord?_eq`, so on the fast path the word quotient is byte-identical
and `Option.getD` returns it; off the fast path the bignum branch is taken. -/
theorem cldQuotientMod_eq_spec (f g : Hex.ZPoly) (p a : Nat) :
    Hex.cldQuotientMod f g p a = Hex.cldQuotientModBignum f g p a := by
  unfold Hex.cldQuotientMod
  split
  · rename_i m hpow
    split_ifs with h
    · obtain ⟨hodd, hm1, hlead, hdeg⟩ := h
      rw [cldQuotientModWord?_eq f g p a hlead hdeg hpow hodd hm1, Option.getD_some]
    · rfl
  · rfl

end HexBerlekampZassenhausMathlib
