/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.WordCld
public import HexModArithMathlib.WordMod
public import HexPolyMathlib.Basic
public import Mathlib.Algebra.Polynomial.Div

public section

/-!
Byte-identical correspondence for the word-sized CLD kernel (issue #8691,
Phase 2): `cldQuotientModWord? f g p a = some (cldQuotientMod f g p a)` for a
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

end HexBerlekampZassenhausMathlib
