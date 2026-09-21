/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Map
public import HexSturmMathlib.Rational

public section
namespace HexSturmMathlib.IntCast

open Hex HexRealRootsMathlib
open HexPolyMathlib.Interpret

/-- Embed the literal integer evidence and dyadic endpoints in the rationals.
No polynomial producer or division is called; the context and value are retained. -/
@[expose] def certificate {Ctx : Type u} (cert : TarskiCertificate Int Dyadic Ctx) : TarskiCertificate Rat Rat Ctx :=
  cert.map (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero) Dyadic.toRat

private theorem map_toRatPoly (p : ZPoly) :
    DensePoly.Interpret.map (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero) p = ZPoly.toRatPoly p := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.Interpret.map_coeff, ZPoly.coeff_toRatPoly]

private theorem interpret_map (p : ZPoly) :
    interpret (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero)
      (DensePoly.Interpret.map (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero) p) = toPolyℝ p := by
  rw [← Tarski.interpret_int_real]
  ext i
  simp only [coeff_interpret, DensePoly.Interpret.map_coeff, Rat.cast_intCast]

private theorem sign_int (z : Int) : Sturm.orderSign (z : Rat) = Int.sign z := by
  have hb : -1 ≤ Int.sign z ∧ Int.sign z ≤ 1 := by
    rcases Int.sign_trichotomy z with h | h | h <;> omega
  have hq := orderSign_spec (z : Rat)
  have hn : Sturm.orderSign (z : Rat) < 0 ↔ Int.sign z < 0 := by
    rw [hq.2.1, Int.cast_lt_zero, Int.sign_neg_iff]
  have hz : Sturm.orderSign (z : Rat) = 0 ↔ Int.sign z = 0 := by
    rw [hq.2.2.1, Int.cast_eq_zero, Int.sign_eq_zero_iff_zero]
  omega

private theorem sign_dyadic (q : Rat) (d : Dyadic) (h : (q : ℝ) = HexRealRootsMathlib.Dyadic.toReal d) :
    Sturm.orderSign q = dyadicSign d := by
  have hq := orderSign_spec q
  have hd : -1 ≤ dyadicSign d ∧ dyadicSign d ≤ 1 := by
    cases d with
    | zero => simp [dyadicSign]
    | ofOdd n k hn => simp only [dyadicSign]; split <;> omega
  have hn : Sturm.orderSign q < 0 ↔ dyadicSign d < 0 := by
    rw [hq.2.1, Tarski.dyadicSign_neg, ← h, Rat.cast_lt_zero]
  have hz : Sturm.orderSign q = 0 ↔ dyadicSign d = 0 := by
    rw [hq.2.2.1, ← Rat.cast_eq_zero (α := ℝ), h,
      ← sign_eq_zero_iff, ← sign_dyadicSign, sign_eq_zero_iff, Int.cast_eq_zero]
  omega

private theorem compare_eq (a b : Dyadic) :
    (EndpointSigns.ofSign Sturm.orderSign).compare a.toRat b.toRat = EndpointSigns.intDyadic.compare a b := by
  apply sign_dyadic
  rw [toReal_eq_cast_toRat, Dyadic.toRat_sub]

private theorem evalSign_eq (p : ZPoly) (a : Dyadic) :
    (EndpointSigns.ofSign Sturm.orderSign).evalSign
      (DensePoly.Interpret.map (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero) p) a.toRat =
      EndpointSigns.intDyadic.evalSign p a := by
  apply sign_dyadic
  rw [toReal_evalDyadic, ← interpret_map p, toReal_eq_cast_toRat,
    eval_interpret _ _ Rat.cast_add Rat.cast_mul]

/-- Every accepted integer certificate embeds into an accepted rational
certificate with the same value and literal context. Infinities are retained. -/
theorem certificate_checks {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p g : ZPoly) (a b : Endpoint Dyadic) (value : Int) (cert : TarskiCertificate Int Dyadic Ctx)
    (h : TarskiCertificate.check Int.sign EndpointSigns.intDyadic context p g a b value cert = true) :
    Sturm.check Sturm.orderSign context (ZPoly.toRatPoly p) (ZPoly.toRatPoly g)
      (a.map Dyadic.toRat) (b.map Dyadic.toRat) value (certificate cert) = true := by
  simpa only [Sturm.check, certificate, map_toRatPoly] using
    TarskiCertificate.map_checks (fun z : Int => (z : Rat)) (fun _ => Int.cast_eq_zero) Dyadic.toRat
      Int.sign Sturm.orderSign sign_int EndpointSigns.intDyadic (EndpointSigns.ofSign Sturm.orderSign)
      compare_eq evalSign_eq Int.cast_add Int.cast_sub Int.cast_mul Int.cast_one
      (fun _ => Int.cast_natCast _) context p g a b value cert h

end HexSturmMathlib.IntCast
