/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsTheory.TarskiSoundness
public import HexRealRootsTheory.TarskiDomain
public import HexRealRootsTheory.RealClosed

public section

namespace HexRealRootsTheory.Tarski

open Hex HexPolyTheory.Interpret

/-- The integer/dyadic replay has root-sum semantics for arbitrary accepted evidence. -/
theorem integer_check_sound {Ctx : Type*} [DecidableEq Ctx] (context : Ctx)
    (p q : ZPoly) (a b : Endpoint Dyadic) (value : Int)
    (certificate : TarskiCertificate Int Dyadic Ctx)
    (checked : TarskiCertificate.check Int.sign EndpointSigns.intDyadic
      context p q a b value certificate = true) :
    value = rootSum (toPolyℝ p) (toPolyℝ q) (a.map Dyadic.toReal) (b.map Dyadic.toReal) := by
  have hsign (z : Int) : z.sign = (SignType.sign (z : ℝ) : Int) := by
    rcases lt_trichotomy z 0 with h | rfl | h
    · rw [Int.sign_eq_neg_one_of_neg h, sign_neg (Int.cast_lt_zero.mpr h)]
      rfl
    · simp
    · rw [Int.sign_eq_one_of_pos h, sign_pos (Int.cast_pos.mpr h)]
      rfl
  have hd (d : Dyadic) : dyadicSign d = (SignType.sign (Dyadic.toReal d) : Int) := by
    have hs := sign_dyadicSign d
    have bound : dyadicSign d = -1 ∨ dyadicSign d = 0 ∨ dyadicSign d = 1 := by
      cases d with
      | zero => simp [dyadicSign]
      | ofOdd n k hn => simp only [dyadicSign]; split <;> simp
    rcases bound with h | h | h <;> rw [h] at hs ⊢
    all_goals
      norm_num at hs
      simpa using congrArg (fun s : SignType => (s : Int)) hs
  have h := check_rootSum (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
    Int.cast_one Int.cast_add Int.cast_sub Int.cast_mul (fun n => Int.cast_natCast n)
    Int.sign hsign Dyadic.toReal EndpointSigns.intDyadic
    (fun x y => by simp only [EndpointSigns.intDyadic, hd, toReal_eq_cast_toRat, Dyadic.toRat_sub, Rat.cast_sub])
    (fun p x => by
      simp only [EndpointSigns.intDyadic, hd, interpret_int_real, toReal_evalDyadic])
    context p q a b value certificate checked
  simpa only [interpret_int_real] using h

end HexRealRootsTheory.Tarski

namespace Hex

open HexRealRootsTheory

/-- Every accepted integer certificate proves its stated signed root sum. -/
theorem IntTarskiCertificate.check_sound (p q : ZPoly) (I : DyadicInterval) (value : Int)
    (certificate : IntTarskiCertificate)
    (checked : IntTarskiCertificate.check p q I value certificate = true) :
    value = Tarski.rootSum (toPolyℝ p) (toPolyℝ q)
      (.finite (HexRealRootsTheory.Dyadic.toReal I.lower)) (.finite (HexRealRootsTheory.Dyadic.toReal I.upper)) :=
  Tarski.integer_check_sound () p q _ _ value certificate checked

/-- The integer/dyadic query computes the signed sum over the distinct interval roots. -/
theorem ZPoly.tarskiQuery_eq (p q : ZPoly) (I : DyadicInterval) (value : Int)
    (result : ZPoly.tarskiQuery p q I = some value) :
    value = Tarski.rootSum (toPolyℝ p) (toPolyℝ q)
      (.finite (HexRealRootsTheory.Dyadic.toReal I.lower)) (.finite (HexRealRootsTheory.Dyadic.toReal I.upper)) := by
  obtain ⟨certificate, produced, hvalue⟩ := Option.map_eq_some_iff.mp result
  have checked := (Tarski.integer_certify_checks p q I certificate produced).1
  rw [← hvalue]
  exact IntTarskiCertificate.check_sound p q I certificate.value certificate checked

/-- Integer querying succeeds exactly for a nonzero squarefree head with root-free endpoints. -/
theorem ZPoly.tarskiQuery_isSome (p q : ZPoly) (I : DyadicInterval) :
    (ZPoly.tarskiQuery p q I).isSome = true ↔
      p ≠ 0 ∧ Squarefree (toPolyℝ p) ∧
        (toPolyℝ p).eval (HexRealRootsTheory.Dyadic.toReal I.lower) ≠ 0 ∧
        (toPolyℝ p).eval (HexRealRootsTheory.Dyadic.toReal I.upper) ≠ 0 :=
  Tarski.integer_domain p q I

/-- A query on an interval with one root returns the query polynomial's sign there. -/
theorem ZPoly.tarskiQuery_sign (p q : ZPoly) (I : DyadicInterval) (value : Int) (x : ℝ)
    (result : ZPoly.tarskiQuery p q I = some value)
    (single : Tarski.rootsIn (toPolyℝ p) (.finite (HexRealRootsTheory.Dyadic.toReal I.lower))
      (.finite (HexRealRootsTheory.Dyadic.toReal I.upper)) = {x}) :
    value = (SignType.sign ((toPolyℝ q).eval x) : Int) := by
  rw [ZPoly.tarskiQuery_eq p q I value result]
  exact Tarski.rootSum_singleton _ _ _ _ x single

end Hex
