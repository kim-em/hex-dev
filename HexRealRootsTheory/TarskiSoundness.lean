/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsTheory.TarskiFoundation
public import HexRealRootsTheory.TarskiSum
public import HexRealRoots.Map
public import Mathlib.FieldTheory.IsRealClosed.Basic

public section

namespace HexRealRootsTheory.Tarski

open Hex HexPolyTheory.Interpret

/-- Every accepted shared query certificate gives the sum of signs at the
distinct roots in its open interval. Coefficient representations need only
reflect zero and preserve the actual operations; endpoint representations
may differ from coefficients. This includes infinite endpoints, constant
heads, zero queries and common factors, with no producer-success premise. -/
theorem check_rootSum
    {D : Type u} {E : Type v} {Ctx : Type w} {R : Type u₁}
    [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    [DecidableEq E] [DecidableEq Ctx]
    [Field R] [DecidableEq R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (f : D → R) (hz : ∀ a, f a = 0 ↔ a = 0)
    (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
    (hs : ∀ a b, f (a - b) = f a - f b)
    (hm : ∀ a b, f (a * b) = f a * f b)
    (hnat : ∀ n : Nat, f (n : D) = (n : R))
    (sign : D → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (point : E → R) (ends : EndpointSigns D E)
    (hcompare : ∀ a b, ends.compare a b = (SignType.sign (point a - point b) : Int))
    (heval : ∀ p a, ends.evalSign p a = (SignType.sign ((interpret f hz p).eval (point a)) : Int))
    (context : Ctx) (p q : DensePoly D) (a b : Endpoint E) (value : Int)
    (certificate : TarskiCertificate D E Ctx)
    (checked : TarskiCertificate.check sign ends context p q a b value certificate = true) :
    value = rootSum (interpret f hz p) (interpret f hz q) (a.map point) (b.map point) := by
  have cast_one : ∀ s : SignType, (s : Int) = 1 ↔ s = 1 := by decide
  have cast_zero : ∀ s : SignType, (s : Int) = 0 ↔ s = 0 := by decide
  have cast_neg : ∀ s : SignType, (s : Int) < 0 ↔ s = -1 := by decide
  have hpos (x : D) : sign x = 1 ↔ 0 < f x := by
    rw [hsign, cast_one, sign_eq_one_iff]
  have guards := checked
  simp only [TarskiCertificate.check_eq, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at guards
  obtain ⟨_, _, _, _, _, _, he, hsf, hlast, _⟩ := guards
  simp only [TarskiCertificate.checkEndpoints, Bool.and_eq_true] at he
  have sf := (check_squarefree f hz ha hs hm hnat sign hpos h1 p certificate.squarefree hsf).mp hlast
  obtain ⟨hr, hv⟩ := check_value sign ends context p q a b value certificate checked
  rw [hv, signs_variations f hz sign point ends hsign heval,
    signs_variations f hz sign point ends hsign heval]
  have hc := check_signed f hz ha hs hm sign hpos p q certificate.remainders hr
  have seed := check_seed f hz ha hs hm hnat sign hpos p q certificate.remainders hr
  have head : (chainPolys f hz certificate.remainders)[0]? = some (interpret f hz p) := by
    have hn := (check_bound f hz sign p q certificate.remainders hr).1
    have hd := chainPolys_getD f hz certificate.remainders 0
    rw [check_head sign p q certificate.remainders hr] at hd
    have hl : 0 < (chainPolys f hz certificate.remainders).length := by
      simpa [chainPolys] using hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at hd
    simpa only [List.getElem?_eq_getElem hl, Option.getD_some] using congrArg some hd
  change (variations (chainPolys f hz certificate.remainders) (a.map point) : Int) -
    variations (chainPolys f hz certificate.remainders) (b.map point) = _
  generalize hcs : chainPolys f hz certificate.remainders = ps at hc seed head ⊢
  cases ps with
  | nil => simp at head
  | cons p₀ cs =>
    have hp₀ : p₀ = interpret f hz p := by simpa using head
    subst p₀
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      ← List.head?_eq_getElem?] at seed
    apply variation_eq _ _ cs hc seed sf
    · have horder := he.1.1.2
      cases a <;> cases b <;>
        simp_all only [Endpoint.lt, Endpoint.map, decide_eq_true_eq,
          sign_eq_neg_one_iff, sub_lt_zero, Bool.false_eq_true]
    · intro x hx
      cases a with
      | negInf => cases hx
      | posInf => cases hx
      | finite a =>
        cases hx
        have hn := he.1.2
        simpa only [Endpoint.nonvanishing, bne_iff_ne, heval, ne_eq, cast_zero,
          sign_eq_zero_iff] using hn
    · intro x hx
      cases b with
      | negInf => cases hx
      | posInf => cases hx
      | finite b =>
        cases hx
        have hn := he.2
        simpa only [Endpoint.nonvanishing, bne_iff_ne, heval, ne_eq, cast_zero,
          sign_eq_zero_iff] using hn

end HexRealRootsTheory.Tarski
