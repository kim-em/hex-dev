/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Cert

@[expose] public section
set_option backward.proofsInPublic true

/-!
Producer-independent content and primitive-part operations.

The recursive coefficient fold is parameterised by a concrete lower-arity
certificate producer. `Prs.lean` supplies that producer structurally, while
the checker remains independent of candidate production.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdOps R]

/-- Componentwise minimum of the monomials in the support, with zero for the
zero polynomial. -/
def monoContent (p : MvPoly n R cmp) : Mono n :=
  match p.support with
  | [] => Mono.zero
  | m :: ms => ms.foldl Mono.gcd m

/-- Producer-free scalar content. -/
def content (p : MvPoly n R cmp) : R :=
  scalarContent p

/-- Divide every stored coefficient by scalar content, with primitive part
zero for the zero polynomial. -/
def primPart (p : MvPoly n R cmp) : MvPoly n R cmp :=
  let c := content p
  if c = 0 then 0 else mapCoeffs (fun a => GcdOps.exactDiv a c) p

/-- Fold a concrete lower-arity gcd-certificate producer over coefficients.
The returned certificate stores every step that the checker replays. -/
def contentCertWith {R : Type u} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (coeffs : List (MvPoly n R cmp)) : ContentCert n R cmp :=
  let pair := coeffs.foldl
    (fun state q =>
      let step := produce state.1 q
      (step.gcd, state.2 ++ [step]))
    (0, [])
  .ofSteps pair.1 pair.2

/-- A producer-built fold has exactly one step per coefficient. -/
theorem contentCertWith_length {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (coeffs : List (MvPoly n R cmp)) :
    (contentCertWith produce coeffs).steps.length = coeffs.length := by
  sorry

/-- A producer-built fold checks when every supplied gcd certificate checks. -/
theorem contentCertWith_checks {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (hproduce : ∀ f h, checkGcd f h (produce f h) = true)
    (coeffs : List (MvPoly n R cmp)) :
    checkContent coeffs (contentCertWith produce coeffs) = true := by
  sorry

/-- Scalar content and primitive part reconstruct the input. -/
theorem content_mul_primPart [LawfulGcdOps R] (p : MvPoly n R cmp) :
    C (content p) * primPart p = p := by
  sorry

@[simp] theorem content_zero : content (0 : MvPoly n R cmp) = 0 := by
  rfl

@[simp] theorem primPart_zero : primPart (0 : MvPoly n R cmp) = 0 := by
  simp [primPart, content]

theorem content_primPart [LawfulGcdOps R] {p : MvPoly n R cmp} (hp : p ≠ 0) :
    content (primPart p) = 1 := by
  sorry

theorem content_mul [LawfulGcdOps R] (p q : MvPoly n R cmp) :
    content (p * q) = content p * content q := by
  sorry

theorem primPart_mul [LawfulGcdOps R] (p q : MvPoly n R cmp) :
    primPart (p * q) = primPart p * primPart q := by
  sorry

end Hex.MvPoly
