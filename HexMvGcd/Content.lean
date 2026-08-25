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
The returned certificate stores every step that the checker replays. Steps are
consed into a reversed accumulator and reversed once after the fold. -/
def contentCertWith {R : Type u} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (coeffs : List (MvPoly n R cmp)) : ContentCert n R cmp :=
  let pair := coeffs.foldl
    (fun state q =>
      let step := produce state.1 q
      (step.gcd, step :: state.2))
    (0, [])
  .ofSteps pair.1 pair.2.reverse

/-- Forward-order specification of the reverse-accumulator content fold. -/
private def contentTrace {R : Type u} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp) :
    MvPoly n R cmp → List (MvPoly n R cmp) →
      MvPoly n R cmp × List (GcdCert n R cmp)
  | acc, [] => (acc, [])
  | acc, q :: qs =>
      let step := produce acc q
      let tail := contentTrace produce step.gcd qs
      (tail.1, step :: tail.2)

private theorem contentFold_eq_trace {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (coeffs : List (MvPoly n R cmp)) (acc : MvPoly n R cmp)
    (done : List (GcdCert n R cmp)) :
    let pair := coeffs.foldl
      (fun state q =>
        let step := produce state.1 q
        (step.gcd, step :: state.2))
      (acc, done)
    (pair.1, pair.2.reverse) =
      let trace := contentTrace produce acc coeffs
      (trace.1, done.reverse ++ trace.2) := by
  induction coeffs generalizing acc done with
  | nil => simp [contentTrace]
  | cons q qs ih =>
      simp only [List.foldl_cons, contentTrace]
      rw [ih]
      simp [List.append_assoc]

private theorem contentCertWith_eq_trace {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (coeffs : List (MvPoly n R cmp)) :
    contentCertWith produce coeffs =
      let trace := contentTrace produce 0 coeffs
      ContentCert.ofSteps trace.1 trace.2 := by
  unfold contentCertWith
  simpa using congrArg
    (fun pair => ContentCert.ofSteps pair.1 pair.2)
    (contentFold_eq_trace produce coeffs 0 [])

private theorem contentTrace_checks {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (check : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp → Bool)
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (hproduce : ∀ f h, check f h (produce f h) = true)
    (coeffs : List (MvPoly n R cmp)) (acc : MvPoly n R cmp) :
    let trace := contentTrace produce acc coeffs
    checkContentSteps check trace.1 acc coeffs trace.2 = true := by
  induction coeffs generalizing acc with
  | nil => simp [contentTrace]
  | cons q qs ih =>
      simp only [contentTrace, checkContentSteps]
      rw [hproduce, Bool.true_and]
      exact ih (produce acc q).gcd

/-- A producer-built fold has exactly one step per coefficient. -/
theorem contentCertWith_length {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (coeffs : List (MvPoly n R cmp)) :
    (contentCertWith produce coeffs).steps.length = coeffs.length := by
  have aux : ∀ (xs : List (MvPoly n R cmp))
      (state : MvPoly n R cmp × List (GcdCert n R cmp)),
      (xs.foldl
          (fun state q =>
            let step := produce state.1 q
            (step.gcd, step :: state.2))
          state).2.length = state.2.length + xs.length := by
    intro xs
    induction xs with
    | nil =>
        intro state
        simp
    | cons q qs ih =>
        intro state
        rw [List.foldl_cons, ih]
        simp only [List.length_cons]
        omega
  have ofList_length : ∀ (steps : List (GcdCert n R cmp)),
      (GcdCerts.ofList steps).toList.length = steps.length := by
    intro steps
    induction steps with
    | nil => rfl
    | cons step steps ih =>
        simp only [GcdCerts.toList, List.length_cons, ih]
  unfold contentCertWith ContentCert.steps ContentCert.ofSteps
  rw [ofList_length, List.length_reverse]
  rw [aux]
  simp

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
  rw [contentCertWith_eq_trace]
  cases n with
  | zero =>
      have hp : ∀ f h,
          checkGcdUsing (baseCheckCoprime (cmp := cmp)) f h
            (produce f h) = true := by
        simpa [checkGcd, checkOps] using hproduce
      simp only [checkContent, checkContentUsing]
      rw [ContentCert.value_ofSteps, ContentCert.steps_ofSteps]
      exact contentTrace_checks
        (checkGcdUsing (baseCheckCoprime (cmp := cmp))) produce hp coeffs
        (0 : MvPoly 0 R cmp)
  | succ n =>
      have hp : ∀ f h,
          checkGcdUsing (succCheckCoprime (checkOps (R := R) n) (cmp := cmp))
            f h (produce f h) = true := by
        simpa [checkGcd, checkOps] using hproduce
      simp only [checkContent, checkContentUsing]
      rw [ContentCert.value_ofSteps, ContentCert.steps_ofSteps]
      exact contentTrace_checks
        (checkGcdUsing
          (succCheckCoprime (checkOps (R := R) n) (cmp := cmp)))
        produce hp coeffs (0 : MvPoly (n + 1) R cmp)

/-- The final value of a producer-built content fold is normalized whenever
every supplied gcd certificate checks. -/
theorem contentCertWith_normalized {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    (produce : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp)
    (hproduce : ∀ f h, checkGcd f h (produce f h) = true)
    (coeffs : List (MvPoly n R cmp)) :
    polyNormalize (contentCertWith produce coeffs).value =
      (contentCertWith produce coeffs).value := by
  have aux : ∀ (xs : List (MvPoly n R cmp))
      (state : MvPoly n R cmp × List (GcdCert n R cmp)),
      polyNormalize state.1 = state.1 →
      let result := xs.foldl
        (fun state q =>
          let step := produce state.1 q
          (step.gcd, step :: state.2))
        state
      polyNormalize result.1 = result.1 := by
    intro xs
    induction xs with
    | nil =>
        intro state hstate
        exact hstate
    | cons q qs ih =>
        intro state _
        simp only [List.foldl_cons]
        apply ih
        exact (checkGcd_sound (hproduce state.1 q)).2.2.1
  unfold contentCertWith ContentCert.value ContentCert.ofSteps
  exact aux coeffs (0, []) polyNormalize_zero

/-- Scalar content and primitive part reconstruct the input. -/
theorem content_mul_primPart [LawfulGcdOps R] (p : MvPoly n R cmp) :
    C (content p) * primPart p = p := by
  by_cases hc : content p = 0
  · have hp : p = 0 := by
      apply ext
      intro m
      have hdiv := scalarContent_dvd_coeff p m
      rw [← content, hc] at hdiv
      rcases (LawfulGcdOps.dvd_iff 0 (coeff m p)).mp hdiv with ⟨q, hq⟩
      rw [hq, Lean.Grind.Semiring.zero_mul, coeff_zero]
    subst p
    have hcontent : content (0 : MvPoly n R cmp) = 0 := rfl
    rw [hcontent, primPart, hcontent, Hex.ite_eq_left rfl]
    rw [C_zero]
    exact zero_mul _
  · apply ext
    intro m
    have hzero : GcdOps.exactDiv (0 : R) (content p) = 0 := by
      simpa only [Lean.Grind.Semiring.zero_mul] using
        LawfulGcdOps.exactDiv_cancel (0 : R) (content p) hc
    rw [coeff_C_mul, primPart, Hex.ite_eq_right hc,
      coeff_mapCoeffs hzero]
    have hdiv := scalarContent_dvd_coeff p m
    rw [← content] at hdiv
    rcases (LawfulGcdOps.dvd_iff (content p) (coeff m p)).mp hdiv with
      ⟨q, hq⟩
    rw [hq, Lean.Grind.CommSemiring.mul_comm (content p) q,
      LawfulGcdOps.exactDiv_cancel q (content p) hc,
      Lean.Grind.CommSemiring.mul_comm]

omit [Dvd R] in
@[simp] theorem content_zero : content (0 : MvPoly n R cmp) = 0 := by
  rfl

omit [Dvd R] in
@[simp] theorem primPart_zero : primPart (0 : MvPoly n R cmp) = 0 := by
  simp [primPart, content]

theorem content_primPart [LawfulGcdOps R] {p : MvPoly n R cmp} (hp : p ≠ 0) :
    content (primPart p) = 1 := by
  let c := content p
  let q := primPart p
  let d := content q
  have hc : c ≠ 0 := by
    intro hc
    apply hp
    rw [← content_mul_primPart p]
    change C c * q = 0
    rw [hc, C_zero, zero_mul]
  have hcoeff : ∀ m, coeff m p = c * coeff m q := by
    intro m
    rw [← content_mul_primPart p]
    exact coeff_C_mul c q m
  have hcd : c * d ∣ c := by
    have hcommon : ∀ m, c * d ∣ coeff m p := by
      intro m
      have hd := scalarContent_dvd_coeff q m
      change d ∣ coeff m q at hd
      rcases (LawfulGcdOps.dvd_iff d (coeff m q)).mp hd with ⟨a, ha⟩
      apply (LawfulGcdOps.dvd_iff (c * d) (coeff m p)).mpr
      refine ⟨a, ?_⟩
      rw [hcoeff, ha, Lean.Grind.Semiring.mul_assoc]
    have := dvd_scalarContent p (c * d) hcommon
    change c * d ∣ c at this
    exact this
  rcases (LawfulGcdOps.dvd_iff (c * d) c).mp hcd with ⟨u, hu⟩
  have hunit : d * u = 1 := by
    have hzero : c * (1 - d * u) = 0 := by
      calc
        c * (1 - d * u) = c - (c * d) * u := by grind
        _ = 0 := by rw [← hu]; grind
    rcases LawfulGcdOps.no_zero_div c (1 - d * u) hzero with hczero | hrest
    · exact False.elim (hc hczero)
    · grind
  have hisUnit : GcdOps.isUnit d = true :=
    (LawfulGcdOps.isUnit_iff d).mpr ⟨u, hunit⟩
  have hnorm : normalize d = d := by
    exact normalize_scalarContent q
  calc
    content (primPart p) = d := rfl
    _ = normalize d := hnorm.symm
    _ = 1 := LawfulGcdOps.normalize_unit d hisUnit

theorem content_mul [LawfulGcdOps R] (p q : MvPoly n R cmp) :
    content (p * q) = content p * content q := by
  sorry

theorem primPart_mul [LawfulGcdOps R] (p q : MvPoly n R cmp) :
    primPart (p * q) = primPart p * primPart q := by
  sorry

end Hex.MvPoly
