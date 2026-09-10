/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Cert
public import HexMvGcd.Gauss

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
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R]
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
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R]
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
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R]
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
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R]
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
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing R]
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
      simp only [ContentCert.ofSteps]
      rw [Cert.Content.value_ofSteps (E := RatLeaf R),
        Cert.Content.steps_ofSteps (E := RatLeaf R)]
      exact contentTrace_checks
        (checkGcdUsing (baseCheckCoprime (cmp := cmp))) produce hp coeffs
        (0 : MvPoly 0 R cmp)
  | succ n =>
      have hp : ∀ f h,
          checkGcdUsing (succCheckCoprime (checkOps (R := R) n) (cmp := cmp))
            f h (produce f h) = true := by
        simpa [checkGcd, checkOps] using hproduce
      simp only [checkContent, checkContentUsing]
      simp only [ContentCert.ofSteps]
      rw [Cert.Content.value_ofSteps (E := RatLeaf R),
        Cert.Content.steps_ofSteps (E := RatLeaf R)]
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
    rw [hcontent, primPart, hcontent, ite_eq_left rfl]
    rw [C_zero]
    exact zero_mul _
  · apply ext
    intro m
    have hzero : GcdOps.exactDiv (0 : R) (content p) = 0 := by
      simpa only [Lean.Grind.Semiring.zero_mul] using
        LawfulGcdOps.exactDiv_cancel (0 : R) (content p) hc
    rw [coeff_C_mul, primPart, ite_eq_right hc,
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

omit [Dvd R] [GcdOps R] in
private theorem C_mul (a b : R) :
    (C (a * b) : MvPoly n R cmp) = C a * C b := by
  unfold C
  rw [monomial_mul_monomial, Mono.zero_mul]

private theorem C_dvd_of_dvd_content [LawfulGcdOps R]
    {p : MvPoly n R cmp} {d : R} (hd : d ∣ content p) : C d ∣ p := by
  rcases (LawfulGcdOps.dvd_iff d (content p)).mp hd with ⟨x, hx⟩
  refine ⟨C x * primPart p, ?_⟩
  calc
    p = C (content p) * primPart p := (content_mul_primPart p).symm
    _ = C (d * x) * primPart p := by rw [hx]
    _ = (C d * C x) * primPart p := by rw [C_mul]
    _ = (C x * primPart p) * C d := by grind

private theorem scalar_dvd_coeff_of_C_dvd [LawfulGcdOps R]
    {p : MvPoly n R cmp} {d : R} (hd : C d ∣ p) (m : Mono n) :
    d ∣ coeff m p := by
  rcases hd with ⟨q, hq⟩
  apply (LawfulGcdOps.dvd_iff d (coeff m p)).mpr
  refine ⟨coeff m q, ?_⟩
  calc
    coeff m p = coeff m (q * C d) := congrArg (coeff m) hq
    _ = coeff m (C d * q) := by rw [MvPoly.mul_comm]
    _ = d * coeff m q := coeff_C_mul d q m

private theorem dvd_polyNormalize [LawfulGcdOps R]
    [IsMonomialOrder cmp] (p : MvPoly n R cmp) : p ∣ polyNormalize p := by
  refine ⟨polyNormUnit p, ?_⟩
  unfold polyNormalize
  exact MvPoly.mul_comm p (polyNormUnit p)

private theorem polyNormalize_dvd [LawfulGcdOps R]
    [IsMonomialOrder cmp] (p : MvPoly n R cmp) : polyNormalize p ∣ p := by
  rcases (polyIsUnit_iff (polyNormUnit p)).mp (polyNormUnit_isUnit p) with
    ⟨v, hv⟩
  refine ⟨v, ?_⟩
  unfold polyNormalize
  grind

private theorem eq_normalize_of_dvd [LawfulGcdOps R]
    (a b : R) (ha : normalize a = a) (hab : a ∣ b) (hba : b ∣ a) :
    a = normalize b := by
  rcases (LawfulGcdOps.dvd_iff a b).mp hab with ⟨q, hbq⟩
  by_cases hazero : a = 0
  · have hbzero : b = 0 := by rw [hbq, hazero, Lean.Grind.Semiring.zero_mul]
    rw [hazero, hbzero]
    unfold normalize
    rw [Lean.Grind.Semiring.zero_mul]
  · rcases (LawfulGcdOps.dvd_iff b a).mp hba with ⟨r, har⟩
    have hqr : q * r = 1 := by
      have hzero : a * (1 - q * r) = 0 := by
        rw [har, hbq]
        grind
      rcases LawfulGcdOps.no_zero_div a (1 - q * r) hzero with
        haz | hrest
      · exact False.elim (hazero haz)
      · grind
    have hqunit : GcdOps.isUnit q = true :=
      (LawfulGcdOps.isUnit_iff q).mpr ⟨r, hqr⟩
    symm
    calc
      normalize b = normalize (a * q) := congrArg normalize hbq
      _ = normalize a * normalize q := LawfulGcdOps.normalize_mul a q
      _ = a * 1 := by rw [ha, LawfulGcdOps.normalize_unit q hqunit]
      _ = a := Lean.Grind.Semiring.mul_one a

private theorem scalarContent_view_assoc
    {sourceCmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp sourceCmp] [Std.LawfulEqCmp sourceCmp] [LawfulGcdOps R]
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n + 1) R sourceCmp)
    (g : MvPoly n R cmp')
    (hdiv : ∀ k, g ∣ (toUnivariate i cmp' p).coeff k)
    (hgreat : ∀ d, (∀ k, d ∣ (toUnivariate i cmp' p).coeff k) → d ∣ g) :
    content p ∣ content g ∧ content g ∣ content p := by
  have hCleft : C (content p) ∣ g := by
    apply hgreat
    intro k
    apply C_dvd_of_dvd_content
    apply dvd_scalarContent
    intro m
    rw [toUnivariate_coeff]
    exact scalarContent_dvd_coeff p (insertVar i k m)
  have hleft : content p ∣ content g := by
    apply dvd_scalarContent
    intro m
    exact scalar_dvd_coeff_of_C_dvd hCleft m
  have hCright : C (content g) ∣ g := by
    apply C_dvd_of_dvd_content
    apply (LawfulGcdOps.dvd_iff (content g) (content g)).mpr
    exact ⟨1, (Lean.Grind.Semiring.mul_one _).symm⟩
  have hright : content g ∣ content p := by
    apply dvd_scalarContent
    intro m
    have hslice : C (content g) ∣
        (toUnivariate i cmp' p).coeff (Mono.degreeOf i m) :=
      Hex.dvdTrans hCright (hdiv (Mono.degreeOf i m))
    have hcoeff := scalar_dvd_coeff_of_C_dvd hslice (removeVar i m)
    rw [toUnivariate_coeff, insertVar_removeVar] at hcoeff
    exact hcoeff
  exact ⟨hleft, hright⟩

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] in
private theorem vars_eq_nil
    {cmp0 : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp0] [Std.LawfulEqCmp cmp0]
    (p : MvPoly 0 R cmp0) : p.vars = [] := by
  cases h : p.vars with
  | nil => rfl
  | cons i is => exact Fin.elim0 i

/-- Content of a constant is its normalized coefficient. -/
theorem content_C [LawfulGcdOps R] (a : R) :
    content (C a : MvPoly n R cmp) = normalize a := by
  unfold content scalarContent
  rw [termsList_C]
  by_cases ha : a = 0
  · rw [ite_eq_left ha, ha, normalize]
    exact (Lean.Grind.Semiring.zero_mul _).symm
  · rw [ite_eq_right ha]
    rfl

theorem content_mul [LawfulGcdOps R] (p q : MvPoly n R cmp) :
    content (p * q) = content p * content q := by
  induction n with
  | zero =>
      have hp : p = C (coeff Mono.zero p) :=
        eq_C_of_vars_eq_nil p (vars_eq_nil p)
      have hq : q = C (coeff Mono.zero q) :=
        eq_C_of_vars_eq_nil q (vars_eq_nil q)
      rw [hp, hq, ← C_mul, content_C, content_C, content_C,
        LawfulGcdOps.normalize_mul]
  | succ n ih =>
      let pv := toUnivariate 0 Mono.lex p
      let qv := toUnivariate 0 Mono.lex q
      let pqv := toUnivariate 0 Mono.lex (p * q)
      let rp := denseContent pv
      let rq := denseContent qv
      let rpq := denseContent pqv
      let dp := polyNormalize rp
      let dq := polyNormalize rq
      let dpq := polyNormalize rpq
      have hdpDiv : ∀ k, dp ∣ pv.coeff k := by
        intro k
        exact Hex.dvdTrans (polyNormalize_dvd rp)
          (denseContent_dvd_coeff pv k)
      have hdpGreat : ∀ d, (∀ k, d ∣ pv.coeff k) → d ∣ dp := by
        intro d hd
        exact Hex.dvdTrans (dvd_denseContent pv d hd)
          (dvd_polyNormalize rp)
      have hdqDiv : ∀ k, dq ∣ qv.coeff k := by
        intro k
        exact Hex.dvdTrans (polyNormalize_dvd rq)
          (denseContent_dvd_coeff qv k)
      have hdqGreat : ∀ d, (∀ k, d ∣ qv.coeff k) → d ∣ dq := by
        intro d hd
        exact Hex.dvdTrans (dvd_denseContent qv d hd)
          (dvd_polyNormalize rq)
      have hdpqDiv : ∀ k, dpq ∣ pqv.coeff k := by
        intro k
        exact Hex.dvdTrans (polyNormalize_dvd rpq)
          (denseContent_dvd_coeff pqv k)
      have hdpqGreat : ∀ d, (∀ k, d ∣ pqv.coeff k) → d ∣ dpq := by
        intro d hd
        exact Hex.dvdTrans (dvd_denseContent pqv d hd)
          (dvd_polyNormalize rpq)
      have hpAssoc := scalarContent_view_assoc 0 Mono.lex p dp hdpDiv hdpGreat
      have hqAssoc := scalarContent_view_assoc 0 Mono.lex q dq hdqDiv hdqGreat
      have hpqAssoc := scalarContent_view_assoc 0 Mono.lex (p * q) dpq
        hdpqDiv hdpqGreat
      have hview : pqv = pv * qv := toUnivariate_mul 0 p q
      have hraw := denseContent_mul_assoc pv qv
      rw [← hview] at hraw
      have hnorm : dpq = dp * dq := by
        have hforward : dpq ∣ rp * rq :=
          Hex.dvdTrans (polyNormalize_dvd rpq) hraw.1
        have hback : rp * rq ∣ dpq :=
          Hex.dvdTrans hraw.2 (dvd_polyNormalize rpq)
        have hcanon := eq_polyNormalize_of_dvd dpq (rp * rq)
          (polyNormalize_idem rpq) hforward hback
        calc
          dpq = polyNormalize (rp * rq) := hcanon
          _ = polyNormalize rp * polyNormalize rq := polyNormalize_mul rp rq
          _ = dp * dq := rfl
      have hlower : content dpq = content dp * content dq := by
        rw [hnorm]
        exact ih (cmp := Mono.lex) dp dq
      have hforward : content (p * q) ∣ content p * content q :=
        Hex.dvdTrans hpqAssoc.1 (by
          rw [hlower]
          exact Hex.dvdMul hpAssoc.2 hqAssoc.2)
      have hback : content p * content q ∣ content (p * q) :=
        Hex.dvdTrans (Hex.dvdMul hpAssoc.1 hqAssoc.1) (by
          rw [← hlower]
          exact hpqAssoc.2)
      have hcanon := eq_normalize_of_dvd
        (content (p * q)) (content p * content q)
        (normalize_scalarContent (p * q)) hforward hback
      have hpNorm : normalize (content p) = content p :=
        normalize_scalarContent p
      have hqNorm : normalize (content q) = content q :=
        normalize_scalarContent q
      rw [LawfulGcdOps.normalize_mul, hpNorm, hqNorm] at hcanon
      exact hcanon

theorem primPart_mul [LawfulGcdOps R] (p q : MvPoly n R cmp) :
    primPart (p * q) = primPart p * primPart q := by
  by_cases hp : p = 0
  · subst p
    rw [MvPoly.zero_mul, primPart_zero, MvPoly.zero_mul]
  by_cases hq : q = 0
  · subst q
    rw [MvPoly.mul_zero, primPart_zero, MvPoly.mul_zero]
  let cp := content p
  let cq := content q
  let pp := primPart p
  let pq := primPart q
  have hrecp : C cp * pp = p := content_mul_primPart p
  have hrecq : C cq * pq = q := content_mul_primPart q
  have hcp : cp ≠ 0 := by
    intro hzero
    rw [hzero, C_zero, MvPoly.zero_mul] at hrecp
    exact hp hrecp.symm
  have hcq : cq ≠ 0 := by
    intro hzero
    rw [hzero, C_zero, MvPoly.zero_mul] at hrecq
    exact hq hrecq.symm
  have hcpcq : cp * cq ≠ 0 := by
    intro hzero
    rcases LawfulGcdOps.no_zero_div cp cq hzero with hzero | hzero
    · exact hcp hzero
    · exact hcq hzero
  have hC :
      (C (cp * cq) : MvPoly n R cmp) = C cp * C cq := C_mul cp cq
  have hleft :
      (C cp * C cq) * primPart (p * q) = p * q := by
    calc
      (C cp * C cq) * primPart (p * q) =
          C (cp * cq) * primPart (p * q) := by rw [hC]
      _ = C (content (p * q)) * primPart (p * q) := by rw [content_mul]
      _ = p * q := content_mul_primPart (p * q)
  have hright : p * q = (C cp * C cq) * (pp * pq) := by
    calc
      p * q = (C cp * pp) * (C cq * pq) := by rw [hrecp, hrecq]
      _ = (C cp * C cq) * (pp * pq) := by grind
  have heq :
      (C cp * C cq) * primPart (p * q) =
        (C cp * C cq) * (pp * pq) := hleft.trans hright
  apply ext
  intro m
  have hcoeff := congrArg (coeff m) heq
  rw [← hC, coeff_C_mul, coeff_C_mul] at hcoeff
  have hzero :
      (cp * cq) *
          (coeff m (primPart (p * q)) - coeff m (pp * pq)) = 0 := by
    grind
  rcases LawfulGcdOps.no_zero_div (cp * cq)
      (coeff m (primPart (p * q)) - coeff m (pp * pq)) hzero with
    hzero | hzero
  · exact False.elim (hcpcq hzero)
  · grind

end Hex.MvPoly
