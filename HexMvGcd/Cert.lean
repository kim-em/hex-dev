/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Modulus
public import HexMvGcd.CertData
public import HexPolyFp

@[expose] public section
set_option backward.proofsInPublic true

/-!
Checked recursive certificates for multivariate gcd and content.

The three datatypes are mutually inductive because positive-arity coprimality
certificates contain checked coefficient-content folds, whose steps are gcd
certificates one arity lower.  Every cycle therefore decreases the arity.
-/

namespace Hex.MvPoly

universe u v

/-- Coefficientwise image followed by evaluation of all remaining variables,
leaving one dense univariate polynomial over the bundled prime field. -/
def imageAt {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (P : ZMod64.Prime)
    (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds)
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (f : MvPoly (n + 1) R cmp) :
    @FpPoly P.m P.bounds :=
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  let q := toUnivariate i cmp' f
  DensePoly.ofList <| (List.range q.size).map fun k =>
    MvPoly.eval a (MvPoly.mapCoeffs φ.toField (q.coeff k))

/-- Computational core of `imageAt`, taking the underlying coefficient map. -/
def imageAtRaw {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (P : ZMod64.Prime)
    (φ : R → @ZMod64 P.m P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds)
    (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (f : MvPoly (n + 1) R cmp) :
    @FpPoly P.m P.bounds :=
  letI : ZMod64.Bounds P.m := P.bounds
  letI : ZMod64.PrimeModulus P.m := ZMod64.primeModulusOfPrime P.prime
  let q := toUnivariate i cmp' f
  DensePoly.ofList <| (List.range q.size).map fun k =>
    MvPoly.eval a (MvPoly.mapCoeffs φ (q.coeff k))

/-- Coefficientwise cast from the integer model used by `ratLift`. -/
def intModelToRat {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : MvPoly n Rat cmp :=
  mapCoeffs (fun z : Int => (z : Rat)) p

/-- The three replay operations at one arity.  Packaging them by arity avoids
Lean's well-founded mutual-recursion compiler: recursive certificate calls
always move to the already-built lower-arity package, while content folds are
ordinary structural recursion on their two lists. -/
structure Cert.CheckOpsAt (R : Type u) [Lean.Grind.CommRing R]
    (E : Cert.Leaves.{v}) (n : Nat) : Type (max (u + 1) (v + 1)) where
  coprime : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → Cert.Coprime R E n cmp → Bool
  gcd : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → Cert.Gcd R E n cmp → Bool
  content : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    List (MvPoly n R cmp) → Cert.Content R E n cmp → Bool

@[reducible] def checkGcdUsing {n : Nat} {R : Type u} {E : Cert.Leaves.{v}}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (coprime : MvPoly n R cmp → MvPoly n R cmp →
      Cert.Coprime R E n cmp → Bool)
    (f h : MvPoly n R cmp) (cert : Cert.Gcd R E n cmp) : Bool :=
  (cert.gcd * cert.cofL == f) &&
    (cert.gcd * cert.cofR == h) &&
    (polyNormalize cert.gcd == cert.gcd) &&
    coprime cert.cofL cert.cofR cert.coprime

/-! `checkContentSteps` exposes the accumulator used by content replay.  The
public checker fixes that accumulator to zero; keeping the general recursion
named lets producer proofs state the natural induction invariant. -/

@[reducible] def checkContentSteps {n : Nat} {R : Type u} {E : Cert.Leaves.{v}}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (gcd : MvPoly n R cmp → MvPoly n R cmp → Cert.Gcd R E n cmp → Bool)
    (value acc : MvPoly n R cmp) :
    List (MvPoly n R cmp) → List (Cert.Gcd R E n cmp) → Bool
  | [], [] => acc == value
  | q :: qs, step :: steps =>
      gcd acc q step && checkContentSteps gcd value step.gcd qs steps
  | _, _ => false

@[reducible] def checkContentUsing {n : Nat} {R : Type u} {E : Cert.Leaves.{v}}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (gcd : MvPoly n R cmp → MvPoly n R cmp → Cert.Gcd R E n cmp → Bool)
    (coeffs : List (MvPoly n R cmp)) (cert : Cert.Content R E n cmp) : Bool :=
  checkContentSteps gcd cert.value 0 coeffs cert.steps

@[reducible] def Cert.baseCheck {S : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    {cmp : Mono 0 → Mono 0 → Ordering}
    [IsMonomialOrder cmp]
    (checkLeaf : MvPoly 0 S cmp → MvPoly 0 S cmp → E 0 cmp → Bool)
    (f h : MvPoly 0 S cmp) (cert : Cert.Coprime S E 0 cmp) : Bool :=
  match cert with
  | .unit => polyIsUnit f || polyIsUnit h
  | .base u v => u * coeff Mono.zero f + v * coeff Mono.zero h == 1
  | .bezout u v => u * f + v * h == 1
  | .leaf data => checkLeaf f h data

@[reducible] def Cert.succCheck {n : Nat} {S : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    (lower : Cert.CheckOpsAt S E n)
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    (checkLeaf : MvPoly (n + 1) S cmp → MvPoly (n + 1) S cmp → E (n + 1) cmp → Bool)
    (f h : MvPoly (n + 1) S cmp)
    (cert : Cert.Coprime S E (n + 1) cmp) : Bool := by
  cases cert with
  | unit => exact polyIsUnit f || polyIsUnit h
  | bezout u v => exact u * f + v * h == 1
  | leaf data => exact checkLeaf f h data
  | split i cmp' P φ a α β left right rest =>
      letI : ZMod64.Bounds P.m := P.bounds
      letI : ZMod64.PrimeModulus P.m :=
        ZMod64.primeModulusOfPrime P.prime
      let fImage := imageAtRaw P φ.toField a i cmp' f
      let hImage := imageAtRaw P φ.toField a i cmp' h
      let fView := toUnivariate i cmp' f
      let hView := toUnivariate i cmp' h
      exact decide (fImage.degree? = fView.degree?) &&
        decide (hImage.degree? = hView.degree?) &&
        (α * fImage + β * hImage == 1) &&
        lower.content cmp' fView.toArray.toList left &&
        lower.content cmp' hView.toArray.toList right &&
        lower.coprime cmp' left.value right.value rest
  | splitBezout i cmp' u v r left right rest =>
      let fView := toUnivariate i cmp' f
      let hView := toUnivariate i cmp' h
      exact decide (r ≠ 0) &&
        (u * f + v * h == constIn i cmp' r) &&
        lower.content cmp' fView.toArray.toList left &&
        lower.content cmp' hView.toArray.toList right &&
        lower.coprime cmp' left.value right.value rest

@[reducible] def Cert.checkOps {S : Type u} {E : Cert.Leaves.{v}}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    (checkLeaf : (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
      [IsMonomialOrder cmp] → MvPoly n S cmp → MvPoly n S cmp → E n cmp → Bool) :
    (n : Nat) → Cert.CheckOpsAt S E n
  | 0 =>
      { coprime := fun cmp _ => Cert.baseCheck (cmp := cmp) (checkLeaf 0 cmp)
        gcd := fun cmp _ => checkGcdUsing (Cert.baseCheck (cmp := cmp) (checkLeaf 0 cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (Cert.baseCheck (cmp := cmp) (checkLeaf 0 cmp))) }
  | n + 1 =>
      let lower := Cert.checkOps checkLeaf n
      { coprime := fun cmp _ => Cert.succCheck lower (cmp := cmp) (checkLeaf (n + 1) cmp)
        gcd := fun cmp _ => checkGcdUsing (Cert.succCheck lower (cmp := cmp) (checkLeaf (n + 1) cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (Cert.succCheck lower (cmp := cmp) (checkLeaf (n + 1) cmp))) }

/-- Replay rational scaling and primitive integer-model coprimality. -/
@[reducible] def checkRatLift {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    (f h : MvPoly n Rat cmp) (lift : RatLiftCert n cmp) : Bool :=
  decide (lift.scaleL ≠ 0) && decide (lift.scaleR ≠ 0) &&
    (f == C lift.scaleL * intModelToRat lift.left) &&
    (h == C lift.scaleR * intModelToRat lift.right) &&
    decide (scalarContent lift.left = 1) &&
    decide (scalarContent lift.right = 1) &&
    (Cert.checkOps (S := Int) (E := Cert.NoLeaves)
      (fun _ _ _ _ _ impossible => nomatch impossible) n).coprime
        cmp lift.left lift.right lift.cert

/-- Replay a rational leaf entirely with canonical `Int` and `Rat` operations. -/
@[reducible] def checkRatLeaf {n : Nat} {R : Type u} [Lean.Grind.CommRing R]
    [DecidableEq R] [BEq R] [LawfulBEq R]
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly n R cmp) (leaf : RatLeaf R n cmp) : Bool :=
  checkRatLift (mapCoeffs leaf.model.toRat f) (mapCoeffs leaf.model.toRat h) leaf.data

/-- Replay package for certificates with canonical rational leaves. -/
abbrev CheckOpsAt (R : Type u) [Lean.Grind.CommRing R] (n : Nat) :=
  Cert.CheckOpsAt R (RatLeaf R) n

@[reducible] def baseCheckCoprime {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    {cmp : Mono 0 → Mono 0 → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly 0 R cmp) (cert : CoprimeCert 0 R cmp) : Bool :=
  Cert.baseCheck checkRatLeaf f h cert

@[reducible] def succCheckCoprime {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] (lower : CheckOpsAt R n)
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) R cmp) (cert : CoprimeCert (n + 1) R cmp) : Bool :=
  Cert.succCheck lower checkRatLeaf f h cert

@[reducible] def checkOps {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] : (n : Nat) → CheckOpsAt R n
  | 0 =>
      { coprime := fun cmp _ => baseCheckCoprime (cmp := cmp)
        gcd := fun cmp _ => checkGcdUsing (baseCheckCoprime (cmp := cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (baseCheckCoprime (cmp := cmp))) }
  | n + 1 =>
      let lower := checkOps n
      { coprime := fun cmp _ => succCheckCoprime lower (cmp := cmp)
        gcd := fun cmp _ => checkGcdUsing (succCheckCoprime lower (cmp := cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (succCheckCoprime lower (cmp := cmp))) }

/-- Replay recursive coprimality evidence. -/
@[reducible] def checkCoprime {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h : MvPoly n R cmp) (cert : CoprimeCert n R cmp) : Bool :=
  (checkOps (R := R) n).coprime cmp f h cert

/-- Replay a gcd candidate and its coprimality evidence. -/
@[reducible] def checkGcd {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h : MvPoly n R cmp) (cert : GcdCert n R cmp) : Bool :=
  (checkOps (R := R) n).gcd cmp f h cert

/-- Replay a coefficient gcd fold, starting from zero and requiring exactly
one checked gcd step per coefficient. -/
@[reducible] def checkContent {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (coeffs : List (MvPoly n R cmp)) (cert : ContentCert n R cmp) : Bool :=
  (checkOps (R := R) n).content cmp coeffs cert

/-- The semantic property witnessed by a coprimality certificate. -/
def CoprimeCofactors {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (f h : MvPoly n R cmp) : Prop :=
  ∀ d, d ∣ f → d ∣ h → ∃ u, d * u = 1

/-- The standalone rational-lift replay transports integer-model
coprimality. -/
theorem checkRatLift_sound {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    {f h : MvPoly n Rat cmp} {lift : RatLiftCert n cmp}
    (hc : checkRatLift f h lift = true) : CoprimeCofactors f h := by
  sorry

/-- Direct semantic payload of a checked gcd certificate. -/
def CheckedGcdResult {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h g cofL cofR : MvPoly n R cmp) : Prop :=
  f = g * cofL ∧ h = g * cofR ∧ polyNormalize g = g ∧
    CoprimeCofactors cofL cofR

/-- A checked result plus greatest-common-divisor maximality. -/
def IsGcdCertResult {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h g cofL cofR : MvPoly n R cmp) : Prop :=
  CheckedGcdResult f h g cofL cofR ∧
    ∀ d, d ∣ f → d ∣ h → d ∣ g

/-- Simultaneous checker soundness: recursive coprimality replay. -/
theorem checkCoprime_sound {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} {cert : CoprimeCert n R cmp}
    (hc : checkCoprime f h cert = true) : CoprimeCofactors f h := by
  sorry

/-- Simultaneous checker soundness: a content fold is both a common divisor
and greatest among common divisors. -/
theorem checkContent_sound {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {coeffs : List (MvPoly n R cmp)} {cert : ContentCert n R cmp}
    (hc : checkContent coeffs cert = true) :
    (∀ q ∈ coeffs, cert.value ∣ q) ∧
      ∀ d, (∀ q ∈ coeffs, d ∣ q) → d ∣ cert.value := by
  sorry

/-- Simultaneous checker soundness: exact cofactors, normalization, and
coprimality. -/
theorem checkGcd_sound {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    {f h : MvPoly n R cmp} {cert : GcdCert n R cmp}
    (hc : checkGcd f h cert = true) :
    CheckedGcdResult f h cert.gcd cert.cofL cert.cofR := by
  cases n with
  | zero =>
      simp only [checkGcd, checkGcdUsing, Bool.and_eq_true,
        beq_iff_eq] at hc
      exact ⟨hc.1.1.1.symm, hc.1.1.2.symm, hc.1.2,
        checkCoprime_sound hc.2⟩
  | succ n =>
      simp only [checkGcd, checkGcdUsing, Bool.and_eq_true,
        beq_iff_eq] at hc
      exact ⟨hc.1.1.1.symm, hc.1.1.2.symm, hc.1.2,
        checkCoprime_sound hc.2⟩

/-- Separate gcd-domain cancellation turns checked coprime cofactors into
maximality. -/
theorem CheckedGcdResult.greatest {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    [CoprimeCancelLaws (MvPoly n R cmp)]
    {f h g cofL cofR : MvPoly n R cmp}
    (hc : CheckedGcdResult f h g cofL cofR) :
    ∀ d, d ∣ f → d ∣ h → d ∣ g := by
  intro d hdf hdh
  rcases hc with ⟨hf, hh, _, hcop⟩
  rw [hf] at hdf
  rw [hh] at hdh
  exact CoprimeCancelLaws.cancel_coprime g cofL cofR d hcop hdf hdh

/-- Full semantic payload of an accepted certificate. -/
theorem checkGcd_greatest {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]
    [CoprimeCancelLaws (MvPoly n R cmp)]
    {f h : MvPoly n R cmp} {cert : GcdCert n R cmp}
    (hc : checkGcd f h cert = true) :
    IsGcdCertResult f h cert.gcd cert.cofL cert.cofR := by
  exact ⟨checkGcd_sound hc, (checkGcd_sound hc).greatest⟩

end Hex.MvPoly
