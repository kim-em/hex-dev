/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Modulus
public import HexMvGcd.Instances
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

universe u

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

/-- Computational core of `imageAt`, separated from the law-bearing
`CoeffHom` so dependent certificate elimination does not have to identify
the constructor's stored operation dictionaries with the checker's ones. -/
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

/-- A law-bearing coefficient embedding used by the internal
universe-polymorphic form of rational lifting.  The public smart constructor
fixes this to the canonical embedding from `Int` into `Rat`. -/
structure CoeffEmbedding (S R : Type u)
    where
  toFun : S → R

mutual
  /-- Recursive evidence that two multivariate polynomials have no common
  nonunit divisor.  The result sort is `Type (u + 1)`: because the
  coefficient type `R : Type u` is itself an index, Lean's universe checker
  rejects `Type u` before considering any constructor fields. -/
  inductive CoprimeCert :
      (n : Nat) → (R : Type u) → [Zero R] →
      (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (u + 1)
    | unit {n : Nat} {R : Type u} [Zero R]
        {cmp : Mono n → Mono n → Ordering}
        [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
        CoprimeCert n R cmp
    | base {R : Type u} [Zero R]
        {cmp : Mono 0 → Mono 0 → Ordering}
        [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (u v : R) : CoprimeCert 0 R cmp
    /-- Internal universe-polymorphic form of rational lifting.  The public
    `CoprimeCert.ratLift` smart constructor fixes the embedded coefficient
    type to `Int` and the target type to `Rat`. -/
    | ratLiftCore {n : Nat} {R S : Type u}
        [zeroR : Zero R] [One R] [Add R] [Mul R]
        [Lean.Grind.CommRing S]
        [DecidableEq S] [BEq S] [LawfulBEq S] [Dvd S] [GcdOps S]
        {cmp : Mono n → Mono n → Ordering}
        [outerTrans : Std.TransCmp cmp] [outerEq : Std.LawfulEqCmp cmp]
        (embed : CoeffEmbedding S R)
        (mapZero : embed.toFun 0 = 0)
        (mapOne : embed.toFun 1 = 1)
        (mapAdd : ∀ a b, embed.toFun (a + b) =
          embed.toFun a + embed.toFun b)
        (mapMul : ∀ a b, embed.toFun (a * b) =
          embed.toFun a * embed.toFun b)
        (injective : ∀ {a b}, embed.toFun a = embed.toFun b → a = b)
        /- The two replayed scale factors and explicit inverse candidates.
        The checker validates both inverse equations; this keeps the
        universe-polymorphic core sound even though its target is not fixed
        to the rational field. -/
        (scaleL scaleR invL invR : R)
        (left right : MvPoly n S cmp)
        (cert : CoprimeCert n S cmp) :
        @CoprimeCert n R zeroR cmp outerTrans outerEq
    | split {n : Nat} {R : Type u} [zeroR : Zero R]
        [One R] [Add R] [Mul R]
        {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
        [outerTrans : Std.TransCmp cmp] [outerEq : Std.LawfulEqCmp cmp]
        (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
        [order : IsMonomialOrder cmp']
        (P : ZMod64.Prime)
        (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
        (a : Fin n → @ZMod64 P.m P.bounds)
        (α β : @FpPoly P.m P.bounds)
        (left right : @ContentCert n R zeroR cmp'
          order.toTransCmp order.toLawfulEqCmp)
        (rest : @CoprimeCert n R zeroR cmp'
          order.toTransCmp order.toLawfulEqCmp) :
        @CoprimeCert (n + 1) R zeroR cmp outerTrans outerEq
    | splitBezout {n : Nat} {R : Type u}
        [zeroR : Zero R] [One R] [Add R] [Mul R]
        {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
        [outerTrans : Std.TransCmp cmp] [outerEq : Std.LawfulEqCmp cmp]
        (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
        [order : IsMonomialOrder cmp']
        (u v : @MvPoly (n + 1) R zeroR cmp outerTrans outerEq)
        (r : @MvPoly n R zeroR cmp' order.toTransCmp order.toLawfulEqCmp)
        (left right : @ContentCert n R zeroR cmp'
          order.toTransCmp order.toLawfulEqCmp)
        (rest : @CoprimeCert n R zeroR cmp'
          order.toTransCmp order.toLawfulEqCmp) :
        @CoprimeCert (n + 1) R zeroR cmp outerTrans outerEq
  /-- A gcd candidate, exact cofactors, and recursive coprimality evidence. -/
  inductive GcdCert :
      (n : Nat) → (R : Type u) → [Zero R] →
      (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (u + 1)
    | mk {n : Nat} {R : Type u} [Zero R]
        {cmp : Mono n → Mono n → Ordering}
        [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (gcd cofL cofR : MvPoly n R cmp)
        (coprime : CoprimeCert n R cmp) : GcdCert n R cmp

  /-- A checked left fold of gcd over a coefficient list. -/
  inductive ContentCert :
      (n : Nat) → (R : Type u) → [Zero R] →
      (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (u + 1)
    | mk {n : Nat} {R : Type u} [Zero R]
        {cmp : Mono n → Mono n → Ordering}
        [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (value : MvPoly n R cmp)
        (steps : GcdCerts n R cmp) : ContentCert n R cmp

  /-- Strictly-positive list used inside the mutual certificate block.
  `List (GcdCert ...)` is a nested inductive occurrence, which Lean rejects
  when the certificate indices contain local comparator instances. -/
  inductive GcdCerts :
      (n : Nat) → (R : Type u) → [Zero R] →
      (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type (u + 1)
    | nil {n : Nat} {R : Type u} [Zero R]
        {cmp : Mono n → Mono n → Ordering}
        [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : GcdCerts n R cmp
    | cons {n : Nat} {R : Type u} [Zero R]
        {cmp : Mono n → Mono n → Ordering}
        [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
        (head : GcdCert n R cmp) (tail : GcdCerts n R cmp) :
        GcdCerts n R cmp
end

namespace CoprimeCert

def intEmbeddingRat : CoeffEmbedding Int Rat where
  toFun := fun z => (z : Rat)

/-- Rational coprimality transported from primitive integer models.  This is
the public, index-specialized constructor; the law-bearing generic embedding
is an implementation detail needed to preserve universe polymorphism. -/
def ratLift {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (scaleL scaleR : Rat) (left right : MvPoly n Int cmp)
    (cert : CoprimeCert n Int cmp) : CoprimeCert n Rat cmp :=
  .ratLiftCore intEmbeddingRat (by rfl) (by rfl)
    (by intro a b; exact Rat.intCast_add a b)
    (by intro a b; exact Rat.intCast_mul a b)
    (by intro a b h; exact Rat.intCast_inj.mp h)
    scaleL scaleR scaleL⁻¹ scaleR⁻¹ left right cert

end CoprimeCert

/-- Flat rational-lift data retained as a convenient standalone replay view.
The checked certificate sum itself exposes `CoprimeCert.ratLift`; new
producers use that constructor. -/
structure RatLiftCert (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  scaleL : Rat
  scaleR : Rat
  left : MvPoly n Int cmp
  right : MvPoly n Int cmp
  cert : CoprimeCert n Int cmp

namespace GcdCerts

variable {n : Nat} {R : Type u} [Zero R]
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

@[reducible] def toList : GcdCerts n R cmp → List (GcdCert n R cmp)
  | .nil => []
  | .cons head tail => head :: toList tail

@[reducible] def ofList : List (GcdCert n R cmp) → GcdCerts n R cmp
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

end GcdCerts

namespace GcdCert

variable {n : Nat} {R : Type u} [Zero R]
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

@[reducible] def gcd : GcdCert n R cmp → MvPoly n R cmp
  | .mk gcd _ _ _ => gcd

@[reducible] def cofL : GcdCert n R cmp → MvPoly n R cmp
  | .mk _ cofL _ _ => cofL

@[reducible] def cofR : GcdCert n R cmp → MvPoly n R cmp
  | .mk _ _ cofR _ => cofR

@[reducible] def coprime : GcdCert n R cmp → CoprimeCert n R cmp
  | .mk _ _ _ coprime => coprime

end GcdCert

namespace ContentCert

variable {n : Nat} {R : Type u} [Zero R]
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

@[reducible] def value : ContentCert n R cmp → MvPoly n R cmp
  | .mk value _ => value

@[reducible] def steps : ContentCert n R cmp → List (GcdCert n R cmp)
  | .mk _ steps => steps.toList

/-- Public list-based constructor; the strictly-positive internal list is an
implementation detail of Lean's mutual-inductive positivity checker. -/
@[reducible] def ofSteps (value : MvPoly n R cmp) (steps : List (GcdCert n R cmp)) :
    ContentCert n R cmp :=
  .mk value (GcdCerts.ofList steps)

@[simp] theorem value_ofSteps (value : MvPoly n R cmp)
    (steps : List (GcdCert n R cmp)) :
    (ofSteps value steps).value = value := by
  rfl

@[simp] theorem steps_ofSteps (value : MvPoly n R cmp)
    (steps : List (GcdCert n R cmp)) :
    (ofSteps value steps).steps = steps := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      simp only [ContentCert.steps, GcdCerts.toList, ih]

end ContentCert

/-- Coefficientwise cast from the integer model used by `ratLift`. -/
def intModelToRat {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : MvPoly n Rat cmp :=
  mapCoeffs (fun z : Int => (z : Rat)) p

/-- The three replay operations at one arity.  Packaging them by arity avoids
Lean's well-founded mutual-recursion compiler: recursive certificate calls
always move to the already-built lower-arity package, while content folds are
ordinary structural recursion on their two lists. -/
structure CheckOpsAt (R : Type u) [Zero R] (n : Nat) : Type (u + 1) where
  coprime : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → CoprimeCert n R cmp → Bool
  gcd : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp → Bool
  content : (cmp : Mono n → Mono n → Ordering) → [IsMonomialOrder cmp] →
    List (MvPoly n R cmp) → ContentCert n R cmp → Bool

@[reducible] def checkGcdUsing {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (coprime : MvPoly n R cmp → MvPoly n R cmp →
      CoprimeCert n R cmp → Bool)
    (f h : MvPoly n R cmp) (cert : GcdCert n R cmp) : Bool :=
  (cert.gcd * cert.cofL == f) &&
    (cert.gcd * cert.cofR == h) &&
    (polyNormalize cert.gcd == cert.gcd) &&
    coprime cert.cofL cert.cofR cert.coprime

/-! `checkContentSteps` exposes the accumulator used by content replay.  The
public checker fixes that accumulator to zero; keeping the general recursion
named lets producer proofs state the natural induction invariant. -/

@[reducible] def checkContentSteps {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (gcd : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp → Bool)
    (value acc : MvPoly n R cmp) :
    List (MvPoly n R cmp) → List (GcdCert n R cmp) → Bool
  | [], [] => acc == value
  | q :: qs, step :: steps =>
      gcd acc q step && checkContentSteps gcd value step.gcd qs steps
  | _, _ => false

@[reducible] def checkContentUsing {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (gcd : MvPoly n R cmp → MvPoly n R cmp → GcdCert n R cmp → Bool)
    (coeffs : List (MvPoly n R cmp)) (cert : ContentCert n R cmp) : Bool :=
  checkContentSteps gcd cert.value 0 coeffs cert.steps

/-! The rational-lift branch contains an embedded coefficient certificate at
the same arity.  Its replay therefore uses this independent structural
package, which rejects nested lifts, instead of recursing through the main
coefficient-polymorphic package.  This keeps both definitions structurally
recursive. -/

@[reducible] def baseCheckNoLift {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    {cmp : Mono 0 → Mono 0 → Ordering}
    [IsMonomialOrder cmp]
    (f h : MvPoly 0 S cmp) (cert : CoprimeCert 0 S cmp) : Bool :=
  match cert with
  | .unit => polyIsUnit f || polyIsUnit h
  | .base u v => u * coeff Mono.zero f + v * coeff Mono.zero h == 1
  | _ => false

@[reducible] def succCheckNoLift {n : Nat} {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    (lower : CheckOpsAt S n)
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) S cmp)
    (cert : CoprimeCert (n + 1) S cmp) : Bool := by
  cases cert with
  | unit => exact polyIsUnit f || polyIsUnit h
  | ratLiftCore => exact false
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

@[reducible] def noLiftOps {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S] : (n : Nat) → CheckOpsAt S n
  | 0 =>
      { coprime := fun cmp _ => baseCheckNoLift (cmp := cmp)
        gcd := fun cmp _ => checkGcdUsing (baseCheckNoLift (cmp := cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (baseCheckNoLift (cmp := cmp))) }
  | n + 1 =>
      let lower := noLiftOps n
      { coprime := fun cmp _ => succCheckNoLift lower (cmp := cmp)
        gcd := fun cmp _ => checkGcdUsing (succCheckNoLift lower (cmp := cmp))
        content := fun cmp _ => checkContentUsing
          (checkGcdUsing (succCheckNoLift lower (cmp := cmp))) }

/-- Replay the payload of the equality-packed rational-lift constructor. -/
@[reducible] def checkRatLiftCoreUsing {n : Nat} {R S : Type u}
    [zeroR : Zero R]
    [Lean.Grind.CommRing S] [DecidableEq S] [BEq S] [LawfulBEq S]
    [Dvd S] [GcdOps S]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h : MvPoly n R cmp) (embed : CoeffEmbedding S R)
    (scaleL scaleR invL invR : R) (left right : MvPoly n S cmp)
    (cert : CoprimeCert n S cmp) : Bool :=
  decide (scaleL ≠ 0) && decide (scaleR ≠ 0) &&
    (scaleL * invL == 1) && (scaleR * invR == 1) &&
    (f == C scaleL * mapCoeffs embed.toFun left) &&
    (h == C scaleR * mapCoeffs embed.toFun right) &&
    decide (scalarContent left = 1) &&
    decide (scalarContent right = 1) &&
    (noLiftOps n).coprime cmp left right cert

@[reducible] def baseCheckCoprime {R : Type u}
    {cmp : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R] [IsMonomialOrder cmp]
    (f h : MvPoly 0 R cmp) (cert : CoprimeCert 0 R cmp) : Bool :=
  match cert with
  | .unit => polyIsUnit f || polyIsUnit h
  | .base u v => u * coeff Mono.zero f + v * coeff Mono.zero h == 1
  | @CoprimeCert.ratLiftCore _ _ S _ _ _ _ _ringModel _decModel
      _beqModel _lawfulModel _dvdModel _gcdModel _ _ _ embed _ _ _ _ _
      scaleL scaleR invL invR left right cert =>
      checkRatLiftCoreUsing (S := S) f h embed scaleL scaleR invL invR
        left right cert

@[reducible] def succCheckCoprime {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    (lower : CheckOpsAt R n)
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    (f h : MvPoly (n + 1) R cmp)
    (cert : CoprimeCert (n + 1) R cmp) : Bool := by
  cases cert with
  | unit => exact polyIsUnit f || polyIsUnit h
  | @ratLiftCore _ _ S _ _ _ _ ringModel decModel beqModel
      lawfulModel dvdModel gcdModel _ _ _ embed _ _ _ _ _
      scaleL scaleR invL invR left right cert =>
      exact checkRatLiftCoreUsing (S := S) f h embed
        scaleL scaleR invL invR left right cert
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

/-- Replay rational scaling and primitive integer-model coprimality. -/
@[reducible] def checkRatLift {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    (f h : MvPoly n Rat cmp) (lift : RatLiftCert n cmp) : Bool :=
  decide (lift.scaleL ≠ 0) && decide (lift.scaleR ≠ 0) &&
    (f == C lift.scaleL * intModelToRat lift.left) &&
    (h == C lift.scaleR * intModelToRat lift.right) &&
    decide (scalarContent lift.left = 1) &&
    decide (scalarContent lift.right = 1) &&
    checkCoprime lift.left lift.right lift.cert

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
  sorry

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
