/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBasic.Rand
public import HexBasic.Rand
public import HexMvGcd.Prs

@[expose] public section

/-! Checked proposal plumbing and routes 0--1. -/

namespace Hex.MvPoly

universe u

structure GcdConfig where
  rand : Rand
  heuristicBitBudget : Nat
  brownPrimeFuel : Nat
  brownPointFuel : Nat

def GcdConfig.default : GcdConfig where
  rand := Rand.ofSeed 0
  heuristicBitBudget := 1048576
  brownPrimeFuel := 64
  brownPointFuel := 4096

/-- The genuinely small-prime-first prefix below a fixed bounded window.
The whole window is enumerated before reversing; asking the downward scanner
for only `fuel` entries would instead select the largest primes in it. -/
def smallPrimeSupply (bound fuel : Nat) : List ZMod64.Prime :=
  (ZMod64.primesBelow bound bound).toList.reverse.take fuel

/-- State carried by a failed bounded draw.  `zeroBound` consumes nothing;
rejection exhaustion reports the already-advanced state. -/
def randErrorState (initial : Rand) : RandError → Rand
  | .zeroBound => initial
  | .exhausted _ advanced => advanced

/-- Draw one separately sampled field element for each coordinate.  Every
coordinate performs its own bounded rejection-sampling call and the returned
state is threaded into the next draw. -/
def samplePoints {p : Nat} [ZMod64.Bounds p] (sampleFuel : Nat) :
    (n : Nat) → Rand → Except RandError ((Fin n → ZMod64 p) × Rand)
  | 0, rand => .ok (Fin.elim0, rand)
  | n + 1, rand => do
      let (value, rand') ← rand.nat p sampleFuel
      let (rest, rand'') ← samplePoints sampleFuel n rand'
      .ok (Fin.cases (ZMod64.ofNat p value) rest, rand'')

structure GcdRun (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  cert : GcdCert n R cmp
  rand : Rand

/-- Untrusted fast-backend output. -/
structure GcdProposal (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  cert? : Option (GcdCert n R cmp)
  rand : Rand

/-- Coefficient-specific routes after the public dispatcher has removed the
mandatory route-0 factor.  Implementations must treat their two polynomial
arguments as the already-reduced problem and must not repeat structural
reduction. -/
class GcdProducer (R : Type u) [Zero R] where
  propose : {n : Nat} → (cmp : Mono n → Mono n → Ordering) →
    [IsMonomialOrder cmp] → GcdConfig →
    MvPoly n R cmp → MvPoly n R cmp → GcdProposal n R cmp

/-- Abstract rings have no coefficient-specific speculative route. -/
@[instance_reducible] def noFastProducer {R : Type u} [Zero R] : GcdProducer R where
  propose := fun _ _ cfg _ _ => ⟨none, cfg.rand⟩

instance (priority := 10) instNoFastProducer {R : Type u} [Zero R] :
    GcdProducer R := noFastProducer

/-- Route 0: zero and unit cases, all represented by genuine replayable
certificates. -/
def structuralCert? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (f h : MvPoly n R cmp) : Option (GcdCert n R cmp) :=
  if f == 0 && h == 0 then some (.mk 0 1 1 .unit)
  else if f == 0 then
    let g := polyNormalize h
    some (.mk g 0 (quotient h g) .unit)
  else if h == 0 then
    let g := polyNormalize f
    some (.mk g (quotient f g) 0 .unit)
  else if polyIsUnit f || polyIsUnit h then
    some (.mk 1 f h .unit)
  else none

/-- The common monomial/coefficient factor removed before every nondegenerate
route, together with the two exact reduced inputs. -/
structure StructuralReduction (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  factor : MvPoly n R cmp
  left : MvPoly n R cmp
  right : MvPoly n R cmp

/-- Route 0's linear common-monomial and scalar-content reduction.  Exact
division is matched explicitly, so an invariant failure declines rather than
manufacturing a reduced input. -/
def structuralReduction? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    (f h : MvPoly n R cmp) : Option (StructuralReduction n R cmp) := do
  let commonMono := Mono.gcd (monoContent f) (monoContent h)
  let commonCoeff := GcdOps.gcd (content f) (content h)
  let factor := monomial commonMono commonCoeff
  let left ← divExact? f factor
  let right ← divExact? h factor
  some ⟨factor, left, right⟩

/-- Re-embed a certificate for structurally reduced inputs.  The common
factor and the reduced gcd are both normalized, and the final checker is the
only acceptance gate for the reassociated product identities. -/
def restoreStructural? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    (f h : MvPoly n R cmp) (reduced : StructuralReduction n R cmp)
    (cert : GcdCert n R cmp) : Option (GcdCert n R cmp) :=
  let restored := GcdCert.mk (reduced.factor * cert.gcd)
    cert.cofL cert.cofR cert.coprime
  if checkGcd f h restored then some restored else none

/-- Complete checked dispatch. Route 0 is computed once before coefficient
dispatch. Proposals affect performance and random state, but rejection always
falls through to route 4 on the reduced problem and is reconstructed through
the same checker gate.  This plumbing lives below the concrete producers so
one coefficient backend can invoke another without creating an import cycle. -/
def gcdCertWith (cfg : GcdConfig)
    {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    [GcdProducer R]
    (f h : MvPoly n R cmp) : GcdRun n R cmp :=
  match structuralCert? f h with
  | some cert =>
      if checkGcd f h cert then ⟨cert, cfg.rand⟩
      else ⟨prsCert f h, cfg.rand⟩
  | none =>
      match structuralReduction? f h with
      | none => ⟨prsCert f h, cfg.rand⟩
      | some reduced =>
          -- The unreduced PRS arm is a fail-closed response to a violated
          -- reduction/restoration invariant, not an ordinary fallback route.
          let fallback (rand : Rand) : GcdRun n R cmp :=
            let cert := prsCert reduced.left reduced.right
            match restoreStructural? f h reduced cert with
            | some restored => ⟨restored, rand⟩
            | none => ⟨prsCert f h, rand⟩
          let proposal := GcdProducer.propose cmp cfg reduced.left reduced.right
          match proposal.cert? with
          | some candidate =>
              if checkGcd reduced.left reduced.right candidate then
                match restoreStructural? f h reduced candidate with
                | some restored => ⟨restored, proposal.rand⟩
                | none => fallback proposal.rand
              else
                fallback proposal.rand
          | none => fallback proposal.rand

/-- Direct coprimality witness when two cofactors differ by one. -/
def unitDiffCert? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (f h : MvPoly n R cmp) : Option (CoprimeCert n R cmp) :=
  if f - h == 1 then some (.bezout 1 (-1))
  else if h - f == 1 then some (.bezout (-1) 1)
  else none

/-- Detect a one-step polynomial remainder equal to `±1` and replay the
resulting direct Bézout identity.  This keeps candidate checking cheap when a
large cofactor is an affine polynomial multiple of the other. -/
def unitRemainderCert? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [GcdOps R]
    (f h : MvPoly n R cmp) : Option (CoprimeCert n R cmp) :=
  let right := divMod h f
  if right.2 == 1 then some (.bezout (-right.1) 1)
  else if right.2 == -1 then some (.bezout right.1 (-1))
  else
    let left := divMod f h
    if left.2 == 1 then some (.bezout 1 (-left.1))
    else if left.2 == -1 then some (.bezout (-1) left.1)
    else none

/-- Offer an arbitrary nonzero polynomial candidate to the full multivariate
checker.  Exact division builds cofactors; a unit difference or unit remainder
gives a direct Bézout witness, and all other pairs use route 4.  No producer
may bypass this function's final replay. -/
def checkedCandidate? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (f h candidate : MvPoly n R cmp) : Option (GcdCert n R cmp) :=
  if candidate == 0 then none
  else
    let normalized := polyNormalize candidate
    let cofL := quotient f normalized
    let cofR := quotient h normalized
    let coprime := match unitDiffCert? cofL cofR with
      | some cert => cert
      | none => match unitRemainderCert? cofL cofR with
        | some cert => cert
        | none => (prsCert cofL cofR).coprime
    let cert := GcdCert.mk normalized cofL cofR coprime
    if checkGcd f h cert then some cert else none

/-! # Integer modular coprimality -/

/-- Canonical reduction homomorphism carried in an image certificate. -/
def intCoeffHom (prime : ZMod64.Prime) :
    @CoeffHom Int prime.m _ _ _ _ prime.bounds := by
  letI : ZMod64.Bounds prime.m := prime.bounds
  exact
    { toField := ZMod64.intCast prime.m
      map_zero := by exact Lean.Grind.Ring.intCast_zero
      map_one := by exact Lean.Grind.Ring.intCast_one
      map_add := by intro a b; exact Lean.Grind.Ring.intCast_add a b
      map_mul := by intro a b; exact Lean.Grind.Ring.intCast_mul a b }

/-- A one-prime coprimality attempt at fixed arity, returning the advanced
random state even when the image is inconclusive.  The coefficient
homomorphism is explicit certificate data, so the same recursion serves
integers and polynomial coefficients evaluated into their ground field. -/
structure CoprimeOpsAt (R : Type u) [Zero R] [One R] [Add R] [Mul R]
    (n : Nat) where
  tryAt : (cmp : Mono n → Mono n → Ordering) →
    [IsMonomialOrder cmp] → (P : ZMod64.Prime) →
    @CoeffHom R P.m _ _ _ _ P.bounds → Rand →
    MvPoly n R cmp → MvPoly n R cmp →
    Option (CoprimeCert n R cmp) × Rand

/-- Arity-zero modular-coprimality leaf. -/
def coprimeBase {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] : CoprimeOpsAt R 0 where
  tryAt := fun cmp _ _ _ rand f h =>
    let cert := baseCoprime cmp f h
    (if checkCoprime f h cert then some cert else none, rand)

/-- One recursive modular image and coefficient-content descent. -/
def coprimeStep {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (lower : CoprimeOpsAt R n) : CoprimeOpsAt R (n + 1) where
  tryAt := fun cmp _ prime φ rand f h =>
    letI : ZMod64.Bounds prime.m := prime.bounds
    letI : ZMod64.PrimeModulus prime.m :=
      ZMod64.primeModulusOfPrime prime.prime
    match samplePoints 8 n rand with
    | .error error => (none, randErrorState rand error)
    | .ok (points, rand') =>
      let main : Fin (n + 1) := ⟨0, by omega⟩
      let fView := toUnivariate main Mono.lex f
      let hView := toUnivariate main Mono.lex h
      let fImage := imageAtRaw prime φ.toField points main Mono.lex f
      let hImage := imageAtRaw prime φ.toField points main Mono.lex h
      if fImage.degree? != fView.degree? || hImage.degree? != hView.degree? then
        (none, rand')
      else
        let xg := DensePoly.xgcd fImage hImage
        if xg.gcd.size != 1 then
          (none, rand')
        else
          let scalar := xg.gcd.coeff 0
          if scalar == 0 then
            (none, rand')
          else
            let alpha := DensePoly.scaleImpl scalar⁻¹ xg.left
            let beta := DensePoly.scaleImpl scalar⁻¹ xg.right
            let left := contentCertWith (fun a b => prsCert a b)
              fView.toArray.toList
            let right := contentCertWith (fun a b => prsCert a b)
              hView.toArray.toList
            let restRun := lower.tryAt Mono.lex prime φ rand'
              left.value right.value
            match restRun.1 with
            | none => (none, restRun.2)
            | some rest =>
                let cert := CoprimeCert.split main Mono.lex prime φ points
                  alpha beta left right rest
                (if checkCoprime f h cert then some cert else none, restRun.2)

/-- Construct the per-variable modular coprimality route. -/
def coprimeOps {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] :
    (n : Nat) → CoprimeOpsAt R n
  | 0 => coprimeBase
  | n + 1 => coprimeStep (coprimeOps n)

/-- Route 1 at one selected prime and coefficient homomorphism.  A failed
image is inconclusive, while a returned gcd certificate has passed the full
recursive checker. -/
def tryCoprimeCert? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (P : ZMod64.Prime) (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
    (rand : Rand) (f h : MvPoly n R cmp) :
    Option (GcdCert n R cmp) × Rand :=
  let run := (coprimeOps (R := R) n).tryAt cmp P φ rand f h
  match run.1 with
  | none => (none, run.2)
  | some coprime =>
      let cert := GcdCert.mk 1 f h coprime
      (if checkGcd f h cert then some cert else none, run.2)

/-- Search a finite prime supply, threading fresh points through every failed
attempt. -/
def intCoprimeLoop {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly n Int cmp) :
    List ZMod64.Prime → Nat → Rand →
      Option (GcdCert n Int cmp) × Rand
  | _, 0, rand => (none, rand)
  | [], _, rand => (none, rand)
  | prime :: primes, fuel + 1, rand =>
      let run := tryCoprimeCert? prime (intCoeffHom prime) rand f h
      match run.1 with
      | some cert => (some cert, run.2)
      | none => intCoprimeLoop f h primes fuel run.2

/-- Route 1 over integers: one image gcd per variable, with all image degree,
Bezout, content, and recursive certificates replayed by `checkGcd`. -/
def intTryCoprimeCert? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (primeFuel : Nat) (rand : Rand) (f h : MvPoly n Int cmp) :
    Option (GcdCert n Int cmp) × Rand :=
  let supply := smallPrimeSupply 47 primeFuel
  intCoprimeLoop f h supply primeFuel rand

/-- Integer route 1 on an already route-0-reduced problem. -/
def intFastProposal {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Int cmp) : GcdProposal n Int cmp :=
  let run := intTryCoprimeCert? cfg.brownPrimeFuel cfg.rand f h
  ⟨run.1, run.2⟩

/-! # Concrete finite-field coefficient homomorphisms -/

/-- Identity coefficient homomorphism for a polynomial already over the
selected bundled prime field. -/
def primeCoeffHom {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] :
    @CoeffHom (@ZMod64 p hp) p _ _ _ _ hp :=
  { toField := fun x => x
    map_zero := rfl
    map_one := rfl
    map_add := by intros; rfl
    map_mul := by intros; rfl }

/-- Evaluation of a univariate prime-field polynomial at a chosen field
point, packaged with the homomorphism laws required by `CoprimeCert.split`. -/
def fpCoeffHom {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] (point : @ZMod64 p hp) :
    @CoeffHom (@FpPoly p hp) p _ _ _ _ hp :=
  { toField := fun f => DensePoly.evalImpl f point
    map_zero := by
      simpa only [← DensePoly.eval_eq_evalImpl] using FpPoly.eval_zero point
    map_one := by
      simpa only [← DensePoly.eval_eq_evalImpl] using FpPoly.eval_one point
    map_add := by
      intro f h
      simpa only [← DensePoly.eval_eq_evalImpl] using FpPoly.eval_add f h point
    map_mul := by
      intro f h
      simpa only [← DensePoly.eval_eq_evalImpl] using FpPoly.eval_mul f h point }

/-- Route 1 over a fixed bounded prime field on an already route-0-reduced
problem. -/
def primeFastProposal {n p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p]
    (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n (@ZMod64 p hp) cmp) :
    GcdProposal n (@ZMod64 p hp) cmp :=
  let P : ZMod64.Prime :=
    { m := p, bounds := hp, prime := ZMod64.PrimeModulus.prime }
  let run := tryCoprimeCert? P primeCoeffHom cfg.rand f h
  ⟨run.1, run.2⟩

/-- Route 1 for `FpPoly` coefficients on an already route-0-reduced problem.
One random field point defines the total evaluation homomorphism carried by
the certificate; subsequent draws are used for the multivariate image
points. -/
def fpFastProposal {n p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p]
    (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n (@FpPoly p hp) cmp) :
    GcdProposal n (@FpPoly p hp) cmp :=
  let P : ZMod64.Prime :=
    { m := p, bounds := hp, prime := ZMod64.PrimeModulus.prime }
  match cfg.rand.nat p 8 with
  | .error error => ⟨none, randErrorState cfg.rand error⟩
  | .ok (value, rand') =>
      let point := ZMod64.ofNat p value
      let run := tryCoprimeCert? P (fpCoeffHom point) rand' f h
      ⟨run.1, run.2⟩

/-! Sampling pins: a non-power-of-two modulus gets one bounded draw per
coordinate, with deterministic values and exactly the corresponding advanced
state. -/

#guard
  letI : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
  match samplePoints (p := 5) 8 3 (Rand.ofSeed 17) with
  | .error _ => false
  | .ok (points, rand) =>
      [points 0 |>.toNat, points 1 |>.toNat, points 2 |>.toNat] == [4, 3, 1] &&
        rand.state == (Rand.ofSeed 17).next.2.next.2.next.2.state

/-- Coefficient-generic post-structural proposal.  Route 1 needs an explicit
total `CoeffHom`, so an abstract coefficient backend has no candidate after
the public route-0 pass. -/
def fastProposal {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R]
    (cfg : GcdConfig) (_f _h : MvPoly n R cmp) : GcdProposal n R cmp :=
  ⟨none, cfg.rand⟩

end Hex.MvPoly
