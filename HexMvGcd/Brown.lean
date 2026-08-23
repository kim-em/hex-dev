/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular
public import HexMvGcd.Heu
public import HexPolyZGcd.Gcd

@[expose] public section

/-!
The state machines used by Brown's dense route.

The point layer and the prime layer deliberately expose their decisions.  A
bad image must not mutate reconstruction state, a larger image degree is
unlucky, and a smaller image degree discards all accumulated interpolation or
CRT data.  Keeping those decisions executable and separate from candidate
checking makes the three failure modes directly testable.
-/

namespace Hex.MvPoly

universe u

/-- Brown's response to one evaluation point. -/
inductive BrownPointAction where
  /-- An input leading coefficient or the correction scalar vanished. -/
  | bad
  /-- The image gcd degree was larger than the current minimum. -/
  | unlucky
  /-- A smaller degree invalidated all previously accumulated images. -/
  | restart
  /-- The image has the current minimal degree and may be interpolated. -/
  | accept
deriving BEq, DecidableEq, Repr

/-- Degree state for one dense interpolation layer. -/
structure BrownPointState where
  bestDegree? : Option Nat := none
  accepted : Nat := 0
deriving BEq, DecidableEq, Repr

/-- Classify one point before it can affect interpolation state. -/
def BrownPointState.offer (state : BrownPointState)
    (inputDegreesSurvive gammaNonzero : Bool) (imageDegree : Nat) :
    BrownPointAction × BrownPointState :=
  if !inputDegreesSurvive || !gammaNonzero then
    (.bad, state)
  else
    match state.bestDegree? with
    | none =>
        (.accept, { bestDegree? := some imageDegree, accepted := 1 })
    | some degree =>
        if imageDegree > degree then
          (.unlucky, state)
        else if imageDegree < degree then
          (.restart, { bestDegree? := some imageDegree, accepted := 1 })
        else
          (.accept, { state with accepted := state.accepted + 1 })

/-- Brown's response to one modular image. -/
inductive BrownPrimeAction where
  /-- Reduction destroyed an input degree or normalization datum. -/
  | bad
  /-- The modular gcd degree was larger than the running minimum. -/
  | unlucky
  /-- A smaller degree invalidated all previous CRT data. -/
  | restart
  /-- The image may be accumulated, but its support is not stable yet. -/
  | accumulate
  /-- The image degree and support agree with the preceding image. -/
  | stable
deriving BEq, DecidableEq, Repr

/-- Prime-layer state.  `support` is stored in canonical monomial order, so
plain list equality is the exact support-stability test required before CRT
reconstruction is trusted. -/
structure BrownPrimeState (n : Nat) where
  bestDegree? : Option Nat := none
  support : List (Mono n) := []
  stableRounds : Nat := 0
deriving BEq, DecidableEq, Repr

/-- Classify a modular image before it can mutate a CRT accumulator. -/
def BrownPrimeState.offer {n : Nat} (state : BrownPrimeState n)
    (inputDegreesSurvive normalizationNonzero : Bool)
    (imageDegree : Nat) (imageSupport : List (Mono n)) :
    BrownPrimeAction × BrownPrimeState n :=
  if !inputDegreesSurvive || !normalizationNonzero then
    (.bad, state)
  else
    match state.bestDegree? with
    | none =>
        (.accumulate,
          { bestDegree? := some imageDegree
            support := imageSupport
            stableRounds := 0 })
    | some degree =>
        if imageDegree > degree then
          (.unlucky, state)
        else if imageDegree < degree then
          (.restart,
            { bestDegree? := some imageDegree
              support := imageSupport
              stableRounds := 0 })
        else if imageSupport == state.support then
          (.stable, { state with stableRounds := state.stableRounds + 1 })
        else
          -- Equal degree with a different support starts a new stabilization
          -- epoch.  Existing CRT coordinates cannot be paired with it.
          (.restart,
            { bestDegree? := some imageDegree
              support := imageSupport
              stableRounds := 0 })

/-- Scale a nonzero univariate image gcd so that its leading coefficient is
the evaluated Brown correction `gamma`.  Returning `none` for either zero is
the zero-divisor/bad-point branch; callers must not interpolate that image. -/
def brownCorrectImage? {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Inv R]
    (gamma : R) (image : DensePoly R) : Option (DensePoly R) :=
  if gamma == 0 || image.isZero then
    none
  else
    let leading := image.leadingCoeff
    if leading == 0 then none
    else some (DensePoly.scaleImpl (gamma * leading⁻¹) image)

/-- The scalar Lagrange basis which is one at `point` and zero at every
member of `others`.  Duplicate points are rejected instead of relying on an
inverse of zero. -/
def brownBasis? {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Inv R]
    (point : R) (others : List R) : Option (DensePoly R) := do
  let (numerator, denominator) ← others.foldlM
    (fun (state : DensePoly R × R) other =>
      if point == other then none
      else some
        (state.1 * DensePoly.ofList [-other, 1],
          state.2 * (point - other)))
    (1, 1)
  if denominator == 0 then none
  else some (DensePoly.scaleImpl denominator⁻¹ numerator)

/-- Embed a scalar dense polynomial into a dense polynomial whose
coefficients are multivariate constants. -/
def brownLiftBasis {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (basis : DensePoly R) : DensePoly (MvPoly n R cmp) :=
  DensePoly.ofList <|
    (List.range basis.size).map fun degree => C (basis.coeff degree)

/-- Dense Lagrange interpolation of polynomial-valued samples.  The result
is a univariate polynomial in the evaluated variable whose coefficients are
polynomials in all remaining variables. -/
def brownInterpolate? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Inv R]
    (samples : List (R × MvPoly n R cmp)) :
    Option (DensePoly (MvPoly n R cmp)) :=
  let rec go (seen : List R) (remaining : List (R × MvPoly n R cmp))
      (result : DensePoly (MvPoly n R cmp)) :
      Option (DensePoly (MvPoly n R cmp)) := do
    match remaining with
    | [] => some result
    | (point, value) :: rest =>
        let others := seen.reverse ++ rest.map Prod.fst
        let basis ← brownBasis? point others
        let term := brownLiftBasis (n := n) (cmp := cmp) basis * DensePoly.C value
        go (point :: seen) rest (result + term)
  go [] samples 0

/-- Evaluate the last variable and remove it.  `Mono.lex` is used for the
remaining variables only as a storage order; reconstruction may target any
monomial order. -/
def brownEvalLast {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (point : R) (p : MvPoly (n + 1) R cmp) : MvPoly n R Mono.lex :=
  DensePoly.evalImpl (toUnivariate (Fin.last n) Mono.lex p) (C point)

/-- Leading coefficient when variable zero is the fixed Brown main
variable. -/
def brownMainLeadingCoeff {n : Nat} {R : Type u}
    {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (p : MvPoly (n + 1) R cmp) : MvPoly n R Mono.lex :=
  (toUnivariate 0 Mono.lex p).leadingCoeff

/-- Turn an untrusted Brown polynomial into a complete certificate.  Trial
division and a deterministic cofactor gcd build the witness, and the public
checker remains the only acceptance condition. -/
def brownCheckedCandidate? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    (f h candidate : MvPoly n R cmp) : Option (GcdCert n R cmp) :=
  checkedCandidate? f h candidate

/-! # Recursive point layer -/

/-- Candidate operation at a fixed arity over a field-like coefficient
kernel.  Inverses need not be trusted: every completed candidate is checked
by `brownCheckedCandidate?`. -/
structure BrownOpsAt (R : Type u) [Zero R] (n : Nat) : Type (u + 1) where
  candidate? : (cmp : Mono n → Mono n → Ordering) →
    [IsMonomialOrder cmp] → Nat → List R →
    MvPoly n R cmp → MvPoly n R cmp → Option (MvPoly n R cmp)

/-- Exact base image at arity zero. -/
def brownBaseOps {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] : BrownOpsAt R 0 where
  candidate? := fun _ _ _ _ f h => some (rawPrsCert f h).gcd

/-- Exact univariate image.  This is the leaf reached after evaluating all
outer variables and is intentionally the existing checked PRS kernel rather
than a second polynomial Euclidean implementation. -/
def brownUnaryOps {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] : BrownOpsAt R 1 where
  candidate? := fun _ _ _ _ f h => some (rawPrsCert f h).gcd

/-- Exact bad-point predicate used by the interpolation loop and by
route-level tests. -/
def brownPointBad {n : Nat} {R : Type u}
    {cmp : Mono (n + 2) → Mono (n + 2) → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (point : R) (gamma : MvPoly (n + 1) R Mono.lex)
    (f h : MvPoly (n + 2) R cmp) : Bool :=
  let fImage := brownEvalLast point f
  let hImage := brownEvalLast point h
  degreeOf (0 : Fin (n + 1)) fImage != degreeOf (0 : Fin (n + 2)) f ||
    degreeOf (0 : Fin (n + 1)) hImage != degreeOf (0 : Fin (n + 2)) h ||
    brownEvalLast point gamma == 0

/-- One recursive dense-interpolation layer.  Variable zero remains the main
variable; the last variable is evaluated and reconstructed. -/
def brownStepOps {n : Nat} {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Inv R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    (lower : BrownOpsAt R (n + 1)) : BrownOpsAt R (n + 2) where
  candidate? := fun cmp _ pointFuel points f h =>
    if f == 0 || h == 0 || polyIsUnit f || polyIsUnit h then
      some (rawPrsCert f h).gcd
    else
      let main : Fin (n + 2) := ⟨0, by omega⟩
      let outer : Fin (n + 2) := Fin.last (n + 1)
      let fView := toUnivariate main Mono.lex f
      let hView := toUnivariate main Mono.lex h
      let fContent := contentCertWith (fun a b => rawPrsCert a b)
        fView.toArray.toList
      let hContent := contentCertWith (fun a b => rawPrsCert a b)
        hView.toArray.toList
      let common := rawPrsCert fContent.value hContent.value
      let fPrimitive := quotient f (constIn main Mono.lex fContent.value)
      let hPrimitive := quotient h (constIn main Mono.lex hContent.value)
      let gamma :=
        (rawPrsCert (brownMainLeadingCoeff fPrimitive)
          (brownMainLeadingCoeff hPrimitive)).gcd
      let sampleTarget :=
        max (degreeOf outer fPrimitive) (degreeOf outer hPrimitive) + 1
      let rec loop (remaining : List R) (fuel : Nat)
          (state : BrownPointState)
          (samples : List (R × MvPoly (n + 1) R Mono.lex)) :
          Option (MvPoly (n + 2) R cmp) := do
        if fuel = 0 then none else pure PUnit.unit
        match remaining with
        | [] => none
        | point :: rest =>
            let fImage := brownEvalLast point fPrimitive
            let hImage := brownEvalLast point hPrimitive
            let gammaAt := brownEvalLast point gamma
            if brownPointBad point gamma fPrimitive hPrimitive then
              loop rest (fuel - 1) state samples
            else
              match lower.candidate? Mono.lex (fuel - 1) rest fImage hImage with
              | none => loop rest (fuel - 1) state samples
              | some rawImage =>
                  let imageLeading := brownMainLeadingCoeff rawImage
                  match divExact? gammaAt imageLeading with
                  | none => loop rest (fuel - 1) state samples
                  | some scale =>
                      let corrected := constIn (0 : Fin (n + 1)) Mono.lex scale * rawImage
                      if brownMainLeadingCoeff corrected != gammaAt then
                        loop rest (fuel - 1) state samples
                      else
                        let imageDegree := degreeOf (0 : Fin (n + 1)) corrected
                        let offered := state.offer true true imageDegree
                        match offered.1 with
                        | .bad | .unlucky =>
                            loop rest (fuel - 1) offered.2 samples
                        | .restart =>
                            if sampleTarget ≤ 1 then
                              let interpolation ← brownInterpolate? [(point, corrected)]
                              let reconstructed :=
                                ofUnivariate (cmp := cmp) outer Mono.lex interpolation
                              let reconstructedView := toUnivariate main Mono.lex reconstructed
                              let reconstructedContent := contentCertWith
                                (fun a b => rawPrsCert a b)
                                reconstructedView.toArray.toList
                              let primitive := quotient reconstructed
                                (constIn main Mono.lex reconstructedContent.value)
                              some (constIn main Mono.lex common.gcd * primitive)
                            else
                              loop rest (fuel - 1) offered.2 [(point, corrected)]
                        | .accept =>
                            let nextSamples := (point, corrected) :: samples
                            if sampleTarget ≤ offered.2.accepted then
                              let interpolation ← brownInterpolate? nextSamples
                              let reconstructed :=
                                ofUnivariate (cmp := cmp) outer Mono.lex interpolation
                              let reconstructedView := toUnivariate main Mono.lex reconstructed
                              let reconstructedContent := contentCertWith
                                (fun a b => rawPrsCert a b)
                                reconstructedView.toArray.toList
                              let primitive := quotient reconstructed
                                (constIn main Mono.lex reconstructedContent.value)
                              some (constIn main Mono.lex common.gcd * primitive)
                            else
                              loop rest (fuel - 1) offered.2 nextSamples
      loop points pointFuel {} []

/-- Construct all recursive point layers by arity. -/
def brownOps {R : Type u}
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Inv R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R] :
    (n : Nat) → BrownOpsAt R n
  | 0 => brownBaseOps
  | 1 => brownUnaryOps
  | n + 2 => brownStepOps (brownOps (n + 1))

/-- Main variable of smallest positive input degree.  Ties keep the first
variable, making the choice deterministic. -/
def brownMainIndex {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (f h : MvPoly n R cmp) : Option (Fin n) :=
  (List.finRange n).foldl (fun best i =>
    let degree := max (degreeOf i f) (degreeOf i h)
    if degree = 0 then best
    else
      match best with
      | none => some i
      | some j =>
          if degree < max (degreeOf j f) (degreeOf j h) then some i
          else best) none

/-- Degree of a modular gcd image in Brown's selected main variable.  When
both inputs are constant there is no selected variable and the degree is
zero. -/
def brownImageDegree {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]
    (main : Option (Fin n)) (image : MvPoly n R cmp) : Nat :=
  match main with
  | none => 0
  | some i => degreeOf i image

/-- Involutive variable permutation which moves `main` to coordinate zero. -/
def brownSwapToZero {n : Nat} (main : Fin n) : Fin n → Fin n :=
  let zero : Fin n := ⟨0, Nat.zero_lt_of_lt main.isLt⟩
  fun i => if i = zero then main else if i = main then zero else i

/-- Run the recursive point layers after moving the cheapest main variable
to coordinate zero, then undo the same involution on the candidate. -/
def brownCandidate? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Inv R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    (pointFuel : Nat) (points : List R)
    (f h : MvPoly n R cmp) : Option (MvPoly n R cmp) :=
  match brownMainIndex f h with
  | none => (brownOps (R := R) n).candidate? cmp pointFuel points f h
  | some main =>
      let swap := brownSwapToZero main
      let f' := rename cmp swap f
      let h' := rename cmp swap h
      match (brownOps (R := R) n).candidate? cmp pointFuel points f' h' with
      | none => none
      | some candidate => some (rename cmp swap candidate)

/-- Run the recursive finite-field point layer and certify its result. -/
def brownFieldCert? {n : Nat} {R : Type u}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Inv R]
    [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    (pointFuel : Nat) (points : List R)
    (f h : MvPoly n R cmp) : Option (GcdCert n R cmp) :=
  match brownCandidate? pointFuel points f h with
  | none => none
  | some candidate => brownCheckedCandidate? f h candidate

/-! # Integer prime/CRT layer -/

/-- A nondependent modular image, ready for prime classification and CRT. -/
structure BrownModImage (n : Nat) where
  /-- Prime modulus used for this image. -/
  modulus : Nat
  /-- Gcd degree in the main variable selected before modular reduction. -/
  mainDegree : Nat
  /-- Canonically ordered support used to align CRT coordinates. -/
  support : List (Mono n)
  /-- Coefficients in the same order as `support`. -/
  residues : List Int
deriving BEq, Repr

/-- Reduce an integer problem at one bundled prime and run every recursive
point layer there.  Destroyed input degrees are rejected before returning an
image. -/
def intBrownImage? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (pointFuel : Nat) (f h : MvPoly n Int cmp)
    (prime : ZMod64.Prime) : Option (BrownModImage n) :=
  let main := brownMainIndex f h
  letI : ZMod64.Bounds prime.m := prime.bounds
  letI : ZMod64.PrimeModulus prime.m :=
    ZMod64.primeModulusOfPrime prime.prime
  let fImage := mapCoeffs (ZMod64.intCast prime.m) f
  let hImage := mapCoeffs (ZMod64.intCast prime.m) h
  let gamma : Int := Int.ofNat (Int.gcd f.leadingCoeff h.leadingCoeff)
  let gammaImage := ZMod64.intCast prime.m gamma
  if fImage.degrees != f.degrees || hImage.degrees != h.degrees ||
      gammaImage == 0 then
    none
  else
    let points : List (ZMod64 prime.m) :=
      (List.range (min pointFuel prime.m)).map
        (fun point => ZMod64.ofNat prime.m point)
    match brownCandidate? pointFuel points fImage hImage with
    | none => none
    | some candidate =>
        if candidate == 0 || candidate.leadingCoeff == 0 then none
        else
          let corrected :=
            C (gammaImage * candidate.leadingCoeff⁻¹) * candidate
          match brownCheckedCandidate? fImage hImage corrected with
          | none => none
          | some _ =>
            -- Keep the gamma-scaled candidate, not the field-normalized
            -- certificate gcd: monic normalization is correct for checking
            -- but would destroy the cross-prime normalization needed by CRT.
            some
              { modulus := prime.m
                mainDegree := brownImageDegree main corrected
                support := corrected.monomials
                residues := corrected.termsList.map
                  (fun term => Int.ofNat term.2.toNat) }

/-- Coefficientwise CRT state at one stabilized support. -/
structure BrownCrtState (n : Nat) where
  prime : BrownPrimeState n
  coeffs : List Modular.Crt

/-- Start a fresh CRT epoch from one image. -/
def BrownCrtState.start {n : Nat} (state : BrownPrimeState n)
    (image : BrownModImage n) : Option (BrownCrtState n) :=
  match image.residues.mapM
      (fun residue => Modular.Crt.init.push residue image.modulus) with
  | none => none
  | some coeffs => some { prime := state, coeffs }

/-- Atomically push corresponding CRT coordinates. -/
def brownPushCrt : List Modular.Crt → List Int → Nat →
    Option (List Modular.Crt)
  | [], [], _ => some []
  | old :: olds, residue :: residues, modulus =>
      match old.push residue modulus,
          brownPushCrt olds residues modulus with
      | some next, some rest => some (next :: rest)
      | _, _ => none
  | _, _, _ => none

/-- Fold an equal-support image into the current CRT epoch. -/
def BrownCrtState.push {n : Nat} (state : BrownCrtState n)
    (nextPrime : BrownPrimeState n) (image : BrownModImage n) :
    Option (BrownCrtState n) :=
  match brownPushCrt state.coeffs image.residues image.modulus with
  | none => none
  | some coeffs => some { prime := nextPrime, coeffs }

/-- Symmetric integer candidate from the current stable support, with scalar
content restored after primitive normalization. -/
def BrownCrtState.candidate {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (state : BrownCrtState n) (f h : MvPoly n Int cmp) :
    MvPoly n Int cmp :=
  let raw := ofTerms <|
    state.prime.support.zip (state.coeffs.map fun coeff => coeff.value)
  let commonContent := GcdOps.gcd (content f) (content h)
  polyNormalize (C commonContent * primPart raw)

/-- Fuel-bounded integer prime layer.  A candidate is offered only after an
equal-degree support has appeared twice and the second image has actually
been pushed through CRT. -/
def intBrownLoop {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (pointFuel : Nat) (f h : MvPoly n Int cmp) :
    List ZMod64.Prime → Nat → Option (BrownCrtState n) →
      Option (GcdCert n Int cmp)
  | _, 0, _ => none
  | [], _, _ => none
  | prime :: primes, fuel + 1, state =>
      match intBrownImage? pointFuel f h prime with
      | none => intBrownLoop pointFuel f h primes fuel state
      | some image =>
          let oldPrime := state.map (fun s => s.prime) |>.getD {}
          let offered := oldPrime.offer true true image.mainDegree image.support
          match offered.1 with
          | .bad | .unlucky =>
              intBrownLoop pointFuel f h primes fuel state
          | .accumulate | .restart =>
              match BrownCrtState.start offered.2 image with
              | none => intBrownLoop pointFuel f h primes fuel state
              | some next => intBrownLoop pointFuel f h primes fuel (some next)
          | .stable =>
              match state with
              | none =>
                  -- `stable` cannot arise from the empty default state.
                  intBrownLoop pointFuel f h primes fuel none
              | some old =>
                  match old.push offered.2 image with
                  | none => intBrownLoop pointFuel f h primes fuel state
                  | some next =>
                      match brownCheckedCandidate? f h (next.candidate f h) with
                      | some cert => some cert
                      | none =>
                          intBrownLoop pointFuel f h primes fuel (some next)

/-- Full integer Brown route for arity at least two. -/
def intBrownModularCert? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Int cmp) :
    Option (GcdCert n Int cmp) :=
  let supply := smallPrimeSupply 257 cfg.brownPrimeFuel
  intBrownLoop cfg.brownPointFuel f h supply cfg.brownPrimeFuel none

/-! # Concrete route-3 dispatch

The released univariate integer Brown implementation is reused verbatim at
arity one.  Higher arities use the point/prime machinery above; a fuel or
stabilization failure is a benign decline which leaves the mandatory checked
PRS route in control. -/

/-- Convert an arity-one integer polynomial to the released dense integer
kernel without changing coefficients. -/
def brownToZPoly {cmp : Mono 1 → Mono 1 → Ordering}
    [IsMonomialOrder cmp] (f : MvPoly 1 Int cmp) : ZPoly :=
  let view := toUnivariate (0 : Fin 1) Mono.lex f
  DensePoly.ofList <|
    (List.range view.size).map fun degree => coeff Mono.zero (view.coeff degree)

/-- Re-embed a released dense integer polynomial at arity one. -/
def brownOfZPoly {cmp : Mono 1 → Mono 1 → Ordering}
    [IsMonomialOrder cmp] (f : ZPoly) : MvPoly 1 Int cmp :=
  ofUnivariate (cmp := cmp) (0 : Fin 1) Mono.lex <|
    DensePoly.ofList <|
      (List.range f.size).map fun degree => C (f.coeff degree)

/-- Default arity-one integer certificate delegated to `HexPolyZGcd`.  The
dense kernel supplies the gcd and cofactors; the multivariate checker receives
a freshly constructed arity-one coprimality witness over those exact
cofactors. -/
def intArityOneRaw {cmp : Mono 1 → Mono 1 → Ordering}
    [IsMonomialOrder cmp] (f h : MvPoly 1 Int cmp) : GcdCert 1 Int cmp :=
  let z := ZPoly.gcdCert (brownToZPoly f) (brownToZPoly h)
  let g := brownOfZPoly z.gcd
  let cofL := brownOfZPoly z.cofL
  let cofR := brownOfZPoly z.cofR
  let lower := prsOps (R := Int) 0
  .mk g cofL cofR (succCoprime lower cmp cofL cofR)

theorem intArityOneRaw_checks {cmp : Mono 1 → Mono 1 → Ordering}
    [IsMonomialOrder cmp] (f h : MvPoly 1 Int cmp) :
    checkGcd f h (intArityOneRaw f h) = true := by
  sorry

def intArityOneCert {cmp : Mono 1 → Mono 1 → Ordering}
    [IsMonomialOrder cmp] (f h : MvPoly 1 Int cmp) : GcdCert 1 Int cmp :=
  intArityOneRaw f h

/-- Arity-indexed integer Brown producer.  The arity-one branch calls the
actual `HexPolyZGcd` Brown route and then builds a fresh multivariate
certificate; higher arities run dense point interpolation and prime CRT. -/
def intBrownCert? {n : Nat} (cmp : Mono n → Mono n → Ordering)
    [order : IsMonomialOrder cmp] (cfg : GcdConfig)
    (f h : MvPoly n Int cmp) : Option (GcdCert n Int cmp) :=
  match n, cmp, order, f, h with
  | 0, _, _, _, _ => none
  | 1, _, _, f, h =>
      if cfg.brownPrimeFuel = 0 || cfg.brownPointFuel = 0 then none
      else
        match ZPoly.brownCert? (brownToZPoly f) (brownToZPoly h) with
        | none => none
        | some cert => brownCheckedCandidate? f h (brownOfZPoly cert.gcd)
  | _ + 2, _, _, f, h => intBrownModularCert? cfg f h

/-- Generic routes 1--3 for route-0-reduced integer coefficients above the
delegated arity-one case. -/
def intConcreteProposalGeneric {n : Nat}
    (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Int cmp) : GcdProposal n Int cmp :=
  let fast := intFastProposal cfg f h
  match fast.cert? with
  | some _ => fast
  | none =>
      match intHeuristicCert? cfg f h with
      | some cert => ⟨some cert, fast.rand⟩
      | none => ⟨intBrownCert? cmp cfg f h, fast.rand⟩

/-- Concrete integer producer.  Arity one delegates immediately to the
released dense integer kernel; other arities use the multivariate routes. -/
def intConcreteProposal {n : Nat}
    (cmp : Mono n → Mono n → Ordering) [order : IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Int cmp) : GcdProposal n Int cmp :=
  match n, cmp, order, f, h with
  | 0, cmp, _, f, h => intConcreteProposalGeneric cmp cfg f h
  | 1, _, _, f, h => ⟨some (intArityOneCert f h), cfg.rand⟩
  | _ + 2, cmp, _, f, h => intConcreteProposalGeneric cmp cfg f h

/-- Register the concrete integer backend before rational lifting so that the
latter can invoke checked integer dispatch without selecting itself. -/
instance intProducer : GcdProducer Int where
  propose := fun cmp _ cfg f h => intConcreteProposal cmp cfg f h

/-- Dense Brown route over rationals.  Rational points are unbounded, so the
caller-provided point fuel is the only point-supply limit. -/
def ratBrownCert? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Rat cmp) :
    Option (GcdCert n Rat cmp) :=
  let points := (List.range cfg.brownPointFuel).map fun (point : Nat) =>
    ((Int.ofNat point : Int) : Rat)
  brownFieldCert? cfg.brownPointFuel points f h

/-! # Rational integer lifting -/

/-- Least common denominator of the stored rational coefficients. -/
def ratMvDen {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Rat cmp) : Nat :=
  p.termsList.foldl (fun den term => Nat.lcm den term.2.den) 1

/-- Clear rational coefficients against a supplied common denominator. -/
def ratMvClear {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] (den : Nat)
    (p : MvPoly n Rat cmp) : MvPoly n Int cmp :=
  ofTerms <| p.termsList.map fun term =>
    (term.1, term.2.num * Int.ofNat (den / term.2.den))

/-- Primitive integer model together with the rational scalar which embeds
it back to the original polynomial. -/
structure RatPrimitiveModel (n : Nat)
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  scale : Rat
  poly : MvPoly n Int cmp

/-- Clear all denominators and remove integer scalar content. -/
def ratPrimitiveModel {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (p : MvPoly n Rat cmp) : RatPrimitiveModel n cmp :=
  let den := ratMvDen p
  let cleared := ratMvClear den p
  let rawModel := primPart cleared
  let unitInv := GcdOps.exactDiv 1 (GcdOps.normUnit rawModel.leadingCoeff)
  let model := polyNormalize rawModel
  let scale : Rat :=
    (((content cleared * unitInv : Int) : Rat) / (den : Rat))
  ⟨scale, model⟩

/-- Build the required rational cofactor witness from primitive integer
models.  The checked integer dispatcher runs only on those models; both the
nested integer certificate and the final rational transport are executable
checker gates.  Its advanced random state is retained even when transport
checking rejects the witness. -/
def ratLiftCoprime? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Rat cmp) :
    Option (CoprimeCert n Rat cmp) × Rand :=
  let left := ratPrimitiveModel f
  let right := ratPrimitiveModel h
  if left.scale == 0 || right.scale == 0 then (none, cfg.rand)
  else
    let run := gcdCertWith cfg left.poly right.poly
    let cert := CoprimeCert.ratLift left.scale right.scale
      left.poly right.poly run.cert.coprime
    (if checkCoprime f h cert then some cert else none, run.rand)

/-- Offer a rational gcd candidate using exact divisions and a `ratLift`
cofactor certificate, threading the integer dispatcher's random state. -/
def ratCheckedCandidate? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h candidate : MvPoly n Rat cmp) :
    GcdProposal n Rat cmp :=
  if candidate == 0 then ⟨none, cfg.rand⟩
  else
    let normalized := polyNormalize candidate
    match divExact? f normalized, divExact? h normalized with
    | some cofL, some cofR =>
        let run := ratLiftCoprime? cfg cofL cofR
        match run.1 with
        | none => ⟨none, run.2⟩
        | some coprime =>
            let cert := GcdCert.mk normalized cofL cofR coprime
            ⟨if checkGcd f h cert then some cert else none, run.2⟩
    | _, _ => ⟨none, cfg.rand⟩

/-- Rational gcd through primitive integer models.  Scaling either input by a
nonzero rational unit does not change the monic gcd; candidate acceptance and
cofactor transport are both checked concretely.  Both the gcd models and the
resulting cofactor models go through checked integer dispatch, never rational
dispatch. -/
def ratIntegerLiftCert? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Rat cmp) : GcdProposal n Rat cmp :=
  let left := ratPrimitiveModel f
  let right := ratPrimitiveModel h
  if left.scale == 0 || right.scale == 0 then ⟨none, cfg.rand⟩
  else
    let run := gcdCertWith cfg left.poly right.poly
    let nextCfg := { cfg with rand := run.rand }
    ratCheckedCandidate? nextCfg f h (intModelToRat run.cert.gcd)

/-- Rational routes on an already route-0-reduced problem. -/
def ratConcreteProposal {n : Nat}
    (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Rat cmp) : GcdProposal n Rat cmp :=
  let lifted := ratIntegerLiftCert? cfg f h
  match lifted.cert? with
  | some _ => lifted
  | none =>
      let nextCfg := { cfg with rand := lifted.rand }
      ⟨ratBrownCert? nextCfg f h, lifted.rand⟩

/-- Dense Brown route over an already-prime coefficient field. -/
def primeFieldBrownCert? {n p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p]
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n (@ZMod64 p hp) cmp) :
    Option (GcdCert n (@ZMod64 p hp) cmp) :=
  let points := (List.range (min cfg.brownPointFuel p)).map fun point =>
    ZMod64.ofNat p point
  brownFieldCert? cfg.brownPointFuel points f h

/-- Routes 1 and 3 over a bundled prime field on an already route-0-reduced
problem. -/
def primeConcreteProposal {n p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p]
    (cmp : Mono n → Mono n → Ordering) [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n (@ZMod64 p hp) cmp) :
    GcdProposal n (@ZMod64 p hp) cmp :=
  let earlier := primeFastProposal cmp cfg f h
  match earlier.cert? with
  | some _ => earlier
  | none => ⟨primeFieldBrownCert? cfg f h, earlier.rand⟩

instance ratProducer : GcdProducer Rat where
  propose := fun cmp _ cfg f h => ratConcreteProposal cmp cfg f h

instance primeProducer {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] : GcdProducer (@ZMod64 p hp) where
  propose := fun cmp _ cfg f h => primeConcreteProposal cmp cfg f h

end Hex.MvPoly
