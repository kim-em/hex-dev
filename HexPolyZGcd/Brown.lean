/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexModular.Crt
public meta import HexPolyZ.Mignotte
public meta import HexPolyZGcd.Fast
public import HexModular.Crt
public import HexPolyZ.Mignotte
public import HexPolyZGcd.Fast

public section

/-!
Brown's multi-prime gcd producer for `Int[x]`.

The image degree is discovered at runtime, then retained as the dependent
length of one `CrtVec`.  Thus every offered modulus computes one inverse shared
by all coefficients.  Bad primes never enter the state.  Larger image degrees
are discarded as unlucky, while a smaller degree restarts the whole
accumulation.  Each reconstruction is primitive-normalized, has the integer
content restored, and is offered to `checkedCandidate?`.
-/

namespace Hex

namespace ZPoly

/-- One admissible, gamma-scaled modular gcd image. -/
structure BrownImage where
  degree : Nat
  coeffs : Array Int

/-- A running shared-vector CRT accumulation at the smallest image degree seen
so far.  The degree discovered at runtime indexes the coefficient vector. -/
structure BrownState where
  degree : Nat
  crt : Modular.CrtVec (degree + 1)

/-- Outcomes needed both by the loop and by route-level tests. -/
inductive BrownOffer where
  /-- The prime destroys an input degree or the gamma scaling. -/
  | bad
  /-- The image gcd degree is larger than the running minimum. -/
  | unlucky
  /-- A smaller image degree discarded all previous CRT data. -/
  | restarted (state : BrownState)
  /-- An equal-degree image was folded into the current CRT data. -/
  | accumulated (state : BrownState)

/-- Compute the monic image gcd and restore the integer leading-coefficient
multiple `gamma`.  Degree preservation checks reject bad primes before the
image can affect reconstruction. -/
def brownImage? (f h : ZPoly) (p : ZMod64.Prime) : Option BrownImage :=
  letI : ZMod64.Bounds p.m := p.bounds
  letI : ZMod64.PrimeModulus p.m := ZMod64.primeModulusOfPrime p.prime
  let f0 := primitivePart f
  let h0 := primitivePart h
  let fp := reduceModP p.m f0
  let hp := reduceModP p.m h0
  if fp.size != f0.size || hp.size != h0.size then
    none
  else
    let raw := FpPoly.gcdCached fp hp
    if raw.isZero then
      none
    else
      let unit := raw.leadingCoeff
      if unit == 0 then
        none
      else
        let monic := DensePoly.scale unit⁻¹ raw
        let gamma : Int := Int.ofNat (Int.gcd f0.leadingCoeff h0.leadingCoeff)
        let gammaP := ZMod64.intCast p.m gamma
        if gammaP == 0 then
          none
        else
          let scaled := DensePoly.scale gammaP monic
          some
            { degree := scaled.size - 1
              coeffs := scaled.toArray.map fun c => Int.ofNat c.toNat }

/-- View an image's dynamically sized coefficient array at the length recorded
by its degree.  The check keeps malformed externally constructed images from
entering the dependent CRT state. -/
private def BrownImage.vector? (image : BrownImage) :
    Option (Vector Int (image.degree + 1)) :=
  if h : image.coeffs.size = image.degree + 1 then
    some ⟨image.coeffs, h⟩
  else
    none

/-- Start a CRT state from one accepted image. -/
private def BrownState.start (image : BrownImage) (p : Nat) : Option BrownState := do
  let residues ← image.vector?
  let crt ← (Modular.CrtVec.init (image.degree + 1)).push residues p
  pure { degree := image.degree, crt }

/-- Fold an equal-degree image into an existing state. -/
private def BrownState.push (state : BrownState) (image : BrownImage)
    (p : Nat) : Option BrownState := do
  if hdegree : image.degree = state.degree then
    let residues ← image.vector?
    let residues : Vector Int (state.degree + 1) := hdegree ▸ residues
    let crt ← state.crt.push residues p
    pure { degree := state.degree, crt }
  else
    none

/-- Offer one prime to a possibly empty Brown state, applying the exact
bad/unlucky/restart rules before any CRT mutation. -/
def brownOffer (f h : ZPoly) (state : Option BrownState)
    (p : ZMod64.Prime) : BrownOffer :=
  match brownImage? f h p with
  | none => .bad
  | some image =>
      match state with
      | none =>
          match BrownState.start image p.m with
          | some next => .accumulated next
          | none => .bad
      | some old =>
          if image.degree > old.degree then
            .unlucky
          else if image.degree < old.degree then
            match BrownState.start image p.m with
            | some next => .restarted next
            | none => .bad
          else
            match old.push image p.m with
            | some next => .accumulated next
            | none => .bad

/-- Reconstruct and normalize the current integer gcd candidate. -/
def BrownState.candidate (state : BrownState) (f h : ZPoly) : ZPoly :=
  let raw : ZPoly := DensePoly.ofCoeffs state.crt.value.toArray
  let primitive := normalizePrimitiveSign (primitivePart raw)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  normalizePrimitiveSign (DensePoly.scale commonContent primitive)

/-- Conservative coefficient bound for Brown's gamma-scaled reconstruction.
The true primitive gcd degree is at most the smaller input degree.  Its
coefficients are bounded by either input's Mignotte bound, and scaling the
monic image by `gamma` costs at most one further factor of `gamma`. -/
def brownCoeffBound (f h : ZPoly) : Nat :=
  let f0 := primitivePart f
  let h0 := primitivePart h
  let degreeBound := min (f0.degree?.getD 0) (h0.degree?.getD 0)
  let center := degreeBound / 2
  let factorBound := min
    (mignotteCoeffBound f0 degreeBound center)
    (mignotteCoeffBound h0 degreeBound center)
  let gamma := Int.gcd f0.leadingCoeff h0.leadingCoeff
  gamma * factorBound

/-- Number of moduli contributing at least 23 bits that suffice to make the
CRT product strictly larger than twice the reconstruction bound. The bundled
hot-path supply below uses 24-bit primes; any dynamically generated tail uses
larger 31-bit primes, so 23 is a conservative common floor. -/
def brownModuliNeeded (f h : ZPoly) : Nat :=
  let bits := (2 * brownCoeffBound f h).log2 + 1
  (bits + 22) / 23

/-- Finite Brown prime budget derived from the reconstruction bound.  Doubling
the required good-modulus count and adding a small floor leaves room for bad
and unlucky images; exhaustion remains a benign fall-through to PRS. -/
def brownPrimeBudget (f h : ZPoly) : Nat :=
  2 * brownModuliNeeded f h + 8

/-- Result of consuming one lazily generated batch of Brown primes. -/
private inductive BrownProgress where
  | found (cert : GcdCert)
  | pending (state : Option BrownState)

/-- Four primes amortize supply construction while keeping the usual early
acceptance path far below the pessimistic Landau--Mignotte budget. -/
private def brownBatchSize : Nat :=
  4

/-- Construct a bundled prime from compile-time checked evidence. Both proof
arguments are erased from compiled code, so consuming the supply does not
repeat trial division at runtime. -/
private def bundledPrime (m : Nat) (hbound : m < 2 ^ 31)
    (hprime : Hex.Nat.isPrimeTrial m = true) : ZMod64.Prime :=
  let prime := Hex.Nat.isPrimeTrial_isPrime hprime
  { m, bounds := { pPos := prime.pos, pLtR := hbound }, prime }

/-- Descending 24-bit primes for the ordinary early-acceptance path. Sixteen
entries reconstruct more than 368 bits; a larger pessimistic budget continues
from the top of the dynamically generated 31-bit supply. -/
private def brownBundledSupply : Array ZMod64.Prime :=
  #[
    bundledPrime 16777213 (by decide) (by decide),
    bundledPrime 16777199 (by decide) (by decide),
    bundledPrime 16777183 (by decide) (by decide),
    bundledPrime 16777153 (by decide) (by decide),
    bundledPrime 16777141 (by decide) (by decide),
    bundledPrime 16777139 (by decide) (by decide),
    bundledPrime 16777127 (by decide) (by decide),
    bundledPrime 16777121 (by decide) (by decide),
    bundledPrime 16777099 (by decide) (by decide),
    bundledPrime 16777049 (by decide) (by decide),
    bundledPrime 16777027 (by decide) (by decide),
    bundledPrime 16776989 (by decide) (by decide),
    bundledPrime 16776973 (by decide) (by decide),
    bundledPrime 16776971 (by decide) (by decide),
    bundledPrime 16776967 (by decide) (by decide),
    bundledPrime 16776961 (by decide) (by decide)
  ]

/-- Fuel-bounded Brown loop.  Every successfully accumulated or restarted
state is offered immediately to the exact certificate checker. -/
private def brownLoop (f h : ZPoly) (supply : Array ZMod64.Prime)
    (index fuel : Nat) (state : Option BrownState) : BrownProgress :=
  if fuel = 0 then
    .pending state
  else if hi : index < supply.size then
    let p := supply[index]
    match brownOffer f h state p with
    | .bad | .unlucky => brownLoop f h supply (index + 1) (fuel - 1) state
    | .restarted next | .accumulated next =>
        match checkedCandidate? f h (next.candidate f h) with
        | some cert => .found cert
        | none => brownLoop f h supply (index + 1) (fuel - 1) (some next)
  else
    .pending state
termination_by fuel
decreasing_by all_goals omega

/-- Generate the prime budget in small descending batches, retaining the CRT
state between batches and stopping as soon as the exact checker accepts. -/
private def brownBatches (f h : ZPoly) (remaining start : Nat)
    (state : Option BrownState) : Option GcdCert :=
  if remaining = 0 then
    none
  else
    let count := min brownBatchSize remaining
    let supply := (ZMod64.primesBelow start count).filter
      (fun p => 2 ^ 30 < p.m)
    match brownLoop f h supply 0 supply.size state with
    | .found cert => some cert
    | .pending next =>
        let nextStart := supply.back?.map (fun p => p.m - 1) |>.getD 0
        brownBatches f h (remaining - count) nextStart next
termination_by remaining
decreasing_by
  have hcount : 0 < min brownBatchSize remaining := by
    simp [brownBatchSize]
    omega
  omega

/-- Brown's modular gcd route. The bundled supply is tried before computing the
pessimistic gamma-scaled Landau--Mignotte budget; if it is exhausted, the
remaining finite budget comes from the dynamic 31-bit supply. Failure is
benign: the dispatcher continues to its deterministic checked fallback. -/
def brownCert? (f h : ZPoly) : Option GcdCert :=
  match brownLoop f h brownBundledSupply 0 brownBundledSupply.size none with
  | .found cert => some cert
  | .pending state =>
      let budget := brownPrimeBudget f h
      if budget <= brownBundledSupply.size then
        none
      else
        let nextStart := 2 ^ 31 - 1
        brownBatches f h (budget - brownBundledSupply.size) nextStart state

/-- A certificate returned by one Brown supply traversal has passed the
shared candidate checker. -/
private theorem brownLoop_checks (f h : ZPoly)
    (supply : Array ZMod64.Prime) (index fuel : Nat)
    (state : Option BrownState) {cert : GcdCert}
    (hfound : brownLoop f h supply index fuel state = .found cert) :
    checkGcd f h cert = true := by
  unfold brownLoop at hfound
  by_cases hfuel : fuel = 0
  · rw [ite_eq_left hfuel] at hfound
    contradiction
  · rw [ite_eq_right hfuel] at hfound
    by_cases hi : index < supply.size
    · rw [dite_eq_left hi] at hfound
      dsimp only at hfound
      generalize hoffer : brownOffer f h state supply[index] = offer at hfound
      cases offer with
      | bad =>
          exact brownLoop_checks f h supply (index + 1) (fuel - 1) state hfound
      | unlucky =>
          exact brownLoop_checks f h supply (index + 1) (fuel - 1) state hfound
      | restarted next =>
          simp only at hfound
          generalize hcand : checkedCandidate? f h (next.candidate f h) =
            candidate? at hfound
          cases candidate? with
          | some candidate =>
              cases hfound
              exact checkedCandidate?_checks hcand
          | none =>
              exact brownLoop_checks f h supply (index + 1) (fuel - 1)
                (some next) hfound
      | accumulated next =>
          simp only at hfound
          generalize hcand : checkedCandidate? f h (next.candidate f h) =
            candidate? at hfound
          cases candidate? with
          | some candidate =>
              cases hfound
              exact checkedCandidate?_checks hcand
          | none =>
              exact brownLoop_checks f h supply (index + 1) (fuel - 1)
                (some next) hfound
    · rw [dite_eq_right hi] at hfound
      contradiction
termination_by fuel
decreasing_by all_goals omega

/-- A certificate returned by the dynamically generated Brown batches has
passed the shared checker. -/
private theorem brownBatches_checks (f h : ZPoly) (remaining start : Nat)
    (state : Option BrownState) {cert : GcdCert}
    (hcert : brownBatches f h remaining start state = some cert) :
    checkGcd f h cert = true := by
  unfold brownBatches at hcert
  by_cases hremaining : remaining = 0
  · rw [ite_eq_left hremaining] at hcert
    contradiction
  · rw [ite_eq_right hremaining] at hcert
    dsimp only at hcert
    let supply := (ZMod64.primesBelow start (min brownBatchSize remaining)).filter
      (fun p => 2 ^ 30 < p.m)
    change (match brownLoop f h supply 0 supply.size state with
      | .found found => some found
      | .pending next =>
          brownBatches f h (remaining - min brownBatchSize remaining)
            (supply.back?.map (fun p => p.m - 1) |>.getD 0) next) =
        some cert at hcert
    generalize hloop : brownLoop f h supply 0 supply.size state = progress at hcert
    cases progress with
    | found found =>
        cases hcert
        exact brownLoop_checks f h supply 0 supply.size state hloop
    | pending next =>
        exact brownBatches_checks f h (remaining - min brownBatchSize remaining)
          (supply.back?.map (fun p => p.m - 1) |>.getD 0) next hcert
termination_by remaining
decreasing_by
  have hcount : 0 < min brownBatchSize remaining := by
    simp [brownBatchSize]
    omega
  exact Nat.sub_lt (Nat.zero_lt_of_ne_zero hremaining) hcount

/-- Every certificate returned by Brown reconstruction has passed the full
checker. -/
theorem brownCert?_checks {f h : ZPoly} {cert : GcdCert}
    (hcert : brownCert? f h = some cert) :
    checkGcd f h cert = true := by
  unfold brownCert? at hcert
  generalize hloop : brownLoop f h brownBundledSupply 0
      brownBundledSupply.size none = progress at hcert
  cases progress with
  | found found =>
      cases hcert
      exact brownLoop_checks f h brownBundledSupply 0
        brownBundledSupply.size none hloop
  | pending state =>
      dsimp only at hcert
      by_cases hbudget : brownPrimeBudget f h ≤ brownBundledSupply.size
      · rw [ite_eq_left hbudget] at hcert
        contradiction
      · rw [ite_eq_right hbudget] at hcert
        exact brownBatches_checks f h
          (brownPrimeBudget f h - brownBundledSupply.size) (2 ^ 31 - 1)
          state hcert

/-! Route-level executable pins for the three easy-to-miss Brown rules. -/

-- Every small witness probe is unlucky when the constant offset is the
-- product of the primes through 47. A bundled large probe still succeeds.
#guard
  let smallPrimorial : Int := 614889782588491410
  let f : ZPoly := DensePoly.ofList [0, 1]
  let h : ZPoly := DensePoly.ofList [smallPrimorial, 1]
  (modularWitness f h).isSome

private def primeAt? (p : Nat) : Option ZMod64.Prime :=
  (ZMod64.primesBelow p 1)[0]?

-- A prime dividing both leading coefficients is bad: both degrees drop.
#guard
  let f : ZPoly := DensePoly.ofList [1, 2]
  let h : ZPoly := DensePoly.ofList [3, 2]
  match primeAt? 2 with
  | some p => (brownImage? f h p).isNone
  | none => false

-- At `p = 2`, `x` and `x+2` have an unlucky degree-one image gcd.  The
-- degree-zero image at `p = 3` must restart the state.
#guard
  let f : ZPoly := DensePoly.ofList [0, 1]
  let h : ZPoly := DensePoly.ofList [2, 1]
  match primeAt? 2, primeAt? 3 with
  | some p2, some p3 =>
      match brownOffer f h none p2 with
      | .accumulated state =>
          match brownOffer f h (some state) p3 with
          | .restarted _ => true
          | _ => false
      | _ => false
  | _, _ => false

-- Gamma scaling restores the nonmonic leading coefficient `2` to the image
-- gcd `2*x+1` rather than reconstructing its monic associate.
#guard
  let common : ZPoly := DensePoly.ofList [1, 2]
  let f := common * DensePoly.ofList [1, 1]
  let h := common * DensePoly.ofList [2, 1]
  match primeAt? 5 with
  | some p =>
      match brownImage? f h p with
      | some image => image.coeffs == #[1, 2]
      | none => false
  | none => false

-- Equal-degree images share one vector CRT state and therefore one common
-- product modulus, independent of the number of coefficients.
#guard
  let common : ZPoly := DensePoly.ofList [1, 2, 3, 4]
  let f := common * DensePoly.ofList [1, 1]
  let h := common * DensePoly.ofList [2, 1]
  match primeAt? 5, primeAt? 7 with
  | some p5, some p7 =>
      match brownOffer f h none p5 with
      | .accumulated state =>
          match brownOffer f h (some state) p7 with
          | .accumulated next =>
              next.crt.modulus == 35 &&
                next.crt.value.toArray == common.toArray
          | _ => false
      | _ => false
  | _, _ => false

-- This coefficient is larger than half the entire former 55-small-prime
-- modulus.  The bound-sized route must continue beyond that old product and
-- still return a checker-accepted certificate.
#guard
  let oldModulus := (ZMod64.primesBelow 257 55).foldl
    (fun modulus p => modulus * p.m) 1
  let common : ZPoly := DensePoly.ofList [Int.ofNat oldModulus + 1, 1]
  let f := common * DensePoly.ofList [1, 1]
  let h := common * DensePoly.ofList [2, 1]
  match brownCert? f h with
  | some cert => cert.gcd == common && checkGcd f h cert
  | none => false

end ZPoly

end Hex
