/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexModular.Crt
public meta import HexPolyZGcd.Fast
public import HexModular.Crt
public import HexPolyZGcd.Fast

public section

/-!
Brown's multi-prime gcd producer for `Int[x]`.

The state records one scalar CRT accumulator per coefficient because the image
degree is discovered at runtime.  Bad primes never enter the state.  Larger
image degrees are discarded as unlucky, while a smaller degree restarts the
whole accumulation.  Each reconstruction is primitive-normalized, has the
integer content restored, and is offered to `checkedCandidate?`.
-/

namespace Hex

namespace ZPoly

/-- One admissible, gamma-scaled modular gcd image. -/
structure BrownImage where
  degree : Nat
  coeffs : Array Int

/-- A running coefficientwise CRT accumulation at the smallest image degree
seen so far. -/
structure BrownState where
  degree : Nat
  coeffs : Array Modular.Crt

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
    let raw := DensePoly.gcd fp hp
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

/-- Push corresponding scalar CRT entries, failing atomically on a length
mismatch or on any non-coprime modulus. -/
private def pushCoeffs : List Modular.Crt → List Int → Nat →
    Option (List Modular.Crt)
  | [], [], _ => some []
  | c :: cs, r :: rs, p => do
      let next ← c.push r p
      let rest ← pushCoeffs cs rs p
      pure (next :: rest)
  | _, _, _ => none

/-- Start a CRT state from one accepted image. -/
private def BrownState.start (image : BrownImage) (p : Nat) : Option BrownState := do
  let coeffs ← image.coeffs.toList.mapM fun r => Modular.Crt.init.push r p
  pure { degree := image.degree, coeffs := coeffs.toArray }

/-- Fold an equal-degree image into an existing state. -/
private def BrownState.push (state : BrownState) (image : BrownImage)
    (p : Nat) : Option BrownState := do
  if image.degree != state.degree then none else pure ()
  let coeffs ← pushCoeffs state.coeffs.toList image.coeffs.toList p
  pure { degree := state.degree, coeffs := coeffs.toArray }

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
  let raw : ZPoly := DensePoly.ofCoeffs (state.coeffs.map (fun c => c.value))
  let primitive := normalizePrimitiveSign (primitivePart raw)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  normalizePrimitiveSign (DensePoly.scale commonContent primitive)

/-- Fuel-bounded Brown loop.  Every successfully accumulated or restarted
state is offered immediately to the exact certificate checker. -/
private def brownLoop (f h : ZPoly) (supply : Array ZMod64.Prime)
    (index fuel : Nat) (state : Option BrownState) : Option GcdCert :=
  if fuel = 0 then
    none
  else if hi : index < supply.size then
    let p := supply[index]
    match brownOffer f h state p with
    | .bad | .unlucky => brownLoop f h supply (index + 1) (fuel - 1) state
    | .restarted next | .accumulated next =>
        match checkedCandidate? f h (next.candidate f h) with
        | some cert => some cert
        | none => brownLoop f h supply (index + 1) (fuel - 1) (some next)
  else
    none
termination_by fuel
decreasing_by all_goals omega

/-- Brown's modular gcd route over the first 55 primes.  Failure is benign:
the dispatcher continues to its deterministic checked fallback. -/
def brownCert? (f h : ZPoly) : Option GcdCert :=
  let supply := (ZMod64.primesBelow 257 55).toList.reverse.toArray
  brownLoop f h supply 0 supply.size none

/-! Route-level executable pins for the three easy-to-miss Brown rules. -/

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

end ZPoly

end Hex
