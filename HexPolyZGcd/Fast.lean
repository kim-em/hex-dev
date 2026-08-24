/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyZGcd.Cert
public import HexPolyZGcd.Cert

public section

/-!
The one-image coprimality route.

This route is intentionally asymmetric: a modular gcd of positive degree says
nothing over the integers, while a checked modular Bezout identity proves the
integer cofactors coprime and can return immediately.
-/

namespace Hex

namespace ZPoly

/-- Try to construct a degree-preserving modular Bezout witness at one bundled
prime.  The final call to `checkCoprime` keeps field normalization and all
dependent-instance plumbing outside the trusted result. -/
def modularWitnessAt (f h : ZPoly) (p : ZMod64.Prime) :
    Option CoprimeWitness :=
  letI : ZMod64.Bounds p.m := p.bounds
  letI : ZMod64.PrimeModulus p.m := ZMod64.primeModulusOfPrime p.prime
  let fp := reduceModP p.m f
  let hp := reduceModP p.m h
  if fp.size != f.size || hp.size != h.size then
    none
  else
    let imageGcd := FpPoly.gcdCached fp hp
    if imageGcd.size != 1 then
      none
    else
      let xg := DensePoly.xgcd fp hp
      let scalar := xg.gcd.coeff 0
      if scalar == 0 then
        none
      else
        let alpha := DensePoly.scale scalar⁻¹ xg.left
        let beta := DensePoly.scale scalar⁻¹ xg.right
        let witness := CoprimeWitness.modular p alpha beta
        if checkCoprime f h witness then some witness else none

/-- Search a finite prime supply for the first usable modular witness. -/
private def modularWitness.go (f h : ZPoly) (supply : Array ZMod64.Prime)
    (index fuel : Nat) : Option CoprimeWitness :=
  if fuel = 0 then
    none
  else if hi : index < supply.size then
    match modularWitnessAt f h supply[index] with
    | some witness => some witness
    | none => modularWitness.go f h supply (index + 1) (fuel - 1)
  else
    none
termination_by fuel
decreasing_by all_goals omega

/-- Construct a prime whose compile-time primality check is erased from the
compiled witness search. -/
private def witnessPrime (m : Nat) (hbound : m < 2 ^ 31)
    (hprime : Hex.Nat.isPrimeTrial m = true) : ZMod64.Prime :=
  let prime := Hex.Nat.isPrimeTrial_isPrime hprime
  { m, bounds := { pPos := prime.pos, pLtR := hbound }, prime }

/-- Small ascending primes followed by large prechecked probes. The large
probes handle inputs whose reductions collide at every small prime, such as a
product of many consecutive linear factors. -/
private def witnessSupply : Array ZMod64.Prime :=
  (ZMod64.primesBelow 47 15).toList.reverse.toArray ++ #[
    witnessPrime 16777213 (by decide) (by decide),
    witnessPrime 16777199 (by decide) (by decide),
    witnessPrime 16777183 (by decide) (by decide)
  ]

/-- Search small primes first for cheap replay, then the bundled large probes
for structured inputs on which every small image is unlucky. -/
def modularWitness (f h : ZPoly) : Option CoprimeWitness :=
  modularWitness.go f h witnessSupply 0 witnessSupply.size

/-- The single small-prime probe used by route 1. A nonconstant image gcd is
inconclusive and hands control to reconstruction immediately; exhausting the
full witness supply here would turn the SPEC's one-image fast path into one
image per available prime on every genuinely noncoprime input. -/
private def coprimeSupply : Array ZMod64.Prime :=
  ZMod64.primesBelow 47 1

/-- Route 1: offer `1` after one modular image and accept it only when the full
checker validates the resulting coprimality witness. -/
def coprimeCert? (f h : ZPoly) : Option GcdCert := do
  match modularWitness.go f h coprimeSupply 0 coprimeSupply.size with
  | none => none
  | some witness =>
      let candidate : GcdCert :=
        { gcd := 1, cofL := f, cofR := h, coprime := witness }
      if checkGcd f h candidate then some candidate else none

/-- Route 1a: recognize the first Euclidean remainder as the gcd.

If `f - h` divides `f`, then it also divides `h`, and the resulting cofactors
differ by the unit used to normalize the remainder's sign.  One long division
therefore supplies both cofactors and the integral Bezout witness; the shared
checker still replays both input products before the certificate is exposed.
This is especially useful for adjacent cofactors, but is not tied to any input
generator. -/
def differenceCert? (f h : ZPoly) : Option GcdCert := do
  let difference := f - h
  if difference == 0 then none else pure ()
  -- A useful first Euclidean remainder must lower the degree of both inputs.
  -- Without this guard an unrelated equal-degree pair pays for a doomed long
  -- division and checker replay before entering its ordinary gcd route.
  if min f.size h.size <= difference.size then none else pure ()
  let sign : Int := if difference.leadingCoeff < 0 then -1 else 1
  let candidate := normalizePrimitiveSign difference
  let cofL := (DensePoly.divMod f candidate).1
  let cofR := cofL - DensePoly.C sign
  let cert : GcdCert :=
    { gcd := candidate
      cofL
      cofR
      coprime := .constant 1 (-1) sign }
  if checkGcd f h cert then some cert else none

/-- A nonzero constant difference is already an integral Bezout identity.
This avoids a modular xgcd when reconstruction leaves adjacent cofactors. -/
private def differenceWitness? (f h : ZPoly) : Option CoprimeWitness :=
  let difference := f - h
  if difference.size = 1 && difference.coeff 0 != 0 then
    let witness := CoprimeWitness.constant 1 (-1) (difference.coeff 0)
    if checkCoprime f h witness then some witness else none
  else
    none

/-- Prefer a direct integral identity before searching modular images. -/
private def candidateWitness (f h : ZPoly) : Option CoprimeWitness :=
  match differenceWitness? f h with
  | some witness => some witness
  | none => modularWitness f h

/-- Offer an arbitrary nonzero gcd candidate to the checker. Long division
builds provisional cofactors; the final checker already replays both product
identities, so running `divExact?` here would duplicate those two dense
multiplications. A direct constant identity or modular search supplies
coprimality evidence. Failure at any stage rejects the candidate without
exposing it. -/
def checkedCandidate? (f h candidate : ZPoly) : Option GcdCert := do
  if candidate == 0 then none else pure ()
  let cofL := (DensePoly.divMod f candidate).1
  let cofR := (DensePoly.divMod h candidate).1
  let witness ← candidateWitness cofL cofR
  let cert : GcdCert := { gcd := candidate, cofL, cofR, coprime := witness }
  if checkGcd f h cert then some cert else none

/-- Every certificate returned by the coprime fast route was accepted by the
full checker. -/
theorem coprimeCert?_checks {f h : ZPoly} {cert : GcdCert}
    (hc : coprimeCert? f h = some cert) :
    checkGcd f h cert = true := by
  unfold coprimeCert? at hc
  generalize hw : modularWitness.go f h coprimeSupply 0 coprimeSupply.size =
    witness? at hc
  cases witness? with
  | none => simp at hc
  | some witness =>
      simp only at hc
      split at hc
      · rename_i hcheck
        cases hc
        exact hcheck
      · contradiction

-- Both signs of an adjacent-cofactor remainder yield the same normalized gcd
-- and a checker-accepted unit-difference certificate.
#guard
  let common : ZPoly := DensePoly.ofList [3, 2]
  let cofactor : ZPoly := DensePoly.ofList [5, -1, 1]
  let f := common * cofactor
  let h := common * (cofactor + 1)
  match differenceCert? f h with
  | some cert => cert.gcd == common && checkGcd f h cert
  | none => false

#guard
  let common : ZPoly := DensePoly.ofList [3, 2]
  let cofactor : ZPoly := DensePoly.ofList [5, -1, 1]
  let f := common * (cofactor + 1)
  let h := common * cofactor
  match differenceCert? f h with
  | some cert => cert.gcd == common && checkGcd f h cert
  | none => false

end ZPoly

end Hex
