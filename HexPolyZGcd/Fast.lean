/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

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
    let xg := DensePoly.xgcd fp hp
    if xg.gcd.size != 1 then
      none
    else
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

/-- Search the small primes in ascending order, so a replayed certificate pays
for the cheapest available primality proof. -/
def modularWitness (f h : ZPoly) : Option CoprimeWitness :=
  let supply := (ZMod64.primesBelow 47 15).toList.reverse.toArray
  modularWitness.go f h supply 0 supply.size

/-- Route 1: offer `1` as the gcd and accept it only when the full checker
validates the modular coprimality witness. -/
def coprimeCert? (f h : ZPoly) : Option GcdCert := do
  match modularWitness f h with
  | none => none
  | some witness =>
      let candidate : GcdCert :=
        { gcd := 1, cofL := f, cofR := h, coprime := witness }
      if checkGcd f h candidate then some candidate else none

/-- Offer an arbitrary nonzero gcd candidate to the checker.  Exact division
builds its cofactors; a modular Bezout search supplies coprimality evidence.
Failure at any stage rejects the candidate without exposing it. -/
def checkedCandidate? (f h candidate : ZPoly) : Option GcdCert := do
  if candidate == 0 then none else pure ()
  let cofL ← divExact? f candidate
  let cofR ← divExact? h candidate
  let witness ← modularWitness cofL cofR
  let cert : GcdCert := { gcd := candidate, cofL, cofR, coprime := witness }
  if checkGcd f h cert then some cert else none

/-- Every certificate returned by the coprime fast route was accepted by the
full checker. -/
theorem coprimeCert?_checks {f h : ZPoly} {cert : GcdCert}
    (hc : coprimeCert? f h = some cert) :
    checkGcd f h cert = true := by
  unfold coprimeCert? at hc
  generalize hw : modularWitness f h = witness? at hc
  cases witness? with
  | none => simp at hc
  | some witness =>
      simp only at hc
      split at hc
      · rename_i hcheck
        cases hc
        exact hcheck
      · contradiction

end ZPoly

end Hex
