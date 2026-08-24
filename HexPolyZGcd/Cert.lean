/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Modulus
public import HexPolyFp
public import HexPolyZGcd.Divide

public section
set_option backward.proofsInPublic true

/-!
Checked certificates for integer-polynomial gcd candidates.

Candidate production is deliberately kept out of this file.  The checker only
replays two exact product identities, normalization, coprime integer contents,
and one of two independently checkable coprimality witnesses.
-/

namespace Hex

namespace ZPoly

/-- Coefficientwise reduction of an integer polynomial into a bundled
word-sized residue ring.  This copy is local to the gcd checker so its kernel
closure does not depend on the Hensel implementation. -/
@[expose]
def reduceModP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) : FpPoly p :=
  DensePoly.ofList <|
    (List.range f.size).map (fun i => ZMod64.intCast p (f.coeff i))

/-- Evidence that the two cofactors have no common nonunit factor. -/
inductive CoprimeWitness
  /-- A degree-preserving reduction and a Bezout identity over a prime field. -/
  | modular (p : ZMod64.Prime)
      (alpha beta : @FpPoly p.m p.bounds)
  /-- An integral polynomial combination equal to a nonzero constant. -/
  | constant (u v : ZPoly) (k : Int)

/-- A gcd candidate, its two exact cofactors, and checked coprimality data. -/
structure GcdCert where
  gcd : ZPoly
  cofL : ZPoly
  cofR : ZPoly
  coprime : CoprimeWitness

/-- The normalization convention for integer gcds.  Zero is admitted for the
unique degenerate answer `gcd 0 0`; every nonzero result has positive leading
coefficient and positive content. -/
@[expose]
def NormalizedGcd (g : ZPoly) : Bool :=
  g == 0 ||
    (decide (0 < DensePoly.leadingCoeff g) && decide (0 < content g))

/-- Replay the coprimality half of a gcd certificate. -/
@[expose]
def checkCoprime (f h : ZPoly) : CoprimeWitness → Bool
  | .constant u v k =>
      decide (k ≠ 0) && (u * f + v * h == DensePoly.C k)
  | .modular p alpha beta =>
      letI : ZMod64.Bounds p.m := p.bounds
      letI : ZMod64.PrimeModulus p.m := ZMod64.primeModulusOfPrime p.prime
      let fp := reduceModP p.m f
      let hp := reduceModP p.m h
      decide (fp.size = f.size) &&
        decide (hp.size = h.size) &&
        (alpha * fp + beta * hp == 1)

/-- Check a gcd certificate.  Every producer, including deterministic
fallbacks, must pass through this function before its candidate is exposed. -/
@[expose]
def checkGcd (f h : ZPoly) (c : GcdCert) : Bool :=
  (c.gcd * c.cofL == f) &&
    (c.gcd * c.cofR == h) &&
    NormalizedGcd c.gcd &&
    decide (Int.gcd (content c.cofL) (content c.cofR) = 1) &&
    checkCoprime c.cofL c.cofR c.coprime

/-- The cofactor identities together with absence of a common nonunit
cofactor. -/
def CoprimeCofactors (f h g : ZPoly) : Prop :=
  ∃ f' h', f = g * f' ∧ h = g * h' ∧
    ∀ d : ZPoly, d ∣ f' → d ∣ h' → IsUnit d

/-- A successful checker establishes both exact cofactor identities and
coprimality of the cofactors. -/
theorem checkGcd_sound {f h : ZPoly} {c : GcdCert}
    (hc : checkGcd f h c = true) :
    f = c.gcd * c.cofL ∧ h = c.gcd * c.cofR ∧
      ∀ d : ZPoly, d ∣ c.cofL → d ∣ c.cofR → IsUnit d := by
  sorry

/-- Checker soundness packaged in the public cofactor predicate. -/
theorem coprimeCofactors_of_checkGcd {f h : ZPoly} {c : GcdCert}
    (hc : checkGcd f h c = true) :
    CoprimeCofactors f h c.gcd := by
  rcases checkGcd_sound hc with ⟨hf, hh, hcop⟩
  exact ⟨c.cofL, c.cofR, hf, hh, hcop⟩

end ZPoly

end Hex
