/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyZGcd.Brown
public meta import HexPolyZGcd.Heu
public meta import HexPolyZGcd.Prs
public import HexPolyZGcd.Brown
public import HexPolyZGcd.Heu
public import HexPolyZGcd.Prs

public section
set_option backward.proofsInPublic true

/-!
The usable integer-polynomial gcd API.

Fast candidates are replayed by one checker and fall through to the total
extended-subresultant route.  The earlier rational implementation remains in
this file as an independently named reference implementation and test oracle;
it is not part of public dispatch.
-/

namespace Hex

namespace ZPoly

/-- The canonical integer candidate obtained from the rational gcd, with the
common integer content restored. -/
def rationalGcdCandidate (f h : ZPoly) : ZPoly :=
  let primitive :=
    ratPolyPrimitivePart (DensePoly.gcd (toRatPoly f) (toRatPoly h))
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  normalizePrimitiveSign (DensePoly.scale commonContent primitive)

/-- The candidate is nonzero unless both inputs are zero. -/
theorem rationalGcdCandidate_ne_zero {f h : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0) :
    rationalGcdCandidate f h ≠ 0 := by
  sorry

/-- The rational gcd candidate exactly divides both integer inputs. -/
theorem rationalGcdCandidate_divisions {f h : ZPoly}
    (hnz : f ≠ 0 ∨ h ≠ 0) :
    (divExact? f (rationalGcdCandidate f h)).isSome = true ∧
      (divExact? h (rationalGcdCandidate f h)).isSome = true := by
  sorry

/-- Least common denominator of the stored coefficients of a rational
polynomial. -/
private def ratDen (f : DensePoly Rat) : Nat :=
  f.toArray.foldl (fun d q => Nat.lcm d q.den) 1

/-- Clear a rational polynomial with a denominator known to be a common
multiple of all coefficient denominators. -/
private def clearRat (den : Nat) (f : DensePoly Rat) : ZPoly :=
  DensePoly.ofList <|
    (List.range f.size).map fun i =>
      let q := f.coeff i
      q.num * Int.ofNat (den / q.den)

/-- Clear the extended rational gcd identity into an integral combination.
For coprime cofactors the rational gcd is a nonzero constant, so the returned
`k` is nonzero and the checker verifies the identity directly. -/
def rationalCoprimeWitness (f h : ZPoly) : CoprimeWitness :=
  let xg := DensePoly.xgcd (toRatPoly f) (toRatPoly h)
  let scalar := xg.gcd.coeff 0
  let den := Nat.lcm (ratDen xg.left) (Nat.lcm (ratDen xg.right) scalar.den)
  let u := clearRat den xg.left
  let v := clearRat den xg.right
  let k := scalar.num * Int.ofNat (den / scalar.den)
  .constant u v k

/-- The canonical certificate for the doubly-zero input.  Unit cofactors keep
the coprimality obligation meaningful even though the gcd itself is zero. -/
def zeroGcdCert : GcdCert :=
  { gcd := 0
    cofL := 1
    cofR := 1
    coprime := .constant 1 0 1 }

/-- Deterministic rational fallback certificate.

The cofactors are the concrete long-division quotients.  Their exactness is
part of `rationalGcdCert_checks`, but no proof is used to extract runtime
data: if the rational-gcd or division implementation regresses, `checkGcd`
reports the concrete certificate as invalid rather than extracting data from
an impossible branch. -/
def rationalGcdCert (f h : ZPoly) : GcdCert :=
  if f = 0 ∧ h = 0 then
    zeroGcdCert
  else
    let g := rationalGcdCandidate f h
    let cofL := (DensePoly.divMod f g).1
    let cofR := (DensePoly.divMod h g).1
    { gcd := g
      cofL
      cofR
      coprime := rationalCoprimeWitness cofL cofR }

/-- Correctness of the deterministic rational fallback, concentrated in one
proof obligation while the executable certificate remains fully concrete. -/
theorem rationalGcdCert_checks (f h : ZPoly) :
    checkGcd f h (rationalGcdCert f h) = true := by
  sorry

/-- The total deterministic fallback.  The name is retained for producer API
compatibility; unlike the previous implementation, this definition does not
use a theorem to manufacture data from a rejected checker branch.  Its
checker contract is `rationalGcdCert_checks`. -/
def checkedRationalGcdCert (f h : ZPoly) : GcdCert :=
  rationalGcdCert f h

/-- Scan the low coefficients for the exponent of the first nonzero term. -/
private def xOrder.go (f : ZPoly) : Nat → Nat → Nat
  | index, 0 => index
  | index, fuel + 1 =>
      if f.coeff index == 0 then xOrder.go f (index + 1) fuel else index

/-- Largest exponent `k` such that `x^k` divides `f`; zero has order zero for
the structural route, which handles it separately. -/
def xOrder (f : ZPoly) : Nat :=
  if f.isZero then 0 else xOrder.go f 0 f.size

/-- The monic power `x^k`. -/
def xPower (k : Nat) : ZPoly :=
  DensePoly.ofList (List.replicate k 0 ++ [1])

/-- Common scalar and `x`-power removed before every primitive route. -/
structure StructuralReduction where
  factor : ZPoly
  left : ZPoly
  right : ZPoly

/-- Route 0: extract the common integer content and common power of `x`.
Both divisions are explicit checked operations, so a representation or
division regression declines instead of inventing a reduced input. -/
def structuralReduction? (f h : ZPoly) : Option StructuralReduction := do
  if f.isZero || h.isZero then none else pure ()
  let commonPower := min (xOrder f) (xOrder h)
  let commonContent : Int := Int.ofNat (Int.gcd (content f) (content h))
  let factor := DensePoly.scale commonContent (xPower commonPower)
  let left ← divExact? f factor
  let right ← divExact? h factor
  pure { factor, left, right }

/-- Restore route 0's common factor around a certificate for the reduced
pair.  The public checker is the only acceptance gate. -/
def restoreStructural? (f h : ZPoly) (reduced : StructuralReduction)
    (cert : GcdCert) : Option GcdCert :=
  let restored : GcdCert :=
    { gcd := normalizePrimitiveSign (reduced.factor * cert.gcd)
      cofL := cert.cofL
      cofR := cert.cofR
      coprime := cert.coprime }
  if checkGcd f h restored then some restored else none

/-- Routes 1--4 on inputs after structural content and `x`-power removal. -/
def reducedGcdCert (f h : ZPoly) : GcdCert :=
  match coprimeCert? f h with
  | some cert => cert
  | none =>
      match heuCert? f h with
      | some cert => cert
      | none =>
          match brownCert? f h with
          | some cert => cert
          | none => prsCert f h

/-- Produce a checked gcd certificate.  Route 0 runs first; rejected fast
candidates and any failed structural restoration fall through to total,
data-only extended-subresultant route 4. -/
def gcdCert (f h : ZPoly) : GcdCert :=
  if f.isZero || h.isZero then
    prsCert f h
  else
    match structuralReduction? f h with
    | none => prsCert f h
    | some reduced =>
        match restoreStructural? f h reduced
            (reducedGcdCert reduced.left reduced.right) with
        | some cert => cert
        | none => prsCert f h

/-- Every public certificate has passed the checker. -/
theorem gcdCert_checks (f h : ZPoly) :
    checkGcd f h (gcdCert f h) = true := by
  sorry

/-- Canonically normalized gcd of two integer polynomials. -/
@[expose]
def gcd (f h : ZPoly) : ZPoly :=
  (gcdCert f h).gcd

/-- Controlled unfolding lemma for the otherwise opaque producer-facing gcd
definition. -/
theorem gcd_eq_cert (f h : ZPoly) :
    gcd f h = (gcdCert f h).gcd := rfl

/-- Exact cofactors belonging to the checked gcd. -/
def cofactors (f h : ZPoly) : ZPoly × ZPoly :=
  let cert := gcdCert f h
  (cert.cofL, cert.cofR)

/-- Decide coprimality using the canonical gcd. -/
def isCoprime (f h : ZPoly) : Bool :=
  gcd f h == 1

/-- Fold gcd over a list; the empty-list convention is zero. -/
def gcdList (fs : List ZPoly) : ZPoly :=
  fs.foldl gcd 0

/-- Canonically normalized least common multiple. -/
def lcm (f h : ZPoly) : ZPoly :=
  if f.isZero || h.isZero then
    0
  else
    let cert := gcdCert f h
    normalizePrimitiveSign (cert.gcd * cert.cofL * cert.cofR)

/-- Monic rational-polynomial gcd. -/
def ratGcd (f h : DensePoly Rat) : DensePoly Rat :=
  let fInt := clearRat (ratDen f) f
  let hInt := clearRat (ratDen h) h
  let g := toRatPoly (gcd fInt hInt)
  if g.isZero then 0 else DensePoly.scale g.leadingCoeff⁻¹ g

/-! Small executable pins for the degenerate contracts and content handling. -/

-- Direct reference canaries.  These deliberately bypass dispatch so the
-- retained rational implementation remains useful as an independent oracle.

#guard
  let f : ZPoly := 0
  let h : ZPoly := 0
  let cert := checkedRationalGcdCert f h
  cert.gcd == 0 && checkGcd f h cert

-- The degenerate direct fallback and its checker also remain reducible in the
-- ordinary kernel while the definition is in scope.  Larger rational
-- Euclidean searches intentionally stay outside the replay closure.
example :
    checkGcd (0 : ZPoly) 0 (checkedRationalGcdCert 0 0) = true := by
  decide +kernel

#guard
  let f : ZPoly := DensePoly.ofList [2, 4, 2]
  let h : ZPoly := 0
  let cert := checkedRationalGcdCert f h
  cert.gcd == f && checkGcd f h cert

#guard
  let f : ZPoly := DensePoly.ofList [0, 12]
  let h : ZPoly := DensePoly.ofList [0, 18]
  let cert := checkedRationalGcdCert f h
  cert.gcd == DensePoly.ofList [0, 6] && checkGcd f h cert

#guard
  let common : ZPoly := DensePoly.ofList [1, 1]
  let f := common * DensePoly.ofList [2, 1]
  let h := common * DensePoly.ofList [3, 1]
  let cert := checkedRationalGcdCert f h
  cert.gcd == common && checkGcd f h cert

#guard gcd (0 : ZPoly) 0 == 0

#guard
  let two : ZPoly := DensePoly.C 2
  let twoX : ZPoly := DensePoly.ofList [0, 2]
  gcd two twoX == two

#guard
  let twelveX : ZPoly := DensePoly.ofList [0, 12]
  let eighteenX : ZPoly := DensePoly.ofList [0, 18]
  gcd twelveX eighteenX == DensePoly.ofList [0, 6]

#guard
  let f : ZPoly := DensePoly.ofList [0, 0, 0, 12, 12]
  let h : ZPoly := DensePoly.ofList [0, 0, 36, 18]
  match structuralReduction? f h with
  | none => false
  | some reduced =>
      reduced.factor == DensePoly.ofList [0, 0, 6] &&
        match restoreStructural? f h reduced
            (prsCert reduced.left reduced.right) with
        | some cert =>
            cert.gcd == DensePoly.ofList [0, 0, 6] && checkGcd f h cert
        | none => false

#guard
  let f : ZPoly := DensePoly.ofList [1, 1]
  let h : ZPoly := DensePoly.ofList [2, 1]
  isCoprime f h

#guard
  let common : ZPoly := DensePoly.ofList [1, 1]
  let f := common * DensePoly.ofList [2, 1]
  let h := common * DensePoly.ofList [3, 1]
  gcd f h == common && checkGcd f h (gcdCert f h)

#guard
  let common : ZPoly := DensePoly.ofList [2, 1]
  let f := common * DensePoly.ofList [1, 2]
  let h := common * DensePoly.ofList [1, 3]
  gcd f h == common &&
    checkCoprime (gcdCert f h).cofL (gcdCert f h).cofR
      (gcdCert f h).coprime

#guard
  let f : ZPoly := DensePoly.ofList [1, 1]
  let h : ZPoly := DensePoly.ofList [2, 1]
  (coprimeCert? f h).isSome

#guard
  let common : ZPoly := DensePoly.ofList [1, 1]
  let f := common * DensePoly.ofList [2, 1]
  let h := common * DensePoly.ofList [3, 1]
  (coprimeCert? f h).isNone

#guard
  let twoX : ZPoly := DensePoly.ofList [0, 2]
  let fourX : ZPoly := DensePoly.ofList [0, 4]
  gcdList [twoX, fourX] == twoX && lcm twoX fourX == fourX

#guard
  let f : DensePoly Rat := DensePoly.ofList [1, 2]
  let h : DensePoly Rat := DensePoly.ofList [2, 4]
  ratGcd f h == DensePoly.ofList [1 / 2, 1]

#guard
  let common : DensePoly Rat :=
    DensePoly.ofList [(1 : Rat) / 1000003, 1]
  let f := common * DensePoly.ofList [(1 : Rat) / 1000033, 1]
  let h := common * DensePoly.ofList [(1 : Rat) / 1000037, 1]
  ratGcd f h == common

#guard
  let common : DensePoly Rat :=
    DensePoly.ofList [-(1 : Rat) / 1000003, -1]
  let f := common * DensePoly.ofList [(1 : Rat) / 1000033, 1]
  let h := common * DensePoly.ofList [(1 : Rat) / 1000037, 1]
  ratGcd f h == DensePoly.ofList [(1 : Rat) / 1000003, 1]

end ZPoly

end Hex
