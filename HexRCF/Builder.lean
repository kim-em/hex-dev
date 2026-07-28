/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.CarrierCheck
public import HexRCF.CommonRootCheck
public import HexRCF.SignMatrixCheck
public import HexRCF.SturmBuilder

public section

/-!
# Compiled arithmetic preparation for RCF certificates

This module performs the rational gcd, division, and denominator-clearing work
that must remain outside kernel replay. Every public builder retains a candidate
only after its multiplication-only checker accepts it.
-/

namespace Hex.RCF

/-- A common positive denominator for all coefficients. -/
private def ratCommonDen (p : DensePoly Rat) : Nat :=
  p.toArray.foldl (fun den q => Nat.lcm den q.den) 1

/-- Clear one rational coefficient at a known common denominator. -/
private def clearRatCoeff (den : Nat) (q : Rat) : Int :=
  q.num * Int.ofNat (den / q.den)

/-- Clear all denominators and return the positive scale and integer
polynomial. -/
private def clearRatPoly (p : DensePoly Rat) : Int × ZPoly :=
  let den := ratCommonDen p
  (Int.ofNat den,
    DensePoly.ofCoeffs (p.toArray.map (clearRatCoeff den)))

/-- Clear a rational polynomial at an externally chosen common denominator. -/
private def clearRatPolyAt (den : Nat) (p : DensePoly Rat) : ZPoly :=
  DensePoly.ofCoeffs (p.toArray.map (clearRatCoeff den))

/-- Convert a rational polynomial whose coefficients are already integral. -/
private def ratPolyToZ? (p : DensePoly Rat) : Option ZPoly :=
  if p.toArray.all (fun q => q.den == 1) then
    some (DensePoly.ofCoeffs (p.toArray.map (fun q => q.num)))
  else none

/-- Recover the signed content relating the square-free decomposition product
to the original atom product. -/
private def factorScale? (q core repeated : ZPoly) : Option Int :=
  let content := ZPoly.content q
  if DensePoly.beqCoeffs q
      (DensePoly.scale content (core * repeated)) then some content
  else if DensePoly.beqCoeffs q
      (DensePoly.scale (-content) (core * repeated)) then some (-content)
  else none

/-- Build a square-free carrier and retain it only after the kernel-facing
checker accepts all multiplication identities and the generalized replay. -/
def buildCarrier? (s : Sentence) : Option CarrierCert :=
  let q := s.product
  let decomposition := ZPoly.primitiveSquareFreeDecomposition q
  let core := decomposition.squareFreeCore
  let repeated := decomposition.repeatedPart
  match factorScale? q core repeated with
  | none => none
  | some factorScale =>
      let derivativeQuotient :=
        ZPoly.toRatPoly (DensePoly.derivative q) / ZPoly.toRatPoly repeated
      let (derivScale, derivPart) := clearRatPoly derivativeQuotient
      match buildSturmReplay? core with
      | none => none
      | some replay =>
          let cert : CarrierCert := {
            carrier := core
            repeated
            derivPart
            factorScale
            derivScale
            replay }
          if cert.check s then some cert else none

/-- Every carrier emitted by compiled preparation has passed its checker. -/
theorem check_buildCarrier {s : Sentence} {cert : CarrierCert}
    (h : buildCarrier? s = some cert) : cert.check s = true := by
  unfold buildCarrier? at h
  dsimp only at h
  split at h <;> rename_i hfactor
  · simp at h
  · split at h <;> rename_i hreplay
    · simp at h
    · split at h <;> rename_i hcheck
      · cases Option.some.inj h
        exact hcheck
      · simp at h

/-- One denominator clearing both Bezout coefficients and the rational unit
relating the executable rational gcd to its primitive integer representative. -/
private def commonDen3 (left right : DensePoly Rat) (unit : Rat) : Nat :=
  Nat.lcm (Nat.lcm (ratCommonDen left) (ratCommonDen right)) unit.den

/-- Constants need no replay. Nonconstant common-root polynomials do. -/
private def buildGcdReplay? (gcd : ZPoly) : Option (Option SturmReplay) :=
  if gcd.size = 1 then some none
  else (buildSturmReplay? gcd).map some

/-- Build one common-root package by rational extended gcd and retain it only
after all divisibility, scaled Bezout, and replay checks pass. -/
def buildCommonRoot? (atom carrier : ZPoly) : Option CommonRootCert :=
  let atomRat := ZPoly.toRatPoly atom
  let carrierRat := ZPoly.toRatPoly carrier
  let result := DensePoly.xgcd atomRat carrierRat
  let gcd := ZPoly.ratPolyPrimitivePart result.gcd
  if gcd.isZero then none
  else
    let gcdRat := ZPoly.toRatPoly gcd
    match ratPolyToZ? (atomRat / gcdRat),
        ratPolyToZ? (carrierRat / gcdRat) with
    | some atomFactor, some carrierFactor =>
        let unit := DensePoly.leadingCoeff result.gcd /
          ((DensePoly.leadingCoeff gcd : Int) : Rat)
        let den := commonDen3 result.left result.right unit
        let scaleRat := (den : Rat) * unit
        if scaleRat.den != 1 then none
        else
          match buildGcdReplay? gcd with
          | none => none
          | some replay =>
              let cert : CommonRootCert := {
                gcd
                atomFactor
                carrierFactor
                atomCoeff := clearRatPolyAt den result.left
                carrierCoeff := clearRatPolyAt den result.right
                scale := scaleRat.num
                replay }
              if cert.check atom carrier then some cert else none
    | _, _ => none

/-- Every common-root package emitted by compiled preparation has passed its
checker against the external atom and carrier. -/
theorem check_buildCommonRoot {atom carrier : ZPoly} {cert : CommonRootCert}
    (h : buildCommonRoot? atom carrier = some cert) :
    cert.check atom carrier = true := by
  unfold buildCommonRoot? at h
  dsimp only at h
  split at h <;> rename_i hgcd
  · simp at h
  · split at h <;> rename_i hfactors
    · split at h <;> rename_i hscale
      · simp at h
      · split at h <;> rename_i hreplay
        · simp at h
        · split at h <;> rename_i hcheck
          · cases Option.some.inj h
            exact hcheck
          · simp at h
    · simp at h

/-- Build common-root packages in a prescribed polynomial order, failing if
any individual package cannot be constructed and checked. -/
private def buildCommonRootsFrom? (carrier : ZPoly) :
    List ZPoly → Option (List CommonRootCert)
  | [] => some []
  | atom :: atoms => do
      let common ← buildCommonRoot? atom carrier
      let commons ← buildCommonRootsFrom? carrier atoms
      some (common :: commons)

/-- Successful list preparation produces packages aligned with and accepted
against every polynomial in the supplied order. -/
private theorem check_buildCommonRootsFrom {carrier : ZPoly} {atoms : List ZPoly}
    {commons : List CommonRootCert}
    (h : buildCommonRootsFrom? carrier atoms = some commons) :
    checkCommon carrier atoms commons = true := by
  induction atoms generalizing commons with
  | nil =>
      simp [buildCommonRootsFrom?] at h
      subst commons
      rfl
  | cons atom atoms ih =>
      simp only [buildCommonRootsFrom?] at h
      obtain ⟨common, hcommon, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail, htail, hpure⟩ := Option.bind_eq_some_iff.mp hrest
      cases Option.some.inj hpure
      simp only [checkCommon, Bool.and_eq_true]
      exact ⟨check_buildCommonRoot hcommon, ih htail⟩

/-- Build one checker-retained common-root package per distinct nonconstant
sentence polynomial, in the exact order expected by the sign-matrix checker. -/
def buildCommonRoots? (s : Sentence) (carrier : ZPoly) :
    Option (List CommonRootCert) :=
  buildCommonRootsFrom? carrier (dedupPolys s.polys)

/-- Every emitted common-root list passes the sign-matrix alignment checker
against the recomputed distinct polynomial order. -/
theorem check_buildCommonRoots {s : Sentence} {carrier : ZPoly}
    {commons : List CommonRootCert}
    (h : buildCommonRoots? s carrier = some commons) :
    checkCommon carrier (dedupPolys s.polys) commons = true := by
  exact check_buildCommonRootsFrom h

end Hex.RCF
