/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Membership
import HexGroebner.NormalForm
import HexGroebner.Division
import HexGroebner.CertificateBasisReplay

namespace Hex.Groebner.MembershipTest
open Hex.Groebner

private def context : Context := ⟨⟨2, Hex.Nat.isPrimeTrial_isPrime (by decide +kernel), by decide⟩, 1, .grevlex⟩
private def generators : Array Certificate.Polynomial := #[[([2],1),([1],1)]]
private def target : Certificate.Polynomial := [([2],1)]
private def basis : Certificate.Basis := ⟨⟨[.generator 0],#[0]⟩,⟨[.generator 0],#[0]⟩,#[#[#[[]]]]⟩
private def receipt : CheckedBasis := .ofCertificate context generators generators basis (by decide +kernel)

#guard match Certificate.BasisVerification.verifyWith context {} generators generators basis with
  | .checked value _ => value.polynomials == receipt.polynomials
  | _ => false

#guard match memberWith receipt {} target with
  | .nonmember _ _ => true
  | _ => false
#guard match memberWith receipt {} generators[0]! with
  | .member division certificate _ _ => division.value.quotients == #[[([0], 1)]] &&
      checkMember receipt.context receipt.generators generators[0]! certificate.witness
  | _ => false
#guard match memberWith receipt { work := 0 } target with
  | .exhausted .work _ => true
  | _ => false

private def finishBoundary : Bool := Id.run do
  let .success _ usage := normalFormWith receipt {} target | return false
  let .exhausted .work state := memberWith receipt { work := usage.work } target | return false
  if !state.stage.isRight then return false
  match resumeMemberWith {} state with
  | .nonmember _ final => return final.work > usage.work
  | _ => return false

#guard finishBoundary

end Hex.Groebner.MembershipTest

namespace Hex.Groebner.MembershipTest

private def positiveBoundary : Bool := Id.run do
  let .success _ division := normalFormWith receipt {} generators[0]! | return false
  let .exhausted .work state := memberWith receipt { work := division.work+1 } generators[0]! | return false
  if !state.stage.isRight then return false
  let .member _ certificate _ usage := resumeMemberWith {} state | return false
  if !checkMember receipt.context receipt.generators generators[0]! certificate.witness ||
      usage.work ≤ division.work then return false
  let .exhausted .nodes state := memberWith receipt { nodes := 0 } generators[0]! | return false
  match resumeMemberWith {} state with
  | .member _ certificate _ _ => return checkMember receipt.context receipt.generators generators[0]! certificate.witness
  | _ => return false

#guard positiveBoundary

end Hex.Groebner.MembershipTest
