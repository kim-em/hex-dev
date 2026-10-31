/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.DivisionFixtures
import HexGroebner.Membership

namespace Hex.Groebner.NormalFormTest

private def checked : Bool := Id.run do
  let mut positive := false
  let mut negative := false
  for c in DivisionFixtures.cases do
    let .checked receipt _ := Certificate.BasisVerification.verifyWith c.context {}
        c.generators c.basis c.certificate | return false
    for target in DivisionFixtures.targets c do
      let .success nf statistics := normalFormWith receipt {} target | return false
      match memberWith receipt {} target with
      | .member division certificate _ usage =>
        if usage.work != statistics.work+1 || usage.allocatedBytes != statistics.allocatedBytes+64 then return false
        positive := true
        if division.value.remainder != nf.value.remainder ||
            !checkMember receipt.context receipt.generators target certificate.witness then return false
      | .nonmember certificate usage =>
        if usage.work != statistics.work+1 || usage.allocatedBytes != statistics.allocatedBytes+64 then return false
        negative := true
        if certificate.witness.division.remainder != nf.value.remainder ||
            !checkNonmember receipt.context receipt.generators target certificate.witness then return false
      | _ => return false
  return positive && negative

#guard checked

private def nonGroebner : Bool := Id.run do
  let context := CertificateConformance.context
  let generators := CertificateConformance.generators
  let target := CertificateConformance.target
  let identity : Certificate.Basis := ⟨⟨[.generator 0,.generator 1],#[0,1]⟩,
    ⟨[.generator 0,.generator 1],#[0,1]⟩,#[#[#[[],[]],#[[],[]]],#[#[[],[]],#[[],[]]]]⟩
  let division : Certificate.Division := ⟨#[[],[]],target⟩
  return Certificate.checkDivision 7 2 .grevlex generators target division &&
    !checkNonmember context generators target ⟨generators,identity,division⟩

#guard nonGroebner

end Hex.Groebner.NormalFormTest
