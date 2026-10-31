/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.CertificateBasisReplay

namespace Hex.Groebner.Certificate.BasisReplayTest

private def context : Context :=
  ⟨⟨2, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 1, .grevlex⟩
private def generators : Array Polynomial := #[[([2],1),([1],1)]]
private def certificate : Basis :=
  ⟨⟨[.generator 0],#[0]⟩,⟨[.generator 0],#[0]⟩,#[#[#[[]]]]⟩

#guard match BasisVerification.verifyWith context {} generators generators certificate with
  | .checked value usage => value.polynomials == generators && usage.nodes == 2 && usage.pairs == 1
  | _ => false

private def exhausts (budget : Budget) (resource : Resource) : Bool :=
  match BasisVerification.verifyWith context budget generators generators certificate with
  | .exhausted actual state => actual == resource &&
      match BasisVerification.resumeWith {} state with
      | .checked _ final => final.work >= state.usage.work
      | _ => false
  | _ => false

#guard exhausts { work := 0 } .work
#guard exhausts { bytes := 0 } .bytes
#guard exhausts { terms := 0 } .terms
#guard exhausts { nodes := 0 } .nodes
#guard exhausts { pairs := 0 } .pairs
#guard exhausts { «variables» := 0 } .variables
#guard exhausts { exponentBits := 0 } .exponentBits

#guard match BasisVerification.verifyWith context {} generators generators
    { certificate with forward := ⟨[.generator 7],#[0]⟩ } with
  | .rejected _ => true
  | _ => false
#guard match BasisVerification.verifyWith context {} generators generators
    { certificate with pairs := #[] } with
  | .rejected _ => true
  | _ => false
#guard match BasisVerification.verifyWith context {} #[[([2],2)]] generators certificate with
  | .invalid 0 _ => true
  | _ => false

end Hex.Groebner.Certificate.BasisReplayTest

namespace Hex.Groebner.Certificate.BasisReplayTest

private def shared : Basis := { certificate with forward :=
  ⟨[.generator 0, .multiply [([1],1),([0],1)] 0, .add 1 1, .add 0 2, .scale 1 3],#[4]⟩ }

#guard match BasisVerification.verifyWith context {} generators generators shared with
  | .checked _ usage => usage.nodes == 6
  | _ => false
#guard match BasisVerification.verifyWith context {} generators generators
    { shared with forward := ⟨[.generator 0,.multiply [([1,0],1)] 0],#[1]⟩ } with
  | .rejected _ => true
  | _ => false
#guard match BasisVerification.verifyWith context {} generators generators
    { shared with forward := ⟨[.generator 0,.scale 2 0],#[1]⟩ } with
  | .rejected _ => true
  | _ => false
#guard match BasisVerification.verifyWith context {} #[] #[] ⟨⟨[],#[]⟩,⟨[],#[]⟩,#[]⟩ with
  | .checked _ _ => true
  | _ => false

end Hex.Groebner.Certificate.BasisReplayTest
