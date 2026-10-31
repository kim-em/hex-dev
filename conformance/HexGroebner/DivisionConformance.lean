/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.CertificateDivision

namespace Hex.Groebner.Certificate.DivisionTest

def context : Context :=
  ⟨⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 2, .grevlex⟩

def divisors : Array Polynomial := #[
  [([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)],
  [([1, 0], 6), ([0, 2], 1)]]

def input : Polynomial := [([3, 0], 2), ([1, 1], 3), ([0, 3], 4), ([0, 0], 5)]

def valid (context : Context) (divisors : Array Polynomial) (input : Polynomial)
    (result : Division) : Bool :=
  let p := context.field.modulus.toNat
  result.quotients.size == divisors.size &&
    result.quotients.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p context.variables) &&
    Hex.MvPoly.Kernel.isCanonicalMod p context.variables result.remainder &&
    Hex.MvPoly.Kernel.beq
      (Hex.MvPoly.Kernel.addMod p (sum p (products p divisors result.quotients)) result.remainder) input &&
    result.remainder.all fun term => divisors.toList.all fun divisor =>
      match leading context.order divisor with
      | none => true
      | some head => !divides head.1 term.1

def check (context : Context) (divisors : Array Polynomial) (input : Polynomial) : Bool :=
  match Division.computeWith context {} divisors input with
  | .candidate result _ => valid context divisors input result
  | _ => false

#guard check context divisors input
#guard check context (divisors.extract 0 2) input
#guard check { context with order := .lex } divisors input
#guard check context #[] input
#guard check context #[[], []] input
#guard check context #[[([2, 0], 3), ([0, 1], 4)]] [([2, 0], 1), ([0, 1], 6)]
#guard match Division.computeWith context {} #[[([2, 0], 3), ([0, 1], 4)]]
    [([2, 0], 1), ([0, 1], 6)] with
  | .candidate r _ => r.quotients == #[[([0, 0], 5)]] && r.remainder.isEmpty
  | _ => false

#guard check ⟨context.field, 0, .grevlex⟩ #[[([], 2)]] [([], 3)]
#guard match Division.computeWith
    ⟨⟨2, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 1, .grevlex⟩ {}
    #[[([2], 1), ([1], 1)]] [([2], 1)] with
  | .candidate r _ => r.remainder == [([1], 1)]
  | _ => false

#guard match Division.computeWith context {} #[[([0], 1)]] [] with
  | .invalid 0 _ => true
  | _ => false
#guard match Division.computeWith context {} #[] [([0, 0], 7)] with
  | .invalid 0 _ => true
  | _ => false

private def resumeChecks : Bool := Id.run do
  let .candidate expected usage := Division.computeWith context {} divisors input | return false
  if !valid context divisors input expected then return false
  let mut prefixes := false
  for work in [:usage.work + 1] do
    match Division.computeWith context { work } divisors input with
    | .candidate result _ =>
      if result.quotients != expected.quotients || result.remainder != expected.remainder then return false
    | .exhausted .work state =>
      prefixes := prefixes || state.checkpoint.isSome
      match Division.resumeWith {} state with
      | .candidate result final =>
        if result.quotients != expected.quotients || result.remainder != expected.remainder ||
            final.work < state.usage.work then return false
      | _ => return false
    | _ => return false
  return prefixes

#guard resumeChecks

end Hex.Groebner.Certificate.DivisionTest

namespace Hex.Groebner.Certificate.DivisionTest

private def exhausts (budget : Budget) (resource : Resource) : Bool :=
  match Division.computeWith context budget divisors input with
  | .exhausted actual state => actual == resource &&
      match Division.resumeWith {} state with
      | .candidate result _ => valid context divisors input result
      | _ => false
  | _ => false

#guard exhausts { work := 0 } .work
#guard exhausts { bytes := 0 } .bytes
#guard exhausts { terms := 0 } .terms
#guard exhausts { steps := 0 } .steps
#guard exhausts { variables := 1 } .variables
#guard exhausts { exponentBits := 0 } .exponentBits

private def wide : Nat := 2^80
private def wideContext : Context := { context with variables := 1 }
private def wideDivisors : Array Polynomial := #[[([wide], 1), ([0], 1)]]
private def wideDividend : Polynomial := [([wide+1], 3), ([1], 3)]

#guard match Division.computeWith wideContext { exponentBits := 128 }
    wideDivisors wideDividend with
  | .candidate r _ => r.quotients == #[[([1], 3)]] && r.remainder.isEmpty
  | _ => false

#guard match Division.computeWith wideContext {} wideDivisors wideDividend with
  | .exhausted .exponentBits state =>
      match Division.resumeWith { exponentBits := 128 } state with
      | .candidate r _ => r.quotients == #[[([1], 3)]] && r.remainder.isEmpty
      | _ => false
  | _ => false

#guard match Division.computeWith context { steps := 1 } divisors input with
  | .exhausted .steps state =>
      match Division.resumeWith { work := 0 } state with
      | .exhausted .work retained => retained.usage == state.usage
      | _ => false
  | _ => false

end Hex.Groebner.Certificate.DivisionTest

namespace Hex.Groebner.Certificate.DivisionTest

#guard match (reserveBytes { bytes := USize.size } USize.size).run {} with
  | (.error .address,usage) => usage.bytes == 0
  | _ => false
#guard match (reserve { bytes := USize.size*2,terms := USize.size } 1 USize.size).run {} with
  | (.error (.exhausted .bytes),usage) => usage.bytes == 0 && usage.terms == 0
  | _ => false

end Hex.Groebner.Certificate.DivisionTest
