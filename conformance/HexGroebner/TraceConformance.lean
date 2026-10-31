/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Producer.Compute
import HexGroebner.F4Fixtures

open Hex.Groebner

private def check : Bool := Id.run do
  let field : PrimeField := ⟨7,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let context : Context := ⟨field,2,.grevlex⟩
  let generators : Array RawPolynomial := #[#[⟨#[2,0],1⟩,⟨#[0,1],6⟩],#[⟨#[1,1],1⟩,⟨#[0,0],6⟩]]
  let .candidate value _ := Producer.computeWith context {} 1000000 generators | return false
  return Certificate.checkContainment 7 2 value.generators value.polynomials value.forward

#guard check

private def canonical (p : Nat) (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f term => if term.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod p f [(term.exponents.toList,term.coefficient.toNat)]) []

private def corpus : Bool := Id.run do
  for field in Fixtures.fields do
    for order in [TermOrder.lex,.grlex,.grevlex] do
      let names := ["missing-s-pair", "cyclic-3", "ordinary-f2", "nonmonic",
        "positive-dimensional", "inhomogeneous"]
      let cases := F4Fixtures.cases field
      if !names.all (fun name => cases.any (fun c => c.name == name)) then return false
      for c in cases.filter (fun c => names.contains c.name) do
        for batchInterreduce in [false, true] do
          let context : Context := ⟨field,c.variables,order⟩
          let .candidate expected _ := computeWith context { batchInterreduce } c.generators | return false
          let .candidate actual _ := Producer.computeWith context { batchInterreduce } 1000000 c.generators | return false
          if actual.polynomials != expected.polynomials.map (canonical field.modulus.toNat) ||
              !Certificate.checkContainment field.modulus.toNat c.variables actual.generators
                actual.polynomials actual.forward then return false
  return true

#guard corpus

private def pruneExample : Bool :=
  match (Producer.prune {} #[.generator 0, .zero, .scale 1 0, .add 2 1] #[2]).run
      ⟨⟨{ arity := 0 }, {}⟩, {}⟩ with
  | (.ok value, _) => value.nodes == [.generator 0, .scale 1 0] && value.roots == #[1]
  | _ => false

#guard pruneExample
#guard match (Producer.prune {} #[.scale 1 1, .zero] #[0]).run
    ⟨⟨{ arity := 0 }, {}⟩, {}⟩ with
  | (.error (.matrix .dimensions), _) => true
  | _ => false
#guard match (Producer.prune {} #[.zero] #[1]).run
    ⟨⟨{ arity := 0 }, {}⟩, {}⟩ with
  | (.error (.matrix .dimensions), _) => true
  | _ => false

/- A matrix input record can reuse a root even when no new node slots remain. -/
#guard match Producer.computeWith
    ⟨⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 1, .lex⟩ {} 1
    #[#[⟨#[1], 1⟩]] with
  | .candidate value _ => value.forward.nodes == [.generator 0]
  | _ => false
