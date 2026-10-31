/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.CertificateBasisReplay
import HexGroebner.CertificateConformance

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
#guard exhausts { allocatedBytes := 0 } .allocatedBytes
#guard exhausts { allocatedTerms := 0 } .allocatedTerms
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

namespace Hex.Groebner.Certificate.BasisCorpusTest
open Hex.Groebner.CertificateConformance

private def unbounded : Basis := { basisWitness with
  pairs := basisWitness.pairs.set! 0
    ((basisWitness.pairs[0]!).set! 1 #[[([0,1],1)],[([1,0],6)],[]]) }

private def corpus : List (Context × Array Polynomial × Array Polynomial × Basis) := [
  (context,generators,basis,basisWitness),
  ({ context with order := .lex },generators,basis,basisWitness),
  ({ context with field := ⟨11,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩ },generators,basis,basisWitness),
  (context,#[],basis,basisWitness),
  (context,generators,basis,{ basisWitness with forward := { basisWitness.forward with roots := #[0,1] } }),
  (context,generators,basis,{ basisWitness with backward := { basisWitness.backward with roots := #[0,0] } }),
  (context,generators,basis,{ basisWitness with forward := { basisWitness.forward with roots := #[0,1,99] } }),
  (context,generators,basis,{ basisWitness with forward := ⟨[.generator 7],#[0,0,0]⟩ }),
  (context,generators,basis,{ basisWitness with pairs := #[] }),
  (context,generators,basis,{ basisWitness with pairs := basisWitness.pairs.push basisWitness.pairs[0]! }),
  (context,generators,basis,{ basisWitness with pairs := basisWitness.pairs.set! 0 #[] }),
  (context,generators,basis,unbounded),
  (context,generators,nonreduced,nonreducedWitness),
  (context,generators,basis.reverse,basisWitness)]

#guard corpus.all fun (context,generators,basis,certificate) =>
  match BasisVerification.verifyWith context {} generators basis certificate with
  | .checked receipt _ => checkBasis context generators basis certificate && receipt.polynomials == basis
  | .rejected _ => !checkBasis context generators basis certificate
  | _ => false

#guard match BasisVerification.verifyWith context {} generators basis basisWitness with
  | .checked _ usage => usage.pairs == 9 && usage.nodes == 8
  | _ => false

end Hex.Groebner.Certificate.BasisCorpusTest

namespace Hex.Groebner.Certificate.BasisCorpusTest

private def larger : Bool := Id.run do
  let n := 16
  let ctx : Context := ⟨Hex.Groebner.CertificateConformance.context.field,n,.grevlex⟩
  let basis : Array Polynomial := (Array.range n).map fun i =>
    [((List.range n).map fun j => if i == j then 1 else 0,1)]
  let nodes := (List.range n).map Node.generator
  let roots := Array.range n
  let certificate : Basis := ⟨⟨nodes,roots⟩,⟨nodes,roots⟩,
    Array.replicate n (Array.replicate n (Array.replicate n []))⟩
  match BasisVerification.verifyWith ctx {} basis basis certificate with
  | .checked _ usage => return usage.pairs == n*n && usage.nodes == 2*n
  | _ => return false

#guard larger

end Hex.Groebner.Certificate.BasisCorpusTest

namespace Hex.Groebner.Certificate.BasisCorpusTest
open Hex.Groebner.CertificateConformance

private def pairResume : Bool := Id.run do
  let parent : Usage := { nodes := 2, pairs := 3 }
  let .checked _ total := BasisVerification.verifyFrom context {} generators basis basisWitness parent
    | return false
  let budget : Budget := { work := total.work-1, nodes := total.nodes, pairs := total.pairs }
  let .exhausted .work state := BasisVerification.verifyFrom context budget generators basis basisWitness parent
    | return false
  if state.usage.nodes != total.nodes || state.usage.pairs == parent.pairs then return false
  match BasisVerification.resumeWith { nodes := total.nodes, pairs := total.pairs } state with
  | .checked receipt final => return receipt.polynomials == basis && final.nodes == total.nodes &&
      final.pairs == total.pairs && final.work >= state.usage.work
  | _ => return false

#guard pairResume

end Hex.Groebner.Certificate.BasisCorpusTest

namespace Hex.Groebner.Certificate.BasisCorpusTest
open Hex.Groebner.CertificateConformance

private def allResume : Bool := Id.run do
  let .checked _ total := BasisVerification.verifyWith context {} generators basis basisWitness
    | return false
  let full : Budget := { nodes := total.nodes, pairs := total.pairs }
  for work in [:total.work+1] do
    match BasisVerification.verifyWith context { full with work } generators basis basisWitness with
    | .checked _ usage => if usage.nodes != total.nodes || usage.pairs != total.pairs then return false
    | .exhausted .work state =>
      match BasisVerification.resumeWith full state with
      | .checked _ usage =>
        if usage.nodes != total.nodes || usage.pairs != total.pairs || usage.work < state.usage.work then return false
      | _ => return false
    | _ => return false
  return true

#guard allResume

end Hex.Groebner.Certificate.BasisCorpusTest
