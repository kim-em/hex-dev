/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.CertificateBasisReplay
import HexGroebner.CertificateConformance

namespace Hex.Groebner.DivisionFixtures

structure Case where
  name : String
  context : Context
  generators : Array Certificate.Polynomial
  basis : Array Certificate.Polynomial
  certificate : Certificate.Basis

def cases : Array Case := Id.run do
  let c := CertificateConformance.context
  let mut output := #[
    ⟨"three/grevlex",c,CertificateConformance.generators,CertificateConformance.basis,
      CertificateConformance.basisWitness⟩,
    ⟨"three/grlex",{ c with order := .grlex },CertificateConformance.generators,
      CertificateConformance.basis,CertificateConformance.basisWitness⟩]
  for order in [TermOrder.lex,.grlex,.grevlex] do
    let ctx : Context := { c with order }
    let identity : Certificate.Basis := ⟨⟨[.generator 0],#[0]⟩,⟨[.generator 0],#[0]⟩,#[#[#[[]]]]⟩
    let x : Array Certificate.Polynomial := #[[([1,0],1)]]
    let one : Array Certificate.Polynomial := #[[([0,0],1)]]
    output := output.push ⟨s!"zero/{reprStr order}",ctx,#[],#[],⟨⟨[],#[]⟩,⟨[],#[]⟩,#[]⟩⟩
    output := output.push ⟨s!"unit/{reprStr order}",ctx,one,one,identity⟩
    output := output.push ⟨s!"linear/{reprStr order}",ctx,x,x,identity⟩
    let f2 : Context := ⟨⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩,1,order⟩
    let poly : Array Certificate.Polynomial := #[[([2],1),([1],1)]]
    output := output.push ⟨s!"ordinary-f2/{reprStr order}",f2,poly,poly,identity⟩
  return output

def dividend (p n seed : Nat) : Certificate.Polynomial :=
  (List.range 7).foldl (fun f i =>
    let exponents := (List.range n).map fun j =>
      ((seed+1)*1103515245+(i+3)*12345+(j+1)*69069+i*j*17)%4
    let coefficient := ((seed+1)*1103515245+(i+1)*12345+(i+3)^3*17+seed*i*69069+1)%p
    if coefficient == 0 then f else Hex.MvPoly.Kernel.addMod p f [(exponents,coefficient)]) []

def targets (c : Case) : Array Certificate.Polynomial :=
  ((Array.range 8).map (dividend c.context.field.modulus.toNat c.context.variables)) ++
    #[[],[ (List.replicate c.context.variables 0,1) ],c.generators[0]?.getD []]

end Hex.Groebner.DivisionFixtures
