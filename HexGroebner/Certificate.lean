/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Runtime
public import HexMvPoly.KernelResidue

@[expose] public section

/-! Shared exact ideal-membership derivations. Certificate polynomials use the
existing descending-lex kernel term lists, independently of the computation's
selected monomial order. Only the leading-term obligations of a complete basis
certificate depend on that order. These identities alone make no Gröbner claim.
-/

namespace Hex.Groebner
namespace Certificate

abbrev Polynomial := Hex.MvPoly.Kernel.PolyList Nat

/-- Acyclic arithmetic node. References address earlier evaluated nodes;
`generator` addresses the original generator array. Factors use the same
canonical natural-residue encoding as all certificate polynomials. -/
inductive Node where
  | zero
  | generator (index : Nat)
  | add (left right : Nat)
  | scale (coefficient source : Nat)
  | multiply (factor : Polynomial) (source : Nat)
  deriving Repr, BEq, Inhabited

/-- Shared derivation with an explicit result reference. An empty derivation
has no result, including for zero; use the `zero` node to prove zero membership. -/
structure Derivation where
  nodes : List Node
  root : Nat
  deriving Repr, BEq, Inhabited

/-- Evaluate one node against previously evaluated nodes. Invalid indices,
noncanonical scalar residues or noncanonical factors are rejected. -/
def evaluate (p n : Nat) (generators values : Array Polynomial) : Node → Option Polynomial
  | .zero => some []
  | .generator index => generators[index]?
  | .add left right => do
    let a ← values[left]?
    let b ← values[right]?
    return Hex.MvPoly.Kernel.addMod p a b
  | .scale coefficient source => do
    if coefficient ≥ p then none else
      let a ← values[source]?
      return Hex.MvPoly.Kernel.smulMod p coefficient a
  | .multiply factor source => do
    if !Hex.MvPoly.Kernel.isCanonicalMod p n factor then none else
      let a ← values[source]?
      return Hex.MvPoly.Kernel.mulMod p factor a

/-- Evaluate a derivation in order, sharing every previously computed polynomial.
A reference to the current or a later node is out of bounds and rejected. -/
def replay (p n : Nat) (generators : Array Polynomial) :
    List Node → Array Polynomial → Option (Array Polynomial)
  | [], values => some values
  | node :: nodes, values => do
    let value ← evaluate p n generators values node
    replay p n generators nodes (values.push value)

end Certificate

/-- Independently replay a positive ideal-membership witness. Input polynomials,
the target and every explicit multiplication factor must be canonical residue
term lists. Acceptance proves a formal polynomial identity, without requiring
or claiming a complete Gröbner basis. -/
def checkDerivation (context : Context) (generators : Array Certificate.Polynomial)
    (target : Certificate.Polynomial) (certificate : Certificate.Derivation) : Bool :=
  let p := context.field.modulus.toNat
  let n := context.variables
  if !generators.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      !Hex.MvPoly.Kernel.isCanonicalMod p n target then false else
    match Certificate.replay p n generators certificate.nodes #[] with
    | none => false
    | some values => match values[certificate.root]? with
      | none => false
      | some value => Hex.MvPoly.Kernel.beq value target

end Hex.Groebner
