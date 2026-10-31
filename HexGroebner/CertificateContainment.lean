/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Certificate

@[expose] public section

namespace Hex.Groebner.Certificate

/-- One shared derivation for an entire ideal containment. Roots correspond
exactly to the target array; every node is evaluated once. -/
structure Containment where
  nodes : List Node
  roots : Array Nat
  deriving Repr, Inhabited

/-- Replay a shared derivation and compare every target with its explicit root.
Malformed references, noncanonical polynomials and mismatched root counts fail. -/
def checkContainment (p n : Nat) (generators targets : Array Polynomial)
    (certificate : Containment) : Bool :=
  if !generators.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      !targets.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      certificate.roots.size != targets.size then false else
    match replay p n generators certificate.nodes #[] with
    | none => false
    | some values => (List.finRange targets.size).all fun i =>
      match values[certificate.roots[i.val]?.getD values.size]? with
      | none => false
      | some value => Hex.MvPoly.Kernel.beq value targets[i]

end Hex.Groebner.Certificate
