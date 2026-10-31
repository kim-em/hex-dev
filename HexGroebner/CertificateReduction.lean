/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificatePair

@[expose] public section

namespace Hex.Groebner.Certificate

/-- Compare polynomial degrees with a separate bottom value for zero. -/
def degreeLE (order : TermOrder) (f g : Polynomial) : Bool :=
  match leading order f, leading order g with
  | none, _ => true
  | some _, none => false
  | some a, some b => (compare order a.1 b.1).isLE

/-- Sum canonical residue polynomials with a tail-recursive accumulator,
without changing their storage order. -/
def sum (p : Nat) (rows : List Polynomial) : Polynomial :=
  rows.foldl (Hex.MvPoly.Kernel.addMod p) []

/-- Actual products for a cofactor representation, in basis order. Missing
cofactors denote zero internally; the checker rejects a mismatched array size. -/
def products (p : Nat) (basis cofactors : Array Polynomial) : List Polynomial :=
  List.ofFn fun i : Fin basis.size =>
    Hex.MvPoly.Kernel.mulMod p (cofactors[i.val]?.getD []) basis[i]

/-- Check an exact zero-remainder representation, including the essential
degree bound on every cofactor-times-divisor product. Unlike unrestricted
ideal membership, this is suitable for Buchberger's criterion. This pure
predicate performs no candidate production or native-only operation. -/
def checkReduction (p n : Nat) (order : TermOrder) (basis cofactors : Array Polynomial)
    (target : Polynomial) : Bool :=
  if basis.size != cofactors.size ||
      !basis.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      !cofactors.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      !Hex.MvPoly.Kernel.isCanonicalMod p n target then false else
    let rows := products p basis cofactors
    rows.all (fun row => degreeLE order row target) &&
      Hex.MvPoly.Kernel.beq (sum p rows) target

end Hex.Groebner.Certificate
