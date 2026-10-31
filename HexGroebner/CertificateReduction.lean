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

/-- Degree comparison with a previously computed target leading term. -/
def degreeLELeading (order : TermOrder) (head target : Option (List Nat × Nat)) : Bool :=
  match head,target with
  | none,_ => true
  | some _,none => false
  | some a,some b => (compare order a.1 b.1).isLE

theorem degreeLELeading_eq (order : TermOrder) (f g : Polynomial) :
    degreeLELeading order (leading order f) (leading order g) = degreeLE order f g := rfl

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
    let targetHead := leading order target
    rows.all (fun row => degreeLELeading order (leading order row) targetHead) &&
      Hex.MvPoly.Kernel.beq (sum p rows) target

/-- Pair replay requiring a separately validated canonical basis. Public
entrypoints `checkReduction` and `checkPairs` perform that validation. -/
def checkReductionCore (p n : Nat) (order : TermOrder)
    (basis cofactors : Array Polynomial) (target : Polynomial) : Bool :=
  if basis.size != cofactors.size ||
      !cofactors.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) ||
      !Hex.MvPoly.Kernel.isCanonicalMod p n target then false else
    let rows := products p basis cofactors
    let targetHead := leading order target
    rows.all (fun row => degreeLELeading order (leading order row) targetHead) &&
      Hex.MvPoly.Kernel.beq (sum p rows) target

private theorem checkReductionCore_eq (p n : Nat) (order : TermOrder)
    (basis cofactors : Array Polynomial) (target : Polynomial)
    (h : basis.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true) :
    checkReductionCore p n order basis cofactors target =
      checkReduction p n order basis cofactors target := by
  simp [checkReductionCore, checkReduction, h]

/-- Every final S-polynomial must have a checked bounded zero representation.
Common basis canonicality is checked once for the entire pair family. -/
def checkPairs (p n : Nat) (order : TermOrder) (basis : Array Polynomial)
    (pairs : Array (Array (Array Polynomial))) : Bool :=
  let heads := basis.map (leading order)
  basis.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) &&
    pairs.size == basis.size && pairs.toList.all (fun row => row.size == basis.size) &&
    (List.finRange basis.size).all fun i => (List.finRange basis.size).all fun j =>
      match pairs[i.val]?.bind (fun row => row[j.val]?) with
      | none => false
      | some cofactors => checkReductionCore p n order basis cofactors
        (sPolynomialHeads p basis[i] basis[j]
          (heads[i.val]'(by simp [heads])) (heads[j.val]'(by simp [heads])))

/-- Cached validation preserves full independent reduction checking for every
pair. This equation is also the pure boundary used by the soundness proof. -/
theorem checkPairs_eq (p n : Nat) (order : TermOrder) (basis : Array Polynomial)
    (pairs : Array (Array (Array Polynomial)))
    (h : basis.toList.all (Hex.MvPoly.Kernel.isCanonicalMod p n) = true) :
    checkPairs p n order basis pairs =
      (pairs.size == basis.size && pairs.toList.all (fun row => row.size == basis.size) &&
        (List.finRange basis.size).all fun i => (List.finRange basis.size).all fun j =>
          match pairs[i.val]?.bind (fun row => row[j.val]?) with
          | none => false
          | some cofactors => checkReduction p n order basis cofactors
            (sPolynomial p order basis[i] basis[j])) := by
  simp only [checkPairs, h, Bool.true_and, checkReductionCore_eq p n order basis _ _ h,
    Array.getElem_map, Fin.getElem_fin, sPolynomialHeads_eq]

end Hex.Groebner.Certificate
