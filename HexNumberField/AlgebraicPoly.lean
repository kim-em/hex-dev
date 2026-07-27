/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Disambiguate
public meta import HexNumberField.Disambiguate

public section

/-!
Polynomials with canonical algebraic coefficients.

This representation owns semantic trailing-zero normalization. In particular,
the Mathlib-free layer never instantiates `DensePoly AlgebraicNumber`: its
normalizer would require a kernel `DecidableEq`, while canonical algebraic
equality is intentionally exposed here only through checked Boolean equality.
-/
namespace Hex

/-- A coefficient array has no trailing semantic zero. This erased invariant
is carried by `AlgebraicPoly` so downstream correctness theorems may quantify
over every value, rather than only values visibly built by `ofArray`. -/
@[expose]
def AlgebraicPolyNormalized (coeffs : Array AlgebraicNumber) : Prop :=
  match coeffs.toList.reverse.head? with
  | some a => a.isZero = false
  | none => True

/-- A semantically normalized polynomial with canonical algebraic
coefficients. Construction is sealed so every stored array has had its
trailing semantic zeros removed. -/
structure AlgebraicPoly where
  private mk ::
  data : Array AlgebraicNumber
  normalized : AlgebraicPolyNormalized data

namespace AlgebraicPoly

private theorem normalized_popWhile (coeffs : Array AlgebraicNumber) :
    AlgebraicPolyNormalized (coeffs.popWhile fun a => a.isZero) := by
  change
    match
        (coeffs.popWhile fun a => a.isZero).toList.reverse.head? with
    | some a => a.isZero = false
    | none => True
  rw [← Array.toArray_toList (xs := coeffs)]
  simp only [List.popWhile_toArray, List.toList_toArray,
    List.reverse_reverse]
  have h := List.head?_dropWhile_not
    (fun a : AlgebraicNumber => a.isZero) coeffs.toList.reverse
  split at * <;> simp_all

/-- Construct a polynomial and remove all trailing coefficients whose
canonical minimal polynomial is `X`. -/
def ofArray (coeffs : Array AlgebraicNumber) : AlgebraicPoly :=
  .mk (coeffs.popWhile fun a => a.isZero) (normalized_popWhile coeffs)

/-- The normalized coefficient array, in increasing degree order. -/
@[expose]
def coeffs (f : AlgebraicPoly) : Array AlgebraicNumber :=
  f.data

/-- Number of stored coefficients. -/
@[expose]
def size (f : AlgebraicPoly) : Nat :=
  f.data.size

/-- Coefficient at degree `n`, defaulting to canonical zero. -/
@[expose]
def coeff (f : AlgebraicPoly) (n : Nat) : AlgebraicNumber :=
  f.data.getD n 0

/-- Semantic zero test. -/
@[expose]
def isZero (f : AlgebraicPoly) : Bool :=
  f.data.isEmpty

/-- Degree of a nonzero polynomial. -/
@[expose]
def degree? (f : AlgebraicPoly) : Option Nat :=
  if f.isZero then none else some (f.size - 1)

/-- Canonical coefficientwise Boolean equality. -/
@[expose]
def beq (f g : AlgebraicPoly) : Bool :=
  f.data == g.data

instance : BEq AlgebraicPoly := ⟨beq⟩

/-! Compiled semantic-normalization checks. -/

#guard
    let z := AlgebraicNumber.zero
    let f := ofArray #[z, z, z]
    f.isZero && f.coeffs.isEmpty && f.degree? = none

#guard
    let z := AlgebraicNumber.zero
    let f := ofArray #[]
    let g := ofArray #[z]
    f == g && (f.coeff 17).isZero

end AlgebraicPoly
end Hex
