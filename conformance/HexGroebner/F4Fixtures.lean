/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexGroebner.Fixtures

namespace Hex.Groebner.F4Fixtures

/-- A raw system fixes variable order before selecting a monomial order. -/
structure Case where
  name : String
  variables : Nat
  generators : Array RawPolynomial

private def polynomial (p : UInt64) (terms : Array (Int × Array Nat)) : RawPolynomial :=
  terms.map fun (c, exponents) => ⟨exponents, (c % (p.toNat : Int)).toNat.toUInt64⟩

/-- Independent-oracle inputs include inhomogeneous, homogeneous, positive-
dimensional, inconsistent and ordinary characteristic-two polynomial systems. -/
def cases (field : PrimeField) : Array Case := Id.run do
  let poly := polynomial field.modulus
  let classic := #[poly #[(1, #[2, 0]), (-1, #[0, 1])], poly #[(1, #[1, 1]), (-1, #[0, 0])]]
  let mut cases := #[
    ⟨"empty", 2, #[]⟩,
    ⟨"zero-variable-zero", 0, #[#[]]⟩,
    ⟨"zero-variable-unit", 0, #[poly #[(1, #[])]]⟩,
    ⟨"constant-unit", 2, #[poly #[(1, #[0, 0])], classic[0]!]⟩,
    ⟨"missing-s-pair", 2, classic⟩,
    ⟨"duplicates", 2, classic ++ classic ++ #[#[]]⟩,
    ⟨"nonmonic", 2, #[poly #[(2, #[2, 0]), (3, #[0, 1]), (-1, #[0, 0])],
      poly #[(3, #[1, 1]), (-2, #[1, 0]), (2, #[0, 0])]]⟩,
    ⟨"positive-dimensional", 3, #[poly #[(1, #[1, 1, 0])], poly #[(1, #[1, 0, 1])]]⟩,
    ⟨"redundant-leading", 2, #[poly #[(1, #[2, 0])], poly #[(1, #[1, 1])], poly #[(1, #[1, 0])]]⟩,
    ⟨"inhomogeneous", 2, #[poly #[(1, #[2, 0]), (1, #[0, 2]), (-1, #[0, 0])],
      poly #[(1, #[3, 0]), (-1, #[0, 1])]]⟩,
    ⟨"cyclic-3", 3, #[
      poly #[(1, #[1, 0, 0]), (1, #[0, 1, 0]), (1, #[0, 0, 1])],
      poly #[(1, #[1, 1, 0]), (1, #[0, 1, 1]), (1, #[1, 0, 1])],
      poly #[(1, #[1, 1, 1]), (-1, #[0, 0, 0])]]⟩,
    ⟨"katsura-2", 3, #[
      poly #[(1, #[1, 0, 0]), (2, #[0, 1, 0]), (2, #[0, 0, 1]), (-1, #[0, 0, 0])],
      poly #[(1, #[2, 0, 0]), (2, #[0, 2, 0]), (2, #[0, 0, 2]), (-1, #[1, 0, 0])],
      poly #[(2, #[1, 1, 0]), (2, #[0, 1, 1]), (-1, #[0, 1, 0])]]⟩,
    ⟨"ordinary-f2", 2, #[poly #[(1, #[2, 0]), (1, #[0, 1])], poly #[(1, #[0, 2]), (1, #[1, 0])]]⟩,
    ⟨"wide-exponent", 1, #[poly #[(1, #[256]), (-1, #[1])]]⟩,
    ⟨"raw-cancellation", 2, #[poly #[(1, #[4, 2]), (-1, #[4, 2]), (1, #[0, 1])],
      poly #[(1, #[2, 0]), (-1, #[0, 1])]]⟩]
  let support : Array (Array Nat) := #[#[2, 0, 0], #[1, 1, 0], #[1, 0, 1],
    #[0, 2, 0], #[0, 1, 1], #[0, 0, 2], #[1, 0, 0], #[0, 1, 0], #[0, 0, 1]]
  for seed in [:12] do
    let generators := (Array.range 3).map fun i =>
      support.zipIdx |>.map fun (exponents, j) =>
        let c := ((seed + 1) * 1103515245 + (i + 3) * 12345 + (j + 1) * 69069 + i * j * 17) % 127
        ⟨exponents, (if (c + j) % 4 == 0 then 0 else c.toUInt64 % field.modulus)⟩
    cases := cases.push ⟨s!"generated-{seed}", 3, generators⟩
  return cases

end Hex.Groebner.F4Fixtures
