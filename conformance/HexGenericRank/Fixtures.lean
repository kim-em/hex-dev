/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRank

namespace Hex.GenericRank.Fixtures

open Hex

abbrev Poly (k : Nat) (C : Type) [Zero C] := MvPoly k C Mono.grevlex

structure Case (k : Nat) (C : Type) [Zero C] where
  name : String
  n : Nat
  m : Nat
  matrix : Matrix (Poly k C) n m
  expected : Nat

variable {k : Nat} {C : Type} [Lean.Grind.CommRing C] [DecidableEq C]
  [BEq C] [LawfulBEq C]

def ofRows (n m : Nat) (rows : Array (Array (Poly k C))) : Matrix (Poly k C) n m :=
  Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

/-- Full-rank, factorised low-rank and repeated-expression inputs, plus empty
and zero shapes. Nonzero leading minors are fixed by the construction. -/
def cases (x y z : Poly k C) : Array (Case k C) :=
  let t := x * y + z + 1
  let L := ofRows 3 1 #[#[x], #[y], #[x + y]]
  let R := ofRows 1 3 #[#[1, z, x]]
  #[⟨"full", 3, 3,
      ofRows 3 3 #[#[x + y, z + 1, x * y], #[0, x + 1, y * z], #[0, 0, z + 1]], 3⟩,
    ⟨"low-rank-product", 3, 3, L * R, 1⟩,
    ⟨"rectangular", 2, 3, ofRows 2 3 #[#[x, 1, z], #[0, y, 1]], 2⟩,
    ⟨"repeated", 2, 2, ofRows 2 2 #[#[t, t + 1], #[t - 1, t]], 2⟩,
    ⟨"variable", 1, 1, ofRows 1 1 #[#[x]], 1⟩,
    ⟨"quadratic-minor", 2, 2, ofRows 2 2 #[#[x, 1], #[1, x]], 2⟩,
    ⟨"zero", 2, 3, ofRows 2 3 #[], 0⟩,
    ⟨"no-rows", 0, 3, ofRows 0 3 #[], 0⟩,
    ⟨"no-columns", 3, 0, ofRows 3 0 #[], 0⟩]

end Hex.GenericRank.Fixtures
