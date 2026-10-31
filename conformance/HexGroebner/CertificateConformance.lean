/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Certificate

/-!
Oracle: none (core); complete polynomial identities are replayed independently.
Mode: always.
Covered operations: shared membership derivations over natural-residue term lists.
Covered properties: acyclic references, canonical forms, exact arithmetic.
Covered edge cases: malformed factors/indices, wrong ideal, wrong target,
zero generators, noncanonical coefficients, zero scalar and zero polynomial.
-/

namespace Hex.Groebner.CertificateConformance

def context : Context :=
  ⟨⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 2, .grevlex⟩

def generators : Array Certificate.Polynomial := #[
  [([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)]]

def target : Certificate.Polynomial := [([1, 0], 6), ([0, 2], 1)]

-- x*(xy-1) - y*(x²-y) = y²-x, serialized in descending lex order.
def witness : Certificate.Member := ⟨[
  .generator 0, .generator 1,
  .multiply [([1, 0], 1)] 1, .multiply [([0, 1], 1)] 0,
  .scale 6 3, .add 2 4], 5⟩

#guard checkMember context generators target witness
#guard !checkMember context #[] target witness
#guard !checkMember context generators [] witness
#guard !checkMember context generators (target.reverse) witness
#guard !checkMember context generators target { witness with root := 6 }
#guard !checkMember context generators target ⟨[], 0⟩
#guard !checkMember context generators target ⟨[.add 0 0], 0⟩
#guard !checkMember context generators target ⟨[.generator 0, .scale 7 0], 1⟩
#guard !checkMember context generators target ⟨[.generator 0, .multiply [([1], 1)] 0], 1⟩
#guard !checkMember context generators target ⟨[.generator 0, .multiply [([1, 0], 7)] 0], 1⟩
#guard !checkMember context generators target ⟨[.generator 0, .multiply [([1, 0], 0)] 0], 1⟩
#guard !checkMember context generators target ⟨[.generator 0, .multiply [([1, 0], 1), ([1, 0], 1)] 0], 1⟩
#guard !checkMember context #[[([1], 1)]] [] ⟨[.zero], 0⟩
#guard checkMember context #[] [] ⟨[.zero], 0⟩
#guard checkMember context generators [] ⟨[.generator 0, .scale 0 0], 1⟩
#guard checkMember context generators [([1, 0], 5), ([0, 2], 2)]
  ⟨witness.nodes ++ [.add 5 5], 6⟩

-- The checker body, including shared lookup, reduces in the ordinary kernel.
theorem accepted : checkMember context generators target witness = true := by
  decide +kernel

/-- info: 'Hex.Groebner.CertificateConformance.accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms accepted

end Hex.Groebner.CertificateConformance
