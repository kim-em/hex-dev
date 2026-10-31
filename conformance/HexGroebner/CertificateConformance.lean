/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.CertificateBasis

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

#guard Certificate.leading .lex target = some ([1, 0], 6)
#guard Certificate.leading .grlex target = some ([0, 2], 1)
#guard Certificate.leading .grevlex target = some ([0, 2], 1)
#guard Certificate.leading .lex [] = none
#guard Certificate.divides [2, 0] [3, 4]
#guard !Certificate.divides [2, 1] [3, 0]
#guard !Certificate.divides [0] [0, 0]
#guard Certificate.lcm [2, 0] [1, 3] = some [2, 3]
#guard Certificate.lcm [0] [0, 0] = none

theorem ordered_leading : Certificate.leading .grevlex target = some ([0, 2], 1) := by
  decide +kernel

-- The checker body, including shared lookup, reduces in the ordinary kernel.
theorem accepted : checkMember context generators target witness = true := by
  decide +kernel

/-- info: 'Hex.Groebner.CertificateConformance.accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms accepted

-- Nonmonic leading coefficients must be crossed, even though production bases
-- are monic. Both zero inputs and ordinary characteristic two remain exact.
#guard Certificate.sPolynomial 7 .grevlex
  [([2, 0], 3), ([0, 1], 4)] [([1, 1], 2), ([0, 0], 5)] =
    [([1, 0], 6), ([0, 2], 1)]
#guard Certificate.sPolynomial 7 .grevlex [] generators[0]! = []
#guard Certificate.sPolynomial 7 .grevlex generators[0]! [] = []
#guard Certificate.sPolynomial 2 .grevlex
  [([2, 0], 1), ([0, 1], 1)] [([1, 1], 1), ([0, 0], 1)] =
    [([1, 0], 1), ([0, 2], 1)]

-- The correct identity -y*(x²-y) + x*(xy-1) has degree-three products.
-- Its degree-two result is an ideal member but this is not a bounded reduction.
#guard !Certificate.checkReduction 7 2 .grevlex generators
  #[[([0, 1], 6)], [([1, 0], 1)]] target
#guard Certificate.checkReduction 7 2 .grevlex (generators.push target)
  #[[], [], [([0, 0], 1)]] target
#guard !Certificate.checkReduction 7 2 .grevlex (generators.push target)
  #[[], [], [([0, 0], 7)]] target
#guard !Certificate.checkReduction 7 2 .grevlex (generators.push target)
  #[[], []] target
#guard !Certificate.checkReduction 7 2 .grevlex #[[([1], 1)]] #[[]] []
#guard Certificate.checkReduction 7 2 .grevlex #[] #[] []
#guard !Certificate.checkReduction 7 2 .grevlex #[] #[] target

def basis : Array Certificate.Polynomial := generators.push target

def basisWitness : Certificate.Basis := {
  forward := ⟨witness.nodes, #[0, 1, 5]⟩
  backward := ⟨[.generator 0, .generator 1], #[0, 1]⟩
  pairs := #[
    #[#[[], [], []], #[[], [], [([0, 0], 6)]], #[[([1, 0], 1)], [], [([0, 1], 6)]]],
    #[#[[], [], [([0, 0], 1)]], #[[], [], []], #[[([0, 0], 1)], [], []]],
    #[#[[([1, 0], 6)], [], [([0, 1], 1)]], #[[([0, 0], 6)], [], []], #[[], [], []]]] }

#guard checkBasis context generators basis basisWitness
#guard !checkBasis { context with order := .lex } generators basis basisWitness
#guard !checkBasis { context with
  field := ⟨11, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩ } generators basis basisWitness
#guard !checkBasis context #[] basis basisWitness
#guard !checkBasis context generators basis { basisWitness with
  forward := { basisWitness.forward with roots := #[0, 1] } }
#guard !checkBasis context generators basis { basisWitness with
  backward := { basisWitness.backward with roots := #[0, 0] } }
#guard !checkBasis context generators basis { basisWitness with
  forward := { basisWitness.forward with roots := #[0, 1, 99] } }
#guard !checkBasis context generators basis { basisWitness with
  forward := ⟨[.generator 7], #[0, 0, 0]⟩ }
#guard !checkBasis context generators basis { basisWitness with pairs := #[] }
#guard !checkBasis context generators basis { basisWitness with
  pairs := basisWitness.pairs.push basisWitness.pairs[0]! }
#guard !checkBasis context generators basis { basisWitness with
  pairs := basisWitness.pairs.set! 0 #[] }
#guard !checkBasis context generators basis { basisWitness with
  pairs := basisWitness.pairs.set! 0
    ((basisWitness.pairs[0]!).set! 1 #[[([0, 1], 1)], [([1, 0], 6)], []]) }

#guard !Certificate.checkShape .grevlex (basis.reverse)
#guard !Certificate.checkShape .grevlex (basis.push [])
#guard !Certificate.checkShape .grevlex #[[([1, 0], 2)]]
#guard !Certificate.checkShape .grevlex #[[([2, 0], 1)], [([1, 0], 1)]]

-- Replacing g₀ by g₀+g₁ preserves the ideal and Gröbner property, with valid
-- containment and bounded pair witnesses. Its xy tail is reducible by g₁.
def nonreduced : Array Certificate.Polynomial := basis.set! 0
  [([2, 0], 1), ([1, 1], 1), ([0, 1], 6), ([0, 0], 6)]

def nonreducedWitness : Certificate.Basis := {
  forward := ⟨witness.nodes ++ [.add 0 1], #[6, 1, 5]⟩
  backward := ⟨[.generator 0, .generator 1, .scale 6 1, .add 0 2], #[3, 1]⟩
  pairs := #[
    #[#[[], [], []], #[[], [([0, 1], 1)], [([0, 0], 6)]],
      #[[([1, 0], 1)], target, [([0, 1], 6)]]],
    #[#[[], [([0, 1], 6)], [([0, 0], 1)]], #[[], [], []],
      #[[([0, 0], 1)], [([0, 0], 6)], []]],
    #[#[[([1, 0], 6)], [([1, 0], 1), ([0, 2], 6)], [([0, 1], 1)]],
      #[[([0, 0], 6)], [([0, 0], 1)], []], #[[], [], []]]] }

#guard Certificate.checkContainment 7 2 generators nonreduced nonreducedWitness.forward
#guard Certificate.checkContainment 7 2 nonreduced generators nonreducedWitness.backward
#guard Certificate.checkPairs 7 2 .grevlex nonreduced nonreducedWitness.pairs
#guard !checkBasis context generators nonreduced nonreducedWitness
#guard checkBasis context #[] #[] ⟨⟨[], #[]⟩, ⟨[], #[]⟩, #[]⟩
#guard checkBasis context #[[]] #[] ⟨⟨[], #[]⟩, ⟨[.zero], #[0]⟩, #[]⟩
#guard checkBasis context #[[([0, 0], 3)]] #[[([0, 0], 1)]] {
  forward := ⟨[.generator 0, .scale 5 0], #[1]⟩
  backward := ⟨[.generator 0, .scale 3 0], #[1]⟩
  pairs := #[#[#[[]]]] }

-- Ordinary F₂[x] retains x²+x as a nonzero generator, with no field equations.
#guard checkBasis
  ⟨⟨2, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 1, .grevlex⟩
  #[[([2], 1), ([1], 1)]] #[[([2], 1), ([1], 1)]] {
    forward := ⟨[.generator 0], #[0]⟩
    backward := ⟨[.generator 0], #[0]⟩
    pairs := #[#[#[[]]]] }

end Hex.Groebner.CertificateConformance
