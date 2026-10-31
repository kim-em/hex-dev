/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.Order
public import HexGroebnerTheory.CertificateLeading
public import HexGroebnerTheory.CertificatePair
public import HexGroebnerTheory.CertificateReduction
public import HexGroebnerTheory.CertificateBasis

public section

/-! Downstream ordinary-kernel examples for the monomial-order bridge. -/

namespace HexGroebnerTheory.Examples
open Hex
open scoped HexMvPolyTheory

/-- A polynomial whose leading term distinguishes lex from graded orders. -/
@[expose] def polynomial (cmp : Mono 2 → Mono 2 → Ordering) [IsMonomialOrder cmp] :
    Hex.MvPoly 2 Int cmp :=
  .ofTerms [(#v[2, 0], 3), (#v[0, 3], -2), (Mono.zero, 1)]

private theorem lead (cmp : Mono 2 → Mono 2 → Ordering) [IsMonomialOrder cmp]
    (m : Mono 2) (c : Int)
    (hc : (polynomial cmp).coeff m = c) (hnc : c ≠ 0)
    (hmax : ∀ k ∈ ([#v[2, 0], #v[0, 3], Mono.zero] : List (Mono 2)), (cmp k m).isLE) :
    (polynomial cmp).leadingTerm = some (m, c) := by
  apply (MvPoly.leadingTerm_eq_some_iff _ _ _).mpr
  constructor
  · unfold MvPoly.coeff at hc
    cases h : (polynomial cmp).coeff? m with
    | none => simp [h] at hc; exact False.elim (hnc hc.symm)
    | some d => simpa [h] using hc
  · intro k hk
    apply hmax k
    have hc := (MvPoly.mem_monomials_iff k _).mp hk
    by_contra h
    have hne : #v[2, 0] ≠ k ∧ #v[0, 3] ≠ k ∧ Mono.zero ≠ k := by
      simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true, and_true, not_or, ne_eq, eq_comm] using h
    simp [polynomial, MvPoly.coeff_ofTerms, hne.1, hne.2.1, hne.2.2] at hc

/-- Lex chooses the first variable despite the other term's larger total degree. -/
theorem lex_degree :
    (toMonomialOrder (@Mono.lex 2)).degree
      (HexMvPolyTheory.toMvPolynomial (polynomial Mono.lex)) =
        HexMvPolyTheory.monoEquiv #v[2, 0] := by
  apply leading_degree Mono.lex (c := (3 : Int))
  apply lead <;> first | (simp [polynomial, MvPoly.coeff_ofTerms]; decide +kernel) | decide +kernel

/-- Graded lex chooses the term of greater total degree. -/
theorem grlex_degree :
    (toMonomialOrder (@Mono.grlex 2)).degree
      (HexMvPolyTheory.toMvPolynomial (polynomial Mono.grlex)) =
        HexMvPolyTheory.monoEquiv #v[0, 3] := by
  apply leading_degree Mono.grlex (c := (-2 : Int))
  apply lead <;> first | (simp [polynomial, MvPoly.coeff_ofTerms]; decide +kernel) | decide +kernel

/-- Graded reverse lex preserves the leading coefficient's sign. -/
theorem grevlex_coefficient :
    (toMonomialOrder (@Mono.grevlex 2)).leadingCoeff
      (HexMvPolyTheory.toMvPolynomial (polynomial Mono.grevlex)) = (-2 : Int) := by
  apply leading_coefficient Mono.grevlex (m := #v[0, 3])
  apply lead <;> first | (simp [polynomial, MvPoly.coeff_ofTerms]; decide +kernel) | decide +kernel

/-- info: 'HexGroebnerTheory.Examples.lex_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lex_degree
/-- info: 'HexGroebnerTheory.Examples.grlex_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms grlex_degree
/-- info: 'HexGroebnerTheory.Examples.grevlex_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms grevlex_coefficient

local instance : Hex.ZMod64.Bounds 7 where
  pPos := by decide
  pLtR := by decide

/-- Ordinary residue term lists retain lex leading exponents after transport. -/
theorem certificate_lex :
    (toMonomialOrder (Hex.Groebner.TermOrder.lex.cmp 2)).degree
      (HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.lex.cmp 2)
        [([2, 0], 3), ([0, 3], 5)]) = HexMvPolyTheory.monoEquiv #v[2, 0] := by
  exact Certificate.leading_degree .lex (term := ([2, 0], 3))
    (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (by decide +kernel)) (by decide +kernel)

/-- The same serialized list has a different leading exponent in graded lex. -/
theorem certificate_grlex :
    (toMonomialOrder (Hex.Groebner.TermOrder.grlex.cmp 2)).degree
      (HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grlex.cmp 2)
        [([2, 0], 3), ([0, 3], 5)]) = HexMvPolyTheory.monoEquiv #v[0, 3] := by
  exact Certificate.leading_degree .grlex (term := ([0, 3], 5))
    (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (by decide +kernel)) (by decide +kernel)

/-- Graded reverse lex selects the stored coefficient of its actual leading term. -/
theorem certificate_grevlex :
    (toMonomialOrder (Hex.Groebner.TermOrder.grevlex.cmp 2)).leadingCoeff
      (HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2)
        [([2, 0], 3), ([0, 3], 5)]) = 5 := by
  exact Certificate.leading_coefficient .grevlex (term := ([0, 3], 5))
    (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (by decide +kernel)) (by decide +kernel)

/-- info: 'HexGroebnerTheory.Examples.certificate_lex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certificate_lex
/-- info: 'HexGroebnerTheory.Examples.certificate_grlex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certificate_grlex
/-- info: 'HexGroebnerTheory.Examples.certificate_grevlex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certificate_grevlex

/-- A literal nonmonic S-pair agrees with Mathlib after ordinary kernel replay. -/
theorem certificate_pair :
    (toMonomialOrder (Hex.Groebner.TermOrder.grevlex.cmp 2)).sPolynomial
      (HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2)
        [([2, 0], 3), ([0, 1], 4)])
      (HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2)
        [([1, 1], 2), ([0, 0], 5)]) =
      HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2)
        [([1, 0], 6), ([0, 2], 1)] := by
  rw [← Certificate.sPolynomial_eq .grevlex
    (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (by decide +kernel))
    (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (by decide +kernel))]
  have h : Hex.Groebner.Certificate.sPolynomial 7 .grevlex
      [([2, 0], 3), ([0, 1], 4)] [([1, 1], 2), ([0, 0], 5)] =
        [([1, 0], 6), ([0, 2], 1)] := by decide +kernel
  rw [h]

/-- info: 'HexGroebnerTheory.Examples.certificate_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certificate_pair

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The completed three-polynomial basis used for a literal S-pair reduction. -/
@[expose] def certificateBasis : Array Hex.Groebner.Certificate.Polynomial := #[
  [([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)],
  [([1, 0], 6), ([0, 2], 1)]]

/-- A kernel-checked bounded identity supplies the actual zero-remainder
obligation for the original pair, rather than just ideal membership. -/
theorem certificate_reduction :
    (toMonomialOrder (Hex.Groebner.TermOrder.grevlex.cmp 2)).IsRemainder
      ((toMonomialOrder (Hex.Groebner.TermOrder.grevlex.cmp 2)).sPolynomial
        (HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2)
          [([2, 0], 1), ([0, 1], 6)])
        (HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2)
          [([1, 1], 1), ([0, 0], 6)]))
      (Set.range fun i : Fin certificateBasis.size =>
        HexMvPolyTheory.Kernel.denoteMod 7 (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2)
          certificateBasis[i]) 0 := by
  rw [← Certificate.sPolynomial_eq .grevlex
    (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (by decide +kernel))
    (Hex.MvPoly.Kernel.isCanonicalMod_iff.mp (by decide +kernel))]
  exact Certificate.checkReduction_sound .grevlex certificateBasis
    #[[], [], [([0, 0], 6)]] _ (by decide +kernel)

/-- info: 'HexGroebnerTheory.Examples.certificate_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certificate_reduction

/-- Original two generators for complete literal basis certification. -/
@[expose] def certificateGenerators : Array Hex.Groebner.Certificate.Polynomial := #[
  [([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)]]

/-- Explicit finite-field and monomial-order metadata for the complete example. -/
@[expose] def basisContext : Hex.Groebner.Context :=
  ⟨⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 2, .grevlex⟩

/-- Shared ideal containments and all nine bounded final S-pair identities. -/
@[expose] def basisWitness : Hex.Groebner.Certificate.Basis := {
  forward := ⟨[.generator 0, .generator 1,
    .multiply [([1, 0], 1)] 1, .multiply [([0, 1], 1)] 0,
    .scale 6 3, .add 2 4], #[0, 1, 5]⟩
  backward := ⟨[.generator 0, .generator 1], #[0, 1]⟩
  pairs := #[
    #[#[[], [], []], #[[], [], [([0, 0], 6)]], #[[([1, 0], 1)], [], [([0, 1], 6)]]],
    #[#[[], [], [([0, 0], 1)]], #[[], [], []], #[[([0, 0], 1)], [], []]],
    #[#[[([1, 0], 6)], [], [([0, 1], 1)]], #[[([0, 0], 6)], [], []], #[[], [], []]]] }

/-- A complete Gröbner basis theorem obtained from literal-data kernel replay. -/
theorem certificate_basis : IsReducedBasis basisContext certificateGenerators certificateBasis :=
  checkBasis_sound basisContext certificateGenerators certificateBasis basisWitness (by decide +kernel)

/-- info: 'HexGroebnerTheory.Examples.certificate_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certificate_basis

end HexGroebnerTheory.Examples
