/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.Member

@[expose] public section

/-! Positive ideal membership proved by a literal shared derivation and the
public soundness theorem. Certificate replay uses ordinary kernel reduction. -/

namespace HexGroebnerTheory.MemberExample
open Hex.Groebner

/-- Explicit prime field and global monomial order. -/
def context : Context :=
  ⟨⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩, 2, .grevlex⟩

/-- The ideal generators x²−y and xy−1. -/
def generators : Array Certificate.Polynomial := #[
  [([2, 0], 1), ([0, 1], 6)], [([1, 1], 1), ([0, 0], 6)]]

/-- The member y²−x, serialized in descending lex order. -/
def target : Certificate.Polynomial := [([1, 0], 6), ([0, 2], 1)]

/-- The shared identity x*(xy−1)−y*(x²−y). -/
def witness : Certificate.Derivation := ⟨[
  .generator 0, .generator 1,
  .multiply [([1, 0], 1)] 1, .multiply [([0, 1], 1)] 0,
  .scale 6 3, .add 2 4], 5⟩

/-- The accepted literal certificate proves membership in the original ideal. -/
theorem member : denote context target ∈ Ideal.span
    (Set.range fun i : Fin generators.size => denote context generators[i]) :=
  checkMember_sound context generators target (.derivation witness) (by decide +kernel)

/-- info: 'HexGroebnerTheory.MemberExample.member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms member

end HexGroebnerTheory.MemberExample

namespace HexGroebnerTheory.MemberExample
open Hex.Groebner

/-- A composed forward-containment and explicit-cofactor positive witness. -/
def composed : Certificate.Member := .combination
  ⟨#[target],⟨witness.nodes,#[witness.root]⟩,⟨#[[([0,0],1)]],[]⟩⟩

theorem composed_mem : denote context target ∈ Ideal.span
    (Set.range fun i : Fin generators.size => denote context generators[i]) :=
  checkMember_sound context generators target composed (by decide +kernel)

/-- info: 'HexGroebnerTheory.MemberExample.composed_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms composed_mem

end HexGroebnerTheory.MemberExample
