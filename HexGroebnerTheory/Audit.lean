/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.Reduced
public import HexGroebnerTheory.Pairs
public import HexGroebnerTheory.Certificate
public import HexGroebnerTheory.CertificateOrder
public import HexGroebnerTheory.CertificateLeading

/-! The mathematical bridge and independent membership checker use only Lean's
standard foundational axioms. No native success bit is a proof assumption. -/

/-- info: 'HexGroebnerTheory.buchberger_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.buchberger_iff
/-- info: 'HexGroebnerTheory.remainder_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.remainder_unique
/-- info: 'HexGroebnerTheory.reduced_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.reduced_unique
/-- info: 'HexGroebnerTheory.checkMember_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.checkMember_sound

/-- info: 'HexGroebnerTheory.spoly_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.spoly_chain
/-- info: 'HexGroebnerTheory.lcm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.lcm_lt

/-- info: 'HexGroebnerTheory.groebner_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.groebner_iff
/-- info: 'HexGroebnerTheory.toMonomialOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.toMonomialOrder
/-- info: 'HexGroebnerTheory.compare_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.compare_lt
/-- info: 'HexGroebnerTheory.leading_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.leading_degree
/-- info: 'HexGroebnerTheory.leading_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.leading_coefficient
/-- info: 'HexGroebnerTheory.Certificate.compare_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.Certificate.compare_eq

/-- info: 'HexGroebnerTheory.Certificate.leading_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.Certificate.leading_degree
/-- info: 'HexGroebnerTheory.Certificate.leading_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexGroebnerTheory.Certificate.leading_coefficient
/-- info: 'HexMvPolyTheory.Kernel.residueEquiv_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HexMvPolyTheory.Kernel.residueEquiv_coeff
