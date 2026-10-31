/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.Reduced
public import HexGroebnerTheory.Certificate

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
