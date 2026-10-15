/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexRealAlgebraicTheory.FieldSign

/-- info: 'Hex.RealAlgebraicNumber.signField_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealAlgebraicNumber.signField_spec

/-- info: 'Hex.RealAlgebraicNumber.signField_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealAlgebraicNumber.signField_eq
