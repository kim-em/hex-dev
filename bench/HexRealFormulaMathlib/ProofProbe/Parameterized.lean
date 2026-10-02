/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.ProofProbe.Support
public meta import HexRealFormulaMathlib.ProofProbe.Support

public section
namespace Hex.RealFormula.ProofProbe

real_parameter_probe parameterized
/-- info: 'Hex.RealFormula.ProofProbe.parameterized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parameterized

end Hex.RealFormula.ProofProbe
