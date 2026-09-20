/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.RealFormulaProbe.Support

public section
namespace Hex.RCF.RealFormulaProbe

theorem adapter : (RealFormula.ofSentence cubic).toProp Fin.elim0 ↔ cubic.toProp :=
  RealFormula.ofSentence_correct cubic Fin.elim0
#print axioms adapter

end Hex.RCF.RealFormulaProbe
