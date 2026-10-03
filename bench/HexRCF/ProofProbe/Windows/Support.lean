/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.GeneratorWindowInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.GeneratorWindowInputs
public meta import HexRCF.ProofProbe.Literals.Support
@[expose] public section

namespace Hex.RCF.ProofProbe.Windows
open RealCoefficients

abbrev sentence : Prop := ∃ x : ℝ, GeneratorWindowTests.matrix.toProp
  (RealFormula.append (fun j => Field.value
    (Field.literalRep SquareTwo.polynomial SquareTwo.square
      GeneratorWindowTests.hw GeneratorWindowTests.hp) (GeneratorWindowTests.values j)) x)

elab "fixed_window_rcf" : tactic => Lean.Elab.Tactic.liftMetaTactic fun goal => do
  let proof ← Lean.withOptions (fun options => options
      |>.setBool `debug.skipKernelTC false |>.setBool `Elab.async false) do
    let (proof, _, _, _) ← FieldLiteral.proveRefiningWithCertificate
      (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``GeneratorWindowTests.root)
      (Lean.mkConst ``GeneratorWindowTests.values) (Lean.mkConst ``GeneratorWindowTests.matrix)
      GeneratorWindowTests.values GeneratorWindowTests.matrix .existsReal
    Hex.RCF.checkAxioms `Hex.RCF.ProofProbe.Windows proof
    Lean.Meta.checkWithKernel proof
    pure proof
  goal.assign proof
  return []

end Hex.RCF.ProofProbe.Windows
