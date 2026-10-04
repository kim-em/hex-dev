/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Precision.Inputs
public import HexRCF.ProofProbe.Windows.Support
public meta import HexRCF.ProofProbe.Precision.Inputs
public meta import HexRCF.ProofProbe.Windows.Support
@[expose] public section

namespace Hex.RCF.ProofProbe.Precision
open RealCoefficients

elab "precision64_rcf" : tactic => Lean.Elab.Tactic.liftMetaTactic fun goal => do
  let proof ← Lean.withOptions (fun options => options
      |>.setBool `debug.skipKernelTC false |>.setBool `Elab.async false) do
    let (proof, _, _, _) ← FieldLiteral.proveRefiningWithCertificate
      (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root64)
      (Lean.mkConst ``values64) (Lean.mkConst ``GeneratorWindowTests.matrix)
      values64 GeneratorWindowTests.matrix .existsReal
    let proof ← Lean.Meta.mkAppM ``Iff.mp #[Lean.mkConst ``sameSentence, proof]
    Hex.RCF.checkAxioms `Hex.RCF.ProofProbe.Precision proof
    Lean.Meta.checkWithKernel proof
    pure proof
  goal.assign proof
  return []

end Hex.RCF.ProofProbe.Precision
