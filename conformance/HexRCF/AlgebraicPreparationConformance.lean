/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.AlgebraicPreparationCases
open Lean Meta

-- A separate importing module requires the end-of-run marker. A swallowed
-- test interrupt must not leave an apparently green, partially executed run.
run_meta do
  let .thmInfo declaration ← getConstInfo ``Hex.RCF.AlgebraicPreparationConformance.runFinished
    | throwError "native source conformance did not finish"
  let _ ← Hex.RCF.checkProof `nativeSourceRunCompleted declaration.type declaration.value
  logInfo "native source conformance completion independently checked"
