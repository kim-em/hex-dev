/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSmithMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.TacticDocumentation

/-!
# Integer Smith-normal-form lint regression

This file intentionally uses legacy file syntax rather than `module`. Imported
docstring metadata is not available to the linter through module imports,
which would make every imported declaration appear undocumented.

The run covers the Mathlib-free implementation and its correspondence-only
Mathlib layer. Batteries' default linter set includes `docBlame`; the local
theorem linter below makes theorem docstring coverage build-enforced too.
-/

open Batteries.Tactic.Lint in
/-- `docBlameThm`, excluding compiler-generated enum constructor-index
theorems that cannot carry a source docstring. -/
@[env_linter disabled] def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName.components.getLast? == some `ofNat_ctorIdx then return none
      docBlameThm.test declName }

#lint- docBlame docBlameThm' in HexSmith

#lint- docBlame docBlameThm' in HexSmithMathlib
