/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexTruncatedSeriesMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.TacticDocumentation

/-!
# Truncated-series lint regression

This file intentionally uses legacy file syntax rather than `module`. Imported
docstring metadata is not available to the linter through module imports,
which would make every imported declaration appear undocumented.

Beyond Batteries' default linter set (which already includes `docBlame` for
definitions, structures, and other non-theorem declarations), this run enables
theorem docstring coverage via `docBlameThm'` below. The run covers both the
Mathlib-free core and its Mathlib correspondence layer.
-/

open Batteries.Tactic.Lint in
/-- `docBlameThm`, minus compiler-generated support theorems whose docstrings
cannot be repaired from this downstream regression module. -/
@[env_linter disabled] def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName.components.getLast? == some `ext_coeff_iff then return none
      if declName.components.getLast? == some `ext_iff then return none
      docBlameThm.test declName }

#lint- docBlameThm' in HexTruncatedSeries

#lint- docBlameThm' in HexTruncatedSeriesMathlib
