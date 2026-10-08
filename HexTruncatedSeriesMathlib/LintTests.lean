/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeriesMathlib
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.Lint
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Linter.TacticDocumentation

import all HexTruncatedSeries.Classes
import all HexTruncatedSeries.Comp
import all HexTruncatedSeries.Defs
import all HexTruncatedSeries.ExpLog
import all HexTruncatedSeries.Inverse
import all HexTruncatedSeries.Newton
import all HexTruncatedSeries.Precision
import all HexTruncatedSeries.Revert
import all HexTruncatedSeries.Ring
import all HexTruncatedSeries.Sqrt
import all HexTruncatedSeriesMathlib.Basic
import all HexTruncatedSeriesMathlib.Newton
import all HexTruncatedSeriesMathlib.Ops

public section

/-!
# Truncated-series lint regression

The explicit `import all` declarations retain docstrings and private proof
helpers for linting. Ordinary module imports omit that metadata.

Beyond Batteries' default linter set (which already includes `docBlame` for
definitions, structures, and other non-theorem declarations), this run enables
theorem docstring coverage via `docBlameThm'` below. The run covers both the
Mathlib-free core and its Mathlib correspondence layer.
-/

open Batteries.Tactic.Lint in
/-- `docBlameThm`, minus compiler-generated support theorems whose docstrings
cannot be repaired from this downstream regression module. -/
@[env_linter disabled] meta def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName.components.getLast? == some `ext_coeff_iff then return none
      if declName.components.getLast? == some `ext_iff then return none
      docBlameThm.test declName }

#lint- docBlameThm' in HexTruncatedSeries

#lint- docBlameThm' in HexTruncatedSeriesMathlib
