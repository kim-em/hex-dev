/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.Lint
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Linter.TacticDocumentation

import all HexRCF.Builder
import all HexRCF.Carrier
import all HexRCF.CarrierCheck
import all HexRCF.Cells
import all HexRCF.CellsCheck
import all HexRCF.Certificate
import all HexRCF.CommonRoot
import all HexRCF.CommonRootCheck
import all HexRCF.Decision
import all HexRCF.DecisionCheck
import all HexRCF.IsolationCheck
import all HexRCF.Isolations
import all HexRCF.Language
import all HexRCF.Regions
import all HexRCF.Reify
import all HexRCF.Separation
import all HexRCF.SeparationCheck
import all HexRCF.SignMatrix
import all HexRCF.SignMatrixCheck
import all HexRCF.Soundness
import all HexRCF.SturmBuilder
import all HexRCF.SturmCheck
import all HexRCF.SturmReplay
import all HexRCF.Syntax
import all HexRCF.Tactic

section

/-!
# Public RCF lint regression

Private module imports retain imported docstrings and declaration bodies for
the lint checks.

Beyond Batteries' default linter set (which already includes `docBlame` for
defs, structures, and other non-theorem declarations), this run enables
theorem docstring coverage via `docBlameThm'` below, so the
docstring-coverage bar of `SPEC/design-principles.md` is build-enforced
rather than manual. `docBlame` is listed explicitly to record that the bar
depends on it.
-/

open Batteries.Tactic.Lint in
/-- `docBlameThm`, minus the compiler-generated `ofNat_ctorIdx` theorems of
enum inductives. Batteries' `Environment.isAutoDecl` filter predates that
generated name (it recognises `ofNat`, `toCtorIdx`, and `ctorIdx`, but not
`ofNat_ctorIdx`), so plain `docBlameThm` reports those theorems as
undocumented; `@[nolint]` cannot repair this from here because it only applies
in the defining module. -/
@[env_linter disabled] public meta def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName.components.getLast? == some `ofNat_ctorIdx then return none
      docBlameThm.test declName }

#lint- docBlame docBlameThm' in HexRCF
