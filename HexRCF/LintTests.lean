/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.TacticDocumentation

/-!
# Public RCF lint regression

This file intentionally uses legacy file syntax rather than `module`. Imported
docstring metadata is not available to the linter through module imports, which
would make every imported declaration appear undocumented.

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
@[env_linter disabled] def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName.components.getLast? == some `ofNat_ctorIdx then return none
      docBlameThm.test declName }

#lint- docBlame docBlameThm' in HexRCF
