/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSparsePolyMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.TacticDocumentation

/-!
# Sparse-polynomial lint regression

This file intentionally uses legacy file syntax rather than `module`.
Imported docstring metadata is not available to the linter through
module imports, which would make every imported declaration appear
undocumented.

Beyond Batteries' default linter set (which already includes `docBlame`
for defs, structures, and other non-theorem declarations), this run
enables theorem docstring coverage via `docBlameThm'` below, so the
docstring-coverage bar of `SPEC/design-principles.md` is build-enforced
rather than manual. `docBlame` is listed explicitly to record that the
bar depends on it. The run covers both the Mathlib-free core and its
Mathlib correspondence layer.
-/

open Batteries.Tactic.Lint in
/-- `docBlameThm`, minus the compiler-generated `ofNat_ctorIdx` theorems
of enum inductives and the `@[ext]`-generated `ext_coeff_iff`.
Batteries' `Environment.isAutoDecl` filter predates those generated
names, so plain `docBlameThm` reports them as undocumented; `@[nolint]`
cannot repair this from here because it only applies in the defining
module. -/
@[env_linter disabled] def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName.components.getLast? == some `ofNat_ctorIdx then return none
      if declName.components.getLast? == some `ext_coeff_iff then return none
      docBlameThm.test declName }

#lint- docBlame docBlameThm' in HexSparsePoly

#lint- docBlame docBlameThm' in HexSparsePolyMathlib
