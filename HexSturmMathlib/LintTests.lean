/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSturmMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.TacticDocumentation

/-! Whole-pair declaration checks use legacy imports to retain docstring metadata.
This audit is separate from computational baseline comparison and individual
proof/API assessment. -/
/-! Environment lints cover both module roots, including theorem documentation.
Legacy imports retain the imported docstring metadata needed by these checks. -/

#lint- docBlame docBlameThm in HexSturm
#lint- docBlame docBlameThm in HexSturmMathlib
