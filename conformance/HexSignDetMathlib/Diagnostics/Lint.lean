/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDetMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint

/-! Environment lints cover the companion production module root, including theorem
documentation. The imported modules supply the docstring metadata used by these
checks. Individual proof/API and use assessment remain separate requirements. -/

#lint- docBlame docBlameThm in HexSignDetMathlib
