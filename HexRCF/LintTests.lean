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
-/

#lint- in HexRCF
