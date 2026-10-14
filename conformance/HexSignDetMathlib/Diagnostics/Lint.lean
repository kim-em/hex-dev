/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet
import HexSignDetMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint

/-! Environment lints cover both production module roots, including theorem
documentation. The imported modules supply the docstring metadata used by these
checks. Individual proof/API and use assessment remain separate requirements. -/

-- The pinned Lean compiler generates three recursive equality auxiliaries and
-- two enum constructor-index identities. Its source defines these names in
-- Lean.Elab.Deriving.DecEq. They are not handwritten API declarations.
-- Guard the exact diagnostics so every additional lint finding still fails;
-- the computational modules need no linter imports or dependency changes.
/-- error: /- The `defsWithUnderscore` linter reports:
FOUND definitions with an underscore in their name.
This linter can be disabled with `@[nolint defsWithUnderscore]`. -/
-- HexSignDet.Codec.Value
#check Hex.SignDet.Codec.Json.instDecidableEqFields.decEq_3 /- The definition `Hex.SignDet.Codec.Json.instDecidableEqFields.decEq_3` contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead. -/
#check Hex.SignDet.Codec.Json.instDecidableEqValues.decEq_3 /- The definition `Hex.SignDet.Codec.Json.instDecidableEqValues.decEq_3` contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead. -/
#check Hex.SignDet.Codec.Json.instDecidableEqValue.decEq_3 /- The definition `Hex.SignDet.Codec.Json.instDecidableEqValue.decEq_3` contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead. -/

/- The `docBlameThm` linter reports:
THEOREMS ARE MISSING DOCUMENTATION STRINGS:
This linter can be disabled with `@[nolint docBlameThm]`. -/
-- HexSignDet.Descriptor
#check Hex.SignDet.DescriptorError.ofNat_ctorIdx /- theorem missing documentation string -/

-- HexSignDet.Produce
#check Hex.SignDet.BuildError.ofNat_ctorIdx /- theorem missing documentation string -/ -/
#guard_msgs (whitespace := lax) in
#lint- docBlame docBlameThm in HexSignDet
#lint- docBlame docBlameThm in HexSignDetMathlib
