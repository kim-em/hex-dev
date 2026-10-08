/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.Lint
public import Mathlib.Tactic.Linter.Style

public section

/-!
Declaration and docstring checks for the fast polynomial API. Legacy file syntax
retains imported docstring metadata. `structureInType` is replaced by the same
check using recorded projection names, so private fields remain encapsulated.
The explicit list covers the default Batteries/Mathlib checks plus theorem docs.
-/

open Lean Meta Batteries.Tactic.Lint in
/-- Check structure fields through their recorded projection names, including private fields. -/
@[env_linter disabled] meta def structureInType' : Batteries.Tactic.Lint.Linter :=
  { structureInType with
    test := fun declName => do
      unless isStructure (← getEnv) declName do return none
      let prop ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
        fun _ ty => return ty == .sort .zero
      if prop then return none
      let info := (getStructureInfo? (← getEnv) declName).get!
      if info.fieldNames.isEmpty then return none
      let allProofs ← info.fieldInfo.allM fun field => do
        isProof (← mkConstWithLevelParams field.projFn)
      unless allProofs do return none
      return m!"all fields are propositional but the structure isn't." }

#lint- only checkType defsWithUnderscore deprecatedNoSince docBlame
  impossibleInstance nonClassInstance simpComm simpNF structureInType'
  synTaut unusedArguments unusedHavesSuffices docBlameThm in HexPolyFast
