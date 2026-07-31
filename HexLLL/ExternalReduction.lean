/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Reduction

public section

/-!
Executable entry point for checking external LLL reduction.

This module defines a small `main` driver that checks the optional native LLL
external reducer against an expected `absent`/`present` state, exercising the public
`Hex.lll.loadExternalReducer` / `Hex.lll.externalReducerActive` surface:

* `absent`; with nothing loaded, confirm `Hex.lll.externalReducerActive` is `false`
  and that `externalReduce` reports `.error` rather than succeeding.
* `present <path>`; `Hex.lll.loadExternalReducer <path>` must succeed and
  `Hex.lll.externalReducerActive` must then be `true`.

The driver returns process exit codes (`0` on agreement, `1`/`2` on mismatch or
misuse) for use as a CI check.
-/

namespace Hex

open Hex.Internal
namespace ExternalReduction

/-- Check the absent or explicitly loaded external-reduction configuration. -/
@[expose]
def main (args : List String) : IO UInt32 := do
  match args with
  | ["absent"] =>
      if ← Hex.lll.externalReducerActive then
        IO.eprintln "externalReducerActive = true, expected false"
        return 1
      match ExternalReducer.externalReduce 0 0 #[] 0.75 0.55 0 false with
      | .error _ => return 0
      | .ok _ =>
          IO.eprintln "externalReduce unexpectedly succeeded while external reducer is absent"
          return 1
  | ["present", path] =>
      if !(← Hex.lll.loadExternalReducer path) then
        IO.eprintln s!"loadExternalReducer failed for {path}"
        return 1
      if ← Hex.lll.externalReducerActive then
        return 0
      else
        IO.eprintln "externalReducerActive = false after a successful loadExternalReducer"
        return 1
  | _ =>
      IO.eprintln "usage: hexlll_external_reduction absent | present <path>"
      return 2

end ExternalReduction
end Hex

/-- Command-line entry point for the external-reduction check. -/
@[expose]
def main (args : List String) : IO UInt32 :=
  Hex.ExternalReduction.main args
