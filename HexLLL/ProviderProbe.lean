/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Basic

public section

/-!
Executable probe entry point for the `hex-lll` external reduction provider.

This module defines a small `main` driver that checks the optional native LLL
provider against an expected `absent`/`present` state.  It compares
`Hex.Internal.LLLProvider.providerAvailable` to the argument, and when the provider is
expected to be absent it additionally confirms that `Hex.Internal.LLLProvider.providerReduce`
reports `.error` rather than succeeding.  The driver returns process exit codes
(`0` on agreement, `1`/`2` on mismatch or misuse) for use as a CI check.
-/

namespace Hex

open Hex.Internal
namespace LLLProviderProbe

@[expose]
def main (args : List String) : IO UInt32 := do
  let expected ←
    match args with
    | ["absent"] => pure false
    | ["present"] => pure true
    | _ =>
        IO.eprintln "usage: hexlll_provider_probe absent|present"
        return 2
  let actual := LLLProvider.providerAvailable ()
  if actual = expected then
    if !expected then
      match LLLProvider.providerReduce 0 0 #[] 0.75 0.55 0 false with
      | .error _ => return 0
      | .ok _ =>
          IO.eprintln "providerReduce unexpectedly succeeded while provider is absent"
          return 1
    return 0
  else
    IO.eprintln s!"providerAvailable = {actual}, expected {expected}"
    return 1

end LLLProviderProbe
end Hex

@[expose]
def main (args : List String) : IO UInt32 :=
  Hex.LLLProviderProbe.main args
