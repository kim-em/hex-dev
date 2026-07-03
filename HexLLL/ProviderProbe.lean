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
provider against an expected `absent`/`present` state, exercising the public
`Hex.lll.loadProvider` / `Hex.lll.providerActive` surface:

* `absent` — with nothing loaded, confirm `Hex.lll.providerActive` is `false`
  and that `providerReduce` reports `.error` rather than succeeding.
* `present <path>` — `Hex.lll.loadProvider <path>` must succeed and
  `Hex.lll.providerActive` must then be `true`.

The driver returns process exit codes (`0` on agreement, `1`/`2` on mismatch or
misuse) for use as a CI check.
-/

namespace Hex

open Hex.Internal
namespace LLLProviderProbe

@[expose]
def main (args : List String) : IO UInt32 := do
  match args with
  | ["absent"] =>
      if ← Hex.lll.providerActive then
        IO.eprintln "providerActive = true, expected false"
        return 1
      match LLLProvider.providerReduce 0 0 #[] 0.75 0.55 0 false with
      | .error _ => return 0
      | .ok _ =>
          IO.eprintln "providerReduce unexpectedly succeeded while provider is absent"
          return 1
  | ["present", path] =>
      if !(← Hex.lll.loadProvider path) then
        IO.eprintln s!"loadProvider failed for {path}"
        return 1
      if ← Hex.lll.providerActive then
        return 0
      else
        IO.eprintln "providerActive = false after a successful loadProvider"
        return 1
  | _ =>
      IO.eprintln "usage: hexlll_provider_probe absent | present <path>"
      return 2

end LLLProviderProbe
end Hex

@[expose]
def main (args : List String) : IO UInt32 :=
  Hex.LLLProviderProbe.main args
