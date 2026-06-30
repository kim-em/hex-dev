/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL

public section

/-!
Compatibility re-export: the `HexLLL` surface, formerly a single
`HexLLL.Basic` module, now lives in dependency-ordered modules aggregated
by the `HexLLL` umbrella. This shim keeps `import HexLLL.Basic` working.
-/
