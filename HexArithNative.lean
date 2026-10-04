/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

/-! The root of `HexArithNative`, the library carrying HexArith's C objects (see
`PLAN/Conventions.md`). It imports nothing: it exists so the library has a single
root named after it, which makes Lake load the library as a plugin. The modules
the library owns are listed by its `globs`, and an import between two of them
would make Lake link that module on its own, without the C objects. -/
