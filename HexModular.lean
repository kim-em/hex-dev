/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.Crt
public import HexModular.Euclid
public import HexModular.KernelTests
public import HexModular.Loop
public import HexModular.Recon
public import HexModular.SymMod

public section

/-!
`HexModular` provides symmetric integer representatives, incremental scalar
and vector CRT, bounded and heuristic rational reconstruction, and a fuelled
multi-modular loop. The library is Mathlib-free.
-/
