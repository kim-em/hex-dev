/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.RREF.Pivot
public import HexRowReduce.RREF.Loop
public import HexRowReduce.RREF.Echelon

public section

/-!
Executable RREF, row-span, and nullspace routines for `hex-matrix`, split by
subject across `HexMatrix/RREF/*`: pivot search and column elimination
(`Pivot`), the `rref` loop with its canonical/no-pivot-zero invariants
(`Loop`), and the `IsEchelonForm`/`IsRREF` contracts with span/nullspace APIs
(`Echelon`). This module re-exports them.
-/
