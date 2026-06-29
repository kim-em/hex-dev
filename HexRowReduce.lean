/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.RowEchelon
public import HexRowReduce.RREF

public section

/-!
The `HexRowReduce` library exposes the executable row-reduction stack over the
`HexMatrix` dense core: the row-echelon transform and its elementary-operation
contracts (`RowEchelon`), and the executable RREF loop with its pivot/free-column
partition and span/nullspace APIs (`RREF`). This module re-exports them.
-/
