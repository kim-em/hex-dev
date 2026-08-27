/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/- The settled prime-table generator invocation.  Its stdout is the two
generated regions in `HexPrimality/Table.lean`. -/
import HexPrimality.SieveElab

#rebuild_primeTable 100000 317 14
