/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGFq.Basic

/-!
User-facing canonical finite-field constructors.

This library packages committed Conway-table entries as generic quotient-field
types and exposes optimized packed characteristic-two constructors for
committed binary entries. The public API is defined in `HexGFq.Basic`. The
core conformance checks and the packed-vs-generic cross-check at extension
degrees beyond the committed `(2, 1)` entry live under the `conformance/`
sub-project (`HexGFq.Conformance` and `HexGFq.CrossCheck`), which builds in
the same `lake build`.
-/
