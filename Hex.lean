/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import Hex.BenchOracle.Flint

/-! Top-level helpers shared by the per-library `Hex<X>` packages.

* `Hex.Conformance.Emit` — JSONL fixture-emission helper used by
  oracle-backed conformance drivers.
* `Hex.BenchOracle.Flint` — shared persistent-subprocess driver
  helper for FLINT comparator wiring (HO-20, consumed by
  HO-21..HO-26). -/
