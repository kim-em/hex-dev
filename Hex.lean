/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import Hex.BenchOracle.Flint
import Hex.BenchOracle.Pari

/-! Top-level helpers shared by the per-library `Hex<X>` packages.

* `Hex.Conformance.Emit` — JSONL fixture-emission helper used by
  oracle-backed conformance drivers.
* `Hex.BenchOracle.Flint` — shared persistent-subprocess driver
  used by FLINT comparator benchmarks. -/
