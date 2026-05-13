import Hex.Conformance.Emit
import Hex.BenchOracle.Flint

/-! Top-level helpers shared by the per-library `Hex<X>` packages.

* `Hex.Conformance.Emit` — JSONL fixture-emission helper used by
  oracle-backed conformance drivers.
* `Hex.BenchOracle.Flint` — shared persistent-subprocess driver
  helper for FLINT comparator wiring (HO-20, consumed by
  HO-21..HO-26). -/
