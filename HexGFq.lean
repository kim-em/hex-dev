import HexGFq.Basic
import HexGFq.Conformance
import HexGFq.CrossCheck

/-!
User-facing canonical finite-field constructors.

This library packages committed Conway-table entries as generic quotient-field
types and exposes optimized packed characteristic-two constructors for
committed binary entries. The public API is defined in `HexGFq.Basic`; this
root also imports the core conformance checks plus the packed-vs-generic
cross-check at extension degrees beyond the committed `(2, 1)` entry.
-/
