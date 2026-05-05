import HexHenselMathlib.Basic
import HexHenselMathlib.Conformance
import HexHenselMathlib.Correctness

/-!
The `HexHenselMathlib` library transfers the executable `HexHensel` surface to
Mathlib's `Polynomial ℤ` API.

The library currently exposes coprimality-lifting infrastructure plus
proof-only Hensel correctness and uniqueness theorem statements used by later
factorization arguments.
-/
