/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexHenselMathlib.Basic
import HexHenselMathlib.Correctness

/-!
The `HexHenselMathlib` library transfers the executable `HexHensel` surface to
Mathlib's `Polynomial ℤ` API.

The library currently exposes coprimality-lifting infrastructure plus
proof-only Hensel correctness and uniqueness theorem statements used by later
factorization arguments.
-/
