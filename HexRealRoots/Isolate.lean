/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.IsolateSturm
public import HexRealRoots.IsolateDescartes
-- Kernel-reducible `Array`/`Vector` equality; see `HexBasic.ArrayDecEq`.
-- Drop once leanprover/lean4#14270 lands and the toolchain is bumped past it.
public import HexBasic.ArrayDecEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Prec
import all HexRealRoots.IsolateSturm
import all HexRealRoots.IsolateDescartes

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section

/-!
The top-level real-root isolation driver.

`ZPoly.isolateRealRoots?` runs the two engines over the same output type: the fast
Descartes search first, falling back to the provably terminating Sturm
search on its `none`. Both emit `RealRootIsolations p` — pairwise-disjoint,
ordered, Sturm-count-certified isolations, one per real root — so the driver
is a one-liner that keeps whichever engine's certified output arrives first.

The companion `HexRealRootsMathlib` proves `ZPoly.isolateRealRoots? p ≠ none` for squarefree
`p` (`isolateRealRoots?_isSome`), routed through the Sturm engine's completeness
(`isolateSturm?_isSome`); the Descartes engine's own completeness waits on the
unformalised two-circle theorem and no driver-level fact depends on it.
Downstream libraries that need a total function (hex-rcf) combine `ZPoly.isolateRealRoots?`
with `isolateRealRoots?_isSome`.
-/
namespace Hex

/-- Isolate the real roots of `p ∈ ℤ[x]`: try the fast Descartes engine, fall
back to the Sturm engine on its `none`. Both engines produce the same
certified `RealRootIsolations p`, so the result carries a full Sturm-count
witness regardless of which one found it. Returns `none` only when both
engines decline (e.g. non-squarefree input); the companion proves this never
happens for squarefree `p`. -/
def ZPoly.isolateRealRoots? (p : ZPoly) : Option (RealRootIsolations p) :=
  ZPoly.isolateDescartes? p <|> ZPoly.isolateSturm? p

/-! Sanity checks (kept light; conformance lives in the shared sub-project).
Polynomials are kept tiny so kernel reduction of `ZPoly.isolateRealRoots?` is fast; the
higher-degree fixtures live in the `#eval`-driven conformance suite. -/

-- The zero polynomial and constants classify as `none`/isolations-of-a-root
-- exactly as the engines do: `ZPoly.isolateRealRoots?` inherits each engine's contract.
example : ZPoly.isolateRealRoots? (DensePoly.ofCoeffs (#[] : Array Int)) = none := by decide
example : (ZPoly.isolateRealRoots? (DensePoly.ofCoeffs #[(7 : Int)])).isSome = true := by decide

-- The positive-degree fixtures route through the Descartes engine's rational
-- squarefree decision, which the kernel does not reduce across the module
-- boundary (it goes through `ceilSqrt`), so they are exercised by `#eval` in
-- the conformance suite rather than `decide` here. Representative results:
--   `ZPoly.isolateRealRoots? (x − 5)`        ⇒ `some`, 1 isolation
--   `ZPoly.isolateRealRoots? (x² − 1)`       ⇒ `some`, 2 isolations
--   `ZPoly.isolateRealRoots? (x² + 1)`       ⇒ `some`, 0 isolations
--   `ZPoly.isolateRealRoots? ((x−1)²(x+1))`  ⇒ `none` (not squarefree; both engines decline)

end Hex
