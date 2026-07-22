/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.IsolateSturm
public import HexRealRoots.IsolateDescartes
-- `import all` on the engine modules so `decide` reduces the sanity checks
-- below in the kernel: the non-`@[expose]` engine bodies (`isolateSturm?`,
-- `isolateDescartes?`, the chain/evaluation helpers they call) are opaque
-- across the module boundary otherwise, so a `decide` unfolding them would
-- get stuck. Same workaround as Var.lean and Refine.lean.
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Prec
import all HexRealRoots.IsolateSturm
import all HexRealRoots.IsolateDescartes

public section

/-!
The top-level real-root isolation driver.

`isolate?` runs the two engines over the same output type: the fast
Descartes search first, falling back to the provably terminating Sturm
search on its `none`. Both emit `RealRootIsolations p` — pairwise-disjoint,
ordered, Sturm-count-certified isolations, one per real root — so the driver
is a one-liner that keeps whichever engine's certified output arrives first.

The companion `HexRealRootsMathlib` proves `isolate? p ≠ none` for squarefree
`p` (`isolate?_isSome`), routed through the Sturm engine's completeness
(`isolateSturm?_isSome`); the Descartes engine's own completeness waits on the
unformalised two-circle theorem and no driver-level fact depends on it.
Downstream libraries that need a total function (hex-rcf) combine `isolate?`
with `isolate?_isSome`.
-/
namespace Hex

/-- Isolate the real roots of `p ∈ ℤ[x]`: try the fast Descartes engine, fall
back to the Sturm engine on its `none`. Both engines produce the same
certified `RealRootIsolations p`, so the result carries a full Sturm-count
witness regardless of which one found it. Returns `none` only when both
engines decline (e.g. non-squarefree input); the companion proves this never
happens for squarefree `p`. -/
def isolate? (p : ZPoly) : Option (RealRootIsolations p) :=
  isolateDescartes? p <|> isolateSturm? p

/-! Sanity checks (kept light; conformance lives in the shared sub-project).
Polynomials are kept tiny so kernel reduction of `isolate?` is fast; the
higher-degree fixtures live in the `#eval`-driven conformance suite. -/

-- The zero polynomial and constants classify as `none`/isolations-of-a-root
-- exactly as the engines do: `isolate?` inherits each engine's contract.
example : isolate? (DensePoly.ofCoeffs (#[] : Array Int)) = none := by decide
example : (isolate? (DensePoly.ofCoeffs #[(7 : Int)])).isSome = true := by decide

-- The positive-degree fixtures route through the Descartes engine's rational
-- squarefree decision, which the kernel does not reduce across the module
-- boundary (it goes through `ceilSqrt`), so they are exercised by `#eval` in
-- the conformance suite rather than `decide` here. Representative results:
--   `isolate? (x − 5)`        ⇒ `some`, 1 isolation
--   `isolate? (x² − 1)`       ⇒ `some`, 2 isolations
--   `isolate? (x² + 1)`       ⇒ `some`, 0 isolations
--   `isolate? ((x−1)²(x+1))`  ⇒ `none` (not squarefree; both engines decline)

end Hex
