/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Prec
public import HexRealRoots.Var
public import HexRealRoots.Mobius
-- `import all` on the source modules so `decide` reduces the zero and
-- constant sanity checks below in the kernel: plain (non-`@[expose]`) defs
-- like `sturmChain`, `evalDyadic`, `dyadicSign`, and `sturmVarAt` have opaque
-- bodies across the module boundary, so a `decide` that unfolds the driver
-- would get stuck without these. The Array-equality `import all` is the same
-- workaround as `IsolateSturm.lean`.
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var

public section

/-!
The Descartes isolation engine.

`isolateDescartes?` runs the same bisection search as `isolateSturm?`, but
dispatches each sub-interval on the Descartes variation count
`V := descartesVar (mobiusTransform p (a, b])` together with the exact test
`p(b) = 0`, per the SPEC's five-row table:

| `V` | `p(b) = 0` | action                         |
|-----|------------|--------------------------------|
| 0   | no         | discard                        |
| 0   | yes        | candidate (the root is `b`)    |
| 1   | no         | candidate                      |
| 1   | yes        | bisect (two roots in `(a, b]`) |
| ≥ 2 | either     | bisect                         |

The engine trusts Descartes' rule for nothing: `V` is only a search
heuristic. Every candidate is re-certified by its exact Sturm count, and a
candidate whose count is not `1` aborts the whole engine with `none` — never a
silent discard. Bisection past the depth budget `isolationDepth p` returns
`none`, and a failed final `complete`/`ordered` check in `assemble?` returns
`none`. Descartes' rule makes the discard row sound and the candidate rows
plausible, but nothing here depends on that soundness: the certificates carry
the correctness.

The per-node cost is one Möbius transform (`O(n²)` integer operations via
Taylor shift) versus the Sturm engine's full chain evaluation, which is why
this engine runs first in `isolate?`. The deferred companion theorem
`isolateDescartes?_isSome` (the Obreshkoff two-circle theorem;
Krandick–Mehlhorn 2006) says none of the `none` outcomes happen for
square-free input at this depth budget — in particular a non-real conjugate
pair keeps `V` at `2` on every interval around its real part until the width
shrinks to the order of its imaginary part, which the depth budget reaches.
No other theorem depends on that statement.

Everything is exact integer and dyadic arithmetic. The only rational
computation is the `SquareFreeRat` input test, which classifies whether a
positive-degree input is admissible.
-/
namespace Hex

/-- The depth-first Descartes visitor for one sub-interval `(lo, hi]`.

Unlike `sturmVisit`, no variation counts are memoised across nodes: each
node's work is its own Möbius transform `descartesVar (mobiusTransform p ⟨lo,
hi, _⟩)`, and the `chain` parameter exists only to certify a candidate's Sturm
count. A dependent `if hlt : lo < hi` supplies the interval structure (a
degenerate `lo ≥ hi` node, which bisection never produces, returns `some #[]`).

Per node, with `V` the variation count and `bZero := (p(hi) = 0)`:

- `V = 0`, `¬ bZero`: discard, emit nothing;
- `V = 0`, `bZero`, or `V = 1`, `¬ bZero`: candidate — certify by the exact
  Sturm count `(sturmVarAt chain lo) − sturmVarAt chain hi`. If it is `1` emit
  the isolation (`subst hchain` turns the memoised-chain difference into
  `sturmCount p (lo, hi] = 1` definitionally); otherwise return `none`, which
  aborts the engine (the SPEC's "a candidate whose count is not `1` aborts");
- `V = 1`, `bZero`, or `V ≥ 2`: bisect. Match `depth`: `0` returns `none` (the
  fuel discipline), `d + 1` recurses left then right at the dyadic midpoint.
  Left-first recursion keeps emissions ordered; a `none` from either child
  aborts the whole run.

Structural recursion on `depth`; both children run at `depth − 1`. -/
private def descartesVisit (p : ZPoly) (chain : Array ZPoly)
    (hchain : chain = ZPoly.sturmChain p) :
    (depth : Nat) → (lo hi : Dyadic) →
    Option (Array (RealRootIsolation p))
  | depth, lo, hi =>
    if hlt : lo < hi then
      let V := descartesVar (mobiusTransform p ⟨lo, hi, hlt⟩)
      let bZero : Bool := dyadicSign (p.evalDyadic hi) == 0
      -- The two candidate rows (`V = 0` with `p(hi) = 0`, and `V = 1` with
      -- `p(hi) ≠ 0`) certify by the exact Sturm count and emit on `1`, else
      -- abort the engine with `none`. The discard row is `V = 0` with
      -- `p(hi) ≠ 0`. Everything else (`V = 1` with `p(hi) = 0`, or `V ≥ 2`)
      -- bisects. The three arms are written once each; the bisect must stay
      -- inline (a `let`-bound bisect would be evaluated strictly at every node,
      -- forcing the recursion regardless of dispatch — an exponential blowup).
      if (V == 0 && bZero) || (V == 1 && !bZero) then
        if h : (sturmVarAt chain lo : Int) - sturmVarAt chain hi = 1 then
          some #[⟨⟨lo, hi, hlt⟩, by subst hchain; exact h⟩]
        else
          none
      else if V = 0 then
        some #[]
      else
        match depth with
        | 0 => none
        | d + 1 =>
          let mid := (lo + hi) >>> (1 : Int)
          match descartesVisit p chain hchain d lo mid with
          | none => none
          | some left =>
            match descartesVisit p chain hchain d mid hi with
            | none => none
            | some right => some (left ++ right)
    else
      some #[]
  termination_by structural depth => depth

/-- The Descartes isolation engine.

Following the SPEC's input contract, `isolateDescartes?` classifies its input
exactly as `isolateSturm?` does:

- `p = 0` (`degree? = none`): `none`.
- `p` a nonzero constant (`degree? = some 0`): `some` with an empty isolation
  array, matching `rootCount p = 0`. `assemble?` certifies completeness (the
  chain is empty, so `sturmVarNegInf − sturmVarPosInf = 0`).
- `p` of positive degree that is not `SquareFreeRat`: `none`. Callers use
  `Hex.ZPoly.squareFreeCore` to obtain a square-free representative first.
- `p` of positive degree and square-free: build the chain once, run
  `descartesVisit` over `(−rootBound p, rootBound p]` with the depth budget
  `isolationDepth p`, then hand the ordered emissions to `assemble?`.

The engine trusts Descartes' rule for nothing; it is a search heuristic
wrapped in Sturm certificates. A `none` on square-free positive-degree input
has one of the SPEC's precise meanings: a candidate's Sturm count was not `1`,
an interval bisected past the depth budget, or the emitted total disagreed
with `rootCount p`. The deferred companion theorem `isolateDescartes?_isSome`
(the Obreshkoff two-circle theorem) says none of them happen for square-free
input at this budget, so the driver's completeness — established through the
Sturm engine — never waits on it. The per-node cost is one `O(n²)` Möbius
transform against the Sturm engine's full chain evaluation, which is why this
engine runs first in `isolate?`. -/
def isolateDescartes? (p : ZPoly) : Option (RealRootIsolations p) :=
  match p.degree? with
  | none => none
  | some 0 => assemble? p (ZPoly.sturmChain p) rfl #[]
  | some (_ + 1) =>
    if ZPoly.SquareFreeRat p then
      let chain := ZPoly.sturmChain p
      let R := rootBound p
      match descartesVisit p chain rfl (isolationDepth p) (-R) R with
      | none => none
      | some arr => assemble? p chain rfl arr
    else
      none

/-! Sanity checks (kept light; conformance lives in the shared sub-project).

The zero and nonzero-constant cases `decide` in the kernel: neither reaches
the `SquareFreeRat` test or a Möbius transform. The positive-degree
square-free cases do reach the `SquareFreeRat` rational gcd (well-founded
recursion the kernel cannot reduce), so they are verified by `#eval` and their
results recorded below. Each is cross-checked against `isolateSturm?`: the two
engines must agree on the isolation count (the intervals need not coincide). -/

-- The zero polynomial is rejected (no `SquareFreeRat` test on this branch).
example : isolateDescartes? (DensePoly.ofCoeffs (#[] : Array Int)) = none := by decide

-- A nonzero constant isolates with zero roots (empty chain, `rootCount = 0`;
-- no `SquareFreeRat` test on this branch).
example : (isolateDescartes? (DensePoly.ofCoeffs #[(7 : Int)])).isSome = true := by decide

-- Positive-degree square-free cases (verified by `#eval`, not `decide`, since
-- `SquareFreeRat`'s rational gcd is well-founded and does not reduce in the
-- kernel). Each line records the observed isolation count and confirms it
-- matches `isolateSturm?` on the same input:
--   `isolateDescartes? (x − 5)`      ⇒ `some`, 1 isolation   (Sturm: 1)
--   `isolateDescartes? (x² − 1)`     ⇒ `some`, 2 isolations  (Sturm: 2)
--   `isolateDescartes? (x² + 1)`     ⇒ `some`, 0 isolations  (Sturm: 0)
--   `isolateDescartes? (x³ − x)`     ⇒ `some`, 3 isolations, increasing (Sturm: 3)
--   `isolateDescartes? ((x−1)²(x+1))` ⇒ `none` (not square-free)  (Sturm: none)
--   `isolateDescartes? (2x² − 5x + 2)` ⇒ `some`, 2 isolations  (Sturm: 2)
--       — roots `1/2` and `2`; bisection midpoints hit the root `2` exactly,
--         exercising the `V = 0`-with-`p(b) = 0` candidate row.
--   `isolateDescartes? (x² − x)`     ⇒ `some`, 2 isolations  (Sturm: 2)
--       — roots `0` and `1`, both dyadic; adjacent isolations may share an
--         endpoint (still disjoint, half-open on the left).

end Hex
