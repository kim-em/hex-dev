/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Prec
public import HexRealRoots.Var
-- `import all` on the source modules so `decide` reduces the sanity checks
-- below in the kernel: plain (non-`@[expose]`) defs like `sturmChain`,
-- `evalDyadic`, `dyadicSign`, and `sturmVarAt` have opaque bodies across the
-- module boundary, so a `decide` that unfolds the engine would get stuck
-- without these. The Array-equality `import all` is the same workaround as
-- Var.lean.
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var

public section

/-!
The Sturm isolation engine.

`isolateSturm?` bisects the initial interval `(−rootBound p, rootBound p]`,
dispatching on the exact Sturm count of each sub-interval: count `0` is
discarded, count `1` is emitted as a `RealRootIsolation` (the count is the
witness), and count `≥ 2` bisects at the dyadic midpoint until the depth
budget `isolationDepth p` is exhausted. A left-first depth-first traversal
keeps the emitted isolations in increasing order, so `assemble?` never sorts.

The engine holds to the memoisation discipline of the SPEC: the Sturm chain
is built once per polynomial, and every endpoint's `sturmVarAt` count is
computed once and reused in both child intervals of a bisection. The witness
of an emitted root re-evaluates the two endpoints against the memoised chain
exactly once per emission (at most `deg p` times over a whole run), which is
the honesty price of certifying each isolation's `sturmCount = 1` directly.

Everything is exact integer and dyadic arithmetic. The only rational
computation is the `SquareFreeRat` input test, which classifies whether a
positive-degree input is admissible.
-/
namespace Hex

/-- The depth-first isolation visitor for one sub-interval `(lo, hi]`.

`vlo` and `vhi` are the memoised `sturmVarAt chain` counts at `lo` and `hi`;
they are never recomputed for the same endpoint. The Sturm count of the
interval is `vlo − vhi`, so the dispatch reads off the two memoised counts:

- `vlo = vhi` (count `0`): no root here, emit nothing;
- `vlo = vhi + 1` (count `1`): emit the single isolation. The witness
  re-evaluates the two endpoints against `chain` once; `subst hchain` turns
  the memoised-chain difference into `sturmCount p (lo, hi] = 1`
  definitionally, so no chain construction is repeated per emission;
- otherwise (count `≥ 2` on honest data, or negative on junk): if the depth
  budget is exhausted return `none` (the SPEC's fuel discipline), else bisect
  at the dyadic midpoint, computing the midpoint count `vmid` once and passing
  it to both children. Left-first recursion keeps emissions ordered; a `none`
  from either child aborts the whole run.

Structural recursion on `depth`; both children run at `depth − 1`. -/
private def sturmVisit (p : ZPoly) (chain : Array ZPoly)
    (hchain : chain = ZPoly.sturmChain p) :
    (depth : Nat) → (lo hi : Dyadic) → (vlo vhi : Nat) →
    Option (Array (RealRootIsolation p))
  | depth, lo, hi, vlo, vhi =>
    if vlo = vhi then
      some #[]
    else if vlo = vhi + 1 then
      if hlt : lo < hi then
        if h : (sturmVarAt chain lo : Int) - sturmVarAt chain hi = 1 then
          some #[⟨⟨lo, hi, hlt⟩, by subst hchain; exact h⟩]
        else
          none
      else
        none
    else
      match depth with
      | 0 => none
      | d + 1 =>
        let mid := (lo + hi) >>> (1 : Int)
        let vmid := sturmVarAt chain mid
        match sturmVisit p chain hchain d lo mid vlo vmid with
        | none => none
        | some left =>
          match sturmVisit p chain hchain d mid hi vmid vhi with
          | none => none
          | some right => some (left ++ right)
  termination_by structural depth => depth

/-- The Sturm isolation engine.

Following the SPEC's input contract, `isolateSturm?` classifies its input
explicitly:

- `p = 0` (`degree? = none`): `none`.
- `p` a nonzero constant (`degree? = some 0`): `some` with an empty isolation
  array, matching `rootCount p = 0`. `assemble?` certifies completeness (the
  chain is empty, so `sturmVarNegInf − sturmVarPosInf = 0`).
- `p` of positive degree that is not `SquareFreeRat`: `none`. Callers use
  `Hex.ZPoly.squareFreeCore` to obtain a square-free representative first.
- `p` of positive degree and square-free: build the chain once, run
  `sturmVisit` over `(−rootBound p, rootBound p]` with the depth budget
  `isolationDepth p` and the two initial memoised endpoint counts, then hand
  the ordered emissions to `assemble?`.

A `none` from this engine on square-free positive-degree input has one precise
meaning: an interval at separation depth still reported two or more roots, or
the emitted total disagreed with `rootCount p`. The companion proves both
impossible for square-free input (`isolateSturm?_isSome`), so on that input
the engine is total in the sense that matters. -/
def isolateSturm? (p : ZPoly) : Option (RealRootIsolations p) :=
  match p.degree? with
  | none => none
  | some 0 => assemble? p (ZPoly.sturmChain p) rfl #[]
  | some (_ + 1) =>
    if ZPoly.SquareFreeRat p then
      let chain := ZPoly.sturmChain p
      let R := rootBound p
      let lo := -R
      let hi := R
      let vlo := sturmVarAt chain lo
      let vhi := sturmVarAt chain hi
      match sturmVisit p chain rfl (isolationDepth p) lo hi vlo vhi with
      | none => none
      | some arr => assemble? p chain rfl arr
    else
      none

/-! Sanity checks (kept light; conformance lives in the shared sub-project).

The zero and nonzero-constant cases `decide` in the kernel: neither reaches
the `SquareFreeRat` test. The positive-degree square-free cases do reach it,
and `SquareFreeRat` runs a rational polynomial gcd built on well-founded
recursion, which the kernel cannot reduce, so those cases cannot be `decide`d.
They are verified by `#eval` instead (the compiled interpreter reduces the
well-founded gcd fine); the observed results are recorded in the comments. -/

-- The zero polynomial is rejected (no `SquareFreeRat` test on this branch).
example : isolateSturm? (DensePoly.ofCoeffs (#[] : Array Int)) = none := by decide

-- A nonzero constant isolates with zero roots (empty chain, `rootCount = 0`;
-- no `SquareFreeRat` test on this branch).
example : (isolateSturm? (DensePoly.ofCoeffs #[(7 : Int)])).isSome = true := by decide

-- Positive-degree square-free cases (verified by `#eval`, not `decide`, since
-- `SquareFreeRat`'s rational gcd is well-founded and does not reduce in the
-- kernel):
--   `isolateSturm? (x − 5)`  ⇒ `some` with 1 isolation `(−8, 8]` (which
--                              contains the root `5`; the whole initial
--                              interval already has Sturm count `1`).
--   `isolateSturm? (x² − 1)` ⇒ `some` with 2 isolations `(−4, 0]`, `(0, 4]`,
--                              in increasing order (roots `−1`, `1`).
--   `isolateSturm? (x² + 1)` ⇒ `some` with 0 isolations (no real roots).
--   `isolateSturm? (x³ − x)` ⇒ `some` with 3 isolations `(−2, −1]`, `(−1, 0]`,
--                              `(0, 4]` (roots `−1`, `0`, `1`).
-- The non-square-free `(x − 1)²(x + 1) = x³ − x² − x + 1` is rejected:
--   `isolateSturm? (ofCoeffs #[1, -1, -1, 1]) = none`.

end Hex
