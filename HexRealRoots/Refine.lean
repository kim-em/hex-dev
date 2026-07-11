/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Var
public import HexRealRoots.Prec
-- `import all` on the source modules so `decide` reduces the sanity checks
-- below in the kernel: plain (non-`@[expose]`) defs like `sturmChain`,
-- `evalDyadic`, `dyadicSign`, `sturmVarAt`, and `twoPow` have opaque bodies
-- across the module boundary, so a `decide` that unfolds them here would get
-- stuck without these. The Array-equality `import all` is the same workaround
-- as Chain.lean and Var.lean.
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Prec

public section

/-!
Isolation refinement by midpoint bisection.

`refine1` bisects an isolation interval `(lower, upper]` at its dyadic
midpoint `m` and keeps the half whose Sturm count is `1`. The half-open
convention removes all endpoint case analysis: a root exactly at `m` lands
in the left half `(lower, m]`, and the counts say so — no comparison against
`m` is ever needed beyond the two Sturm-variation reads. `refineTo` iterates
`refine1` until the interval width drops to at most `2^{−target}`, fueled by
the width gap so the loop is total on any input.

Everything here is exact: the Sturm chain is built once per `refine1` call
and evaluated at dyadic endpoints by exact Horner arithmetic, so each
half-count is an exact integer difference with no rounding.
-/
namespace Hex.RealRootIsolation

variable {p : ZPoly}

/-- Package a certified half-open interval `(lower, upper]` from a
precomputed Sturm chain and a proof that its endpoint sign-variation gap is
`1`, reusing the caller's already-built `chain` so the Sturm count is not
recomputed. The `hchain : chain = ZPoly.sturmChain p` equality (passed as
`rfl` when `chain` is let-bound to `ZPoly.sturmChain p`) identifies the gap
`h` with `sturmCount p (lower, upper]` without rebuilding the chain — the
same memoisation discipline as `assemble?`. -/
private def ofHalf (chain : Array ZPoly) (hchain : chain = ZPoly.sturmChain p)
    (lower upper : Dyadic) (hlt : lower < upper)
    (h : (sturmVarAt chain lower : Int) - sturmVarAt chain upper = 1) :
    RealRootIsolation p :=
  ⟨⟨lower, upper, hlt⟩, by subst hchain; exact h⟩

/-- Bisect an isolation at its dyadic midpoint and keep the half whose Sturm
count is `1`.

One chain construction, then at most four endpoint evaluations decide it: the
midpoint `m` is `(lower + upper) / 2` computed exactly, so a genuine interval
always splits into two nonempty halves. The left half `(lower, m]` is tried
first — its Sturm count is `sturmVarAt chain lower − sturmVarAt chain m`,
phrased directly on the let-bound `chain` so the chain is built once, never
per `sturmCount`. If the left count is `1` it certifies; otherwise the right
half `(m, upper]` is tried the same way. The half-open convention means a root
exactly at `m` lands in the left half `(lower, m]` and its count is `1` there,
so no endpoint comparison against `m` is ever needed.

If neither half certifies — impossible for squarefree `p`, proven unreachable
by the companion `refine1_isolates_same` — the input is returned unchanged, so
the function is total. `refine1` takes no cached chain (its SPEC signature is
fixed), so the chain is rebuilt per call; a cached-chain variant can follow if
profiling demands it. -/
def refine1 (iso : RealRootIsolation p) : RealRootIsolation p :=
  let chain := ZPoly.sturmChain p
  let m := iso.interval.midpoint
  if hlt : iso.interval.lower < m then
    if h : (sturmVarAt chain iso.interval.lower : Int) - sturmVarAt chain m = 1 then
      ofHalf chain rfl iso.interval.lower m hlt h
    else if hltu : m < iso.interval.upper then
      if h' : (sturmVarAt chain m : Int) - sturmVarAt chain iso.interval.upper = 1 then
        ofHalf chain rfl m iso.interval.upper hltu h'
      else iso
    else iso
  else iso

/-- Iterate `refine1` until the interval width is at most `2^{−target}`.

The fuel is `(ceilLog2Dyadic width + target).toNat + 1`. Since
`width ≤ 2^{ceilLog2Dyadic width}` and each honest `refine1` halves the
width, `ceilLog2Dyadic width + target` halvings bring the width to at most
`2^{−target}`; the `.toNat` clamps the already-satisfied case (a
nonpositive gap) to `0`, and the `+ 1` covers the loop's own width test. On
adversarial data that violates the isolation semantics `refine1` returns its
input, and the loop then drains its fuel without shrinking — total either
way, it cannot loop. -/
def refineTo (iso : RealRootIsolation p) (target : Int) : RealRootIsolation p :=
  go ((ceilLog2Dyadic iso.interval.width + target).toNat + 1) iso
where
  /-- Structural fuel drives the loop: stop at fuel `0` or once the width
  condition holds, else refine once and recurse. -/
  go : Nat → RealRootIsolation p → RealRootIsolation p
    | 0, iso => iso
    | k + 1, iso =>
      if iso.interval.width ≤ twoPow (-target) then iso
      else go k (refine1 iso)

/-! Sanity checks (kept light; conformance lives in the shared sub-project).
Polynomials are kept tiny so kernel reduction of `refine1`/`refineTo` is
fast. -/

-- `p = x² − 2`, isolating `√2 ≈ 1.4142` in `(1, 2]`. Chain `[x²−2, x, 1]`;
-- at `1` evals `(−1, 1, 1)` → 1 variation, at `2` `(2, 2, 1)` → 0, so the
-- Sturm count is `1 − 0 = 1`.
example : RealRootIsolation (DensePoly.ofCoeffs #[(-2 : Int), 0, 1]) :=
  ⟨⟨Dyadic.ofInt 1, Dyadic.ofInt 2, by decide⟩, by decide⟩

-- `refine1` on `(1, 2]`: midpoint `3/2`, `√2 < 3/2` so the left half
-- `(1, 3/2]` certifies (count `1 − 0 = 1`).
example : (refine1 (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    ⟨⟨Dyadic.ofInt 1, Dyadic.ofInt 2, by decide⟩, by decide⟩).interval.lower
    = Dyadic.ofInt 1 := by decide
example : (refine1 (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    ⟨⟨Dyadic.ofInt 1, Dyadic.ofInt 2, by decide⟩, by decide⟩).interval.upper
    = (Dyadic.ofInt 3) >>> (1 : Int) := by decide

-- `refine1` again on `(1, 3/2]`: midpoint `5/4 = 1.25 < √2`, so the left half
-- `(1, 5/4]` has count `1 − 1 = 0` and fails; the RIGHT half `(5/4, 3/2]`
-- certifies (count `1 − 0 = 1`).
example : (refine1 (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    ⟨⟨Dyadic.ofInt 1, (Dyadic.ofInt 3) >>> (1 : Int), by decide⟩, by decide⟩).interval.lower
    = (Dyadic.ofInt 5) >>> (2 : Int) := by decide
example : (refine1 (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    ⟨⟨Dyadic.ofInt 1, (Dyadic.ofInt 3) >>> (1 : Int), by decide⟩, by decide⟩).interval.upper
    = (Dyadic.ofInt 3) >>> (1 : Int) := by decide

-- A dyadic root exactly at the midpoint. `p = 2x − 1`, root `1/2`, isolated
-- in `(0, 1]` (chain `[2x−1, 1]`; at `0` evals `(−1, 1)` → 1 variation, at `1`
-- `(1, 1)` → 0). `refine1` keeps the LEFT half `(0, 1/2]`: at `1/2` the chain
-- evals `(0, 1)` → 0 variations, so the left count is `1 − 0 = 1` and the root
-- at the midpoint lands left by the half-open convention.
example : (refine1 (p := DensePoly.ofCoeffs #[(-1 : Int), 2])
    ⟨⟨Dyadic.ofInt 0, Dyadic.ofInt 1, by decide⟩, by decide⟩).interval.lower
    = Dyadic.ofInt 0 := by decide
example : (refine1 (p := DensePoly.ofCoeffs #[(-1 : Int), 2])
    ⟨⟨Dyadic.ofInt 0, Dyadic.ofInt 1, by decide⟩, by decide⟩).interval.upper
    = (Dyadic.ofInt 1) >>> (1 : Int) := by decide

-- `refineTo` on the `x² − 2` isolation with `target = 3`: the loop runs
-- `(1, 2] → (1, 3/2] → (5/4, 3/2] → (11/8, 3/2]`, whose width `1/8` meets
-- `2^{−3}`. Assert the width bound and that the endpoints still bracket `√2`
-- (eval `< 0` at the lower endpoint, `> 0` at the upper).
example : (refineTo (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    ⟨⟨Dyadic.ofInt 1, Dyadic.ofInt 2, by decide⟩, by decide⟩ 3).interval.width
    ≤ twoPow (-3) := by decide
example : dyadicSign (ZPoly.evalDyadic (DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    (refineTo (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
      ⟨⟨Dyadic.ofInt 1, Dyadic.ofInt 2, by decide⟩, by decide⟩ 3).interval.lower) = -1 := by
  decide
example : dyadicSign (ZPoly.evalDyadic (DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    (refineTo (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
      ⟨⟨Dyadic.ofInt 1, Dyadic.ofInt 2, by decide⟩, by decide⟩ 3).interval.upper) = 1 := by
  decide

-- `refineTo` with an already-satisfied target `-2`: the width `1` of `(1, 2]`
-- already meets `2^{2} = 4`, so the loop returns immediately.
example : (refineTo (p := DensePoly.ofCoeffs #[(-2 : Int), 0, 1])
    ⟨⟨Dyadic.ofInt 1, Dyadic.ofInt 2, by decide⟩, by decide⟩ (-2)).interval.width
    ≤ twoPow 2 := by decide

end Hex.RealRootIsolation
