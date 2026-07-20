/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Chain
-- `import all` on the two source modules so `decide` reduces the sanity
-- checks below in the kernel: plain (non-`@[expose]`) defs like `sturmChain`,
-- `evalDyadic`, and `dyadicSign` have opaque bodies across the module
-- boundary, so a `decide` that unfolds them here would get stuck without
-- these. The Array-equality `import all` is the same workaround as Chain.lean.
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain

public section

/-!
Sign variations, Sturm counts, and the isolation certificate types.

`signVar` counts the sign changes of a list of exact integer values under
the zero-skipping convention: drop the zero entries, then count adjacent
pairs of opposite sign. The variation count of `(+, 0, −)` is `1`. This is
the numeric heart of both root-counting engines — the Sturm counts here and
the Descartes count in the Mobius layer both reduce to `signVar` of a list
of exact signs.

The Sturm counts turn `signVar` into a certificate: `sturmCount p (l, u]` is
the sign-variation difference of `p`'s Sturm chain at the two dyadic
endpoints, which counts the real roots in the half-open interval `(l, u]`
exactly, and `rootCount p` is the same difference between `−∞` and `+∞`. A
`RealRootIsolation` bundles an interval with a `decide`-checkable proof that
its Sturm count is `1`; a `RealRootIsolations` bundles an ordered,
pairwise-disjoint array of them whose size matches `rootCount p`, which is
the completeness certificate the companion turns into the semantic
statement. Everything here is exact integer or dyadic arithmetic: no floats,
no error budget.
-/
namespace Hex

/-- Zero-skipping sign variations of a list of exact integer values.

Drop the zero entries, then count the adjacent pairs of opposite sign (the
product is negative). The variation count of `(+, 0, −)` is `1`: the zero is
skipped, leaving one sign change. This is the plain-`List Int` primitive
shared by the Sturm counts below and the Descartes count in the Mobius
layer. -/
@[expose]
def signVar (l : List Int) : Nat :=
  go (l.filter (· != 0))
where
  /-- Count adjacent opposite-sign pairs of an already zero-free list. -/
  go : List Int → Nat
    | a :: b :: rest => (if a * b < 0 then 1 else 0) + go (b :: rest)
    | _ => 0

/-- Zero-skipping sign variations of the Sturm chain evaluated at a dyadic
point `x`.

Every chain element is evaluated at `x` by exact Horner arithmetic
(`evalDyadic`), reduced to its exact sign in `{−1, 0, 1}` (`dyadicSign`), and
the resulting sign list is fed to `signVar`. No rounding and no error budget:
the sign of `q(x)` at a dyadic `x` is exact. -/
@[expose]
def sturmVarAt (chain : Array ZPoly) (x : Dyadic) : Nat :=
  signVar (chain.toList.map (fun q => dyadicSign (q.evalDyadic x)))

/-- Zero-skipping sign variations of the Sturm chain at `+∞`.

At `+∞` the sign of each element is the sign of its leading coefficient, so
no evaluation is needed. The zero polynomial has leading coefficient `0`,
which the zero-skipping convention drops (it never occurs in a genuine chain
element, but the total function tolerates it). -/
@[expose]
def sturmVarPosInf (chain : Array ZPoly) : Nat :=
  signVar (chain.toList.map (fun q => (DensePoly.leadingCoeff q).sign))

/-- Zero-skipping sign variations of the Sturm chain at `−∞`.

At `−∞` the sign of each element is the sign of its leading coefficient times
`(−1)^{deg}`: the leading term dominates, and its sign flips with the parity
of the degree. No evaluation is needed. The zero polynomial has leading
coefficient `0`, dropped by the zero-skipping convention. -/
@[expose]
def sturmVarNegInf (chain : Array ZPoly) : Nat :=
  signVar (chain.toList.map (fun q =>
    (DensePoly.leadingCoeff q).sign *
      (if (DensePoly.degree? q).getD 0 % 2 = 1 then -1 else 1)))

/-- The number of real roots of `p` in the half-open interval
`(I.lower, I.upper]`, as certified by the Sturm chain: the sign-variation
difference between the two endpoints. An `Int` by definition. The companion
proves it equals the root count in the interval (in particular, that it is
nonnegative) for squarefree `p`. -/
@[expose]
def sturmCount (p : ZPoly) (I : DyadicInterval) : Int :=
  (sturmVarAt (ZPoly.sturmChain p) I.lower : Int) -
    sturmVarAt (ZPoly.sturmChain p) I.upper

/-- The total number of real roots of `p`: the sign-variation difference of
its Sturm chain between `−∞` and `+∞`. -/
@[expose]
def rootCount (p : ZPoly) : Nat :=
  sturmVarNegInf (ZPoly.sturmChain p) - sturmVarPosInf (ZPoly.sturmChain p)

/-- Exactly one real root of `p` lies in the half-open interval
`(interval.lower, interval.upper]`, witnessed by a Sturm count of `1`. The
witness is decidable data, dischargeable by `decide`. -/
structure RealRootIsolation (p : ZPoly) where
  /-- The half-open interval `(lower, upper]` containing the root. -/
  interval  : DyadicInterval
  /-- The Sturm count certifies exactly one root in the interval. -/
  count_one : sturmCount p interval = 1

/-- A complete isolation run for `p`: pairwise-disjoint isolations, in
increasing order, one per real root of `p`.

`ordered` records that the isolations are sorted with non-overlapping
half-open intervals — the upper endpoint of each is at most the lower
endpoint of the next. Because the intervals are half-open on the left,
touching at a shared endpoint still leaves them disjoint as sets, so
`ordered` gives pairwise disjointness for free. `complete` records that there
are exactly `rootCount p` of them.

Both invariants are decidable data, so for squarefree `p` the structure
certifies itself no matter which engine produced it: `count_one` puts exactly
one root in each interval, `ordered` makes the intervals disjoint, and
`complete` matches their number to the total root count, so every real root
is captured exactly once. -/
structure RealRootIsolations (p : ZPoly) where
  /-- The isolations, emitted in increasing order. -/
  isolations : Array (RealRootIsolation p)
  /-- The half-open intervals are sorted and non-overlapping. -/
  ordered    : ∀ i j : Fin isolations.size, i < j →
                 isolations[i].interval.upper ≤ isolations[j].interval.lower
  /-- There is exactly one isolation per real root of `p`. -/
  complete   : isolations.size = rootCount p

/-- Final-assembly helper shared by both isolation engines.

An engine emits its isolations in increasing order (a left-first DFS over the
bisection tree), so there is no sorting to do here: `assemble?` only checks
the two `RealRootIsolations` invariants and packages them. `ordered` is
checked directly over `arr`; `complete` is checked against
`sturmVarNegInf chain − sturmVarPosInf chain` on the caller's
already-computed `chain`, and the `hchain : chain = sturmChain p` equality
(passed as `rfl` by a caller whose `chain` is let-bound to `sturmChain p`)
identifies that difference with `rootCount p` without recomputing the chain —
the memoisation discipline of computing the chain once per polynomial.

A `none` here means the engine's output violated its own invariants; the
drivers surface it as engine failure. -/
def assemble? (p : ZPoly) (chain : Array ZPoly) (hchain : chain = ZPoly.sturmChain p)
    (arr : Array (RealRootIsolation p)) : Option (RealRootIsolations p) :=
  if hord : ∀ i j : Fin arr.size, i < j →
      arr[i].interval.upper ≤ arr[j].interval.lower then
    if hcomp : arr.size = sturmVarNegInf chain - sturmVarPosInf chain then
      some ⟨arr, hord, by subst hchain; exact hcomp⟩
    else none
  else none

/-! Sanity checks (kept light; conformance lives in the shared
sub-project). -/

-- `signVar` under the zero-skipping convention.
example : signVar [] = 0 := by decide
example : signVar [1] = 0 := by decide
example : signVar [1, -1] = 1 := by decide
-- The SPEC's example: `(+, 0, −)` has one variation.
example : signVar [1, 0, -1] = 1 := by decide
example : signVar [1, 0, 1] = 0 := by decide
example : signVar [-1, 1, -1] = 2 := by decide
example : signVar [0, 0] = 0 := by decide

-- `sturmChain (x² − 1) = [x² − 1, x, 1]`.
-- At `−2`: evals `(3, −2, 1)` → signs `(+, −, +)` → 2 variations.
example : sturmVarAt (ZPoly.sturmChain (DensePoly.ofCoeffs #[(-1 : Int), 0, 1]))
    (Dyadic.ofInt (-2)) = 2 := by decide
-- At `0`: evals `(−1, 0, 1)` → signs `(−, 0, +)` → 1 variation.
example : sturmVarAt (ZPoly.sturmChain (DensePoly.ofCoeffs #[(-1 : Int), 0, 1]))
    (Dyadic.ofInt 0) = 1 := by decide
-- At `2`: evals `(3, 2, 1)` → signs `(+, +, +)` → 0 variations.
example : sturmVarAt (ZPoly.sturmChain (DensePoly.ofCoeffs #[(-1 : Int), 0, 1]))
    (Dyadic.ofInt 2) = 0 := by decide

-- `sturmCount (x² − 1)` on the half-open intervals. Roots are `±1`.
-- `(−2, 2]`: varAt(−2) − varAt(2) = 2 − 0 = 2 (both roots).
example : sturmCount (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (by decide)) = 2 := by decide
-- `(0, 2]`: varAt(0) − varAt(2) = 1 − 0 = 1 (only the root at `1`).
example : sturmCount (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide)) = 1 := by decide
-- `(−2, 0]`: varAt(−2) − varAt(0) = 2 − 1 = 1. The root at `−1` is captured;
-- the included endpoint `0` is not a root. Half-open on the left counts
-- `−1 ∈ (−2, 0]`.
example : sturmCount (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 0) (by decide)) = 1 := by decide
-- `(1, 2]`: varAt(1) − varAt(2) = 0 − 0 = 0. The root at `1` sits on the
-- excluded left endpoint, so it is not counted (half-open convention). At
-- `1` the chain evals are `(0, 1, 1)` → signs `(0, +, +)` → 0 variations.
example : sturmCount (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 2) (by decide)) = 0 := by decide

-- `rootCount`: total real-root counts read off the leading coefficients and
-- degree parities, no evaluation.
-- `x² − 1`: chain `[x²−1, x, 1]`, −∞ signs `(+, −, +)` → 2, +∞ `(+, +, +)` → 0.
example : rootCount (DensePoly.ofCoeffs #[(-1 : Int), 0, 1]) = 2 := by decide
-- `x² + 1`: no real roots.
example : rootCount (DensePoly.ofCoeffs #[(1 : Int), 0, 1]) = 0 := by decide
-- `x³ − x`: roots `−1, 0, 1`; chain `[x³−x, 3x²−1, x, 1]`, −∞ `(−, +, −, +)` → 3.
example : rootCount (DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1]) = 3 := by decide
-- `x − 5`: one real root; chain `[x−5, 1]`, −∞ `(−, +)` → 1, +∞ `(+, +)` → 0.
example : rootCount (DensePoly.ofCoeffs #[(-5 : Int), 1]) = 1 := by decide
-- Constant `7`: empty chain, `0 − 0 = 0`.
example : rootCount (DensePoly.ofCoeffs #[(7 : Int)]) = 0 := by decide

-- A concrete isolation of the single root of `x − 5` in `(4, 8]`.
-- Chain `[x−5, 1]`; at `4` evals `(−1, 1)` → 1 variation, at `8` `(3, 1)` → 0,
-- so the Sturm count is `1 − 0 = 1`.
example : RealRootIsolation (DensePoly.ofCoeffs #[(-5 : Int), 1]) :=
  ⟨DyadicInterval.mk (Dyadic.ofInt 4) (Dyadic.ofInt 8) (by decide), by decide⟩

-- The whole isolation set for `x − 5` assembles: one isolation, `rootCount = 1`.
example :
    (assemble? (DensePoly.ofCoeffs #[(-5 : Int), 1])
      (ZPoly.sturmChain (DensePoly.ofCoeffs #[(-5 : Int), 1])) rfl
      #[⟨DyadicInterval.mk (Dyadic.ofInt 4) (Dyadic.ofInt 8) (by decide),
        by decide⟩]).isSome = true := by decide

end Hex
