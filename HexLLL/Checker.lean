/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Certificate
public import HexLLL.Interval

public section

/-!
Executable reducedness checkers: the exact integer `lllReduced`, the
fixed-precision `lllReducedInterval`, their cost-predicted dispatch
`lllReducedCheck`, and the bundled external-candidate checker `certCheck`.
-/

namespace Hex

open Hex.Internal

namespace Internal

/-- Working precision (bits) of the interval reducedness checker. The
inequalities being certified carry slack by design: the dispatch requests a
`(requestedDelta δ, requestedEta)`-reduced basis but certifies it against the
weaker `(δ, 11/20)`, so size reduction clears `11/20` by `11/20 − requestedEta`
and Lovász clears `δ` by `(requestedDelta δ − δ)·d[i+1]²`. A fixed precision
decides them on a correctly-reduced candidate; any indecision falls back to
the exact checker rather than failing. The 128-bit width is fixed (independent
of input size) and chosen to comfortably exceed the per-step slack margins for
the documented input families, keeping every enclosure at a small, predictable
arithmetic cost. -/
@[expose]
def intervalPrec : Nat := 128

end Internal

/-- Fixed-precision interval reducedness checker. Computes enclosures of
the Gram-Schmidt data of `b` from its exact integer Gram matrix and accepts
only when every independence, size-reduction, and Lovász inequality is
decided with the enclosure strictly on the correct side. `false` means
"not reduced or indecisive at this precision": callers must fall back to
the exact checker `lllReduced`, which keeps completeness structural.
Soundness (`lllReducedInterval_sound`, HexLLLMathlib) entails
`b.independent ∧ isLLLReduced b δ η` at the exact rational parameters. -/
@[expose]
def lllReducedInterval (b : Matrix Int n m) (δ η : Rat) : Bool :=
  let S : Int := (2 : Int) ^ intervalPrec
  let g := (Matrix.gramMatrix b).rows.toArray.map Vector.toArray
  match IntervalGS.pass S g n with
  | none => false
  | some (mus, bstars) =>
      IntervalGS.sizeOK S η mus n && IntervalGS.lovaszOK S δ mus bstars n

/-- Executable integer `Bool` reducedness checker over the `GramSchmidt.Int`
representation: leading Gram determinants `d` and integer scaled Gram-Schmidt
coefficients `ν`.

Verifies, over integer arithmetic only:

* **independence**: every `d[k+1]` is positive (`k < n`);
* **size-reduced at `η`**: `η.den · |ν[i][j]| ≤ η.num · d[j+1]` for all `j < i`
  — the integer form of `|μ| ≤ η`;
* **integer Lovász at `δ`**: `δ.den · (d[i+2] · d[i] + ν[i+1][i]²) ≥
  δ.num · d[i+1]²` for all `i + 1 < n`.

No validity hypothesis on `η` is required: a malformed `η` (e.g. negative) is
incompatible with a positive `d[j+1]` and the size-reduced bound, so the
checker simply returns `false`. Soundness
(`lllReduced_sound`, HexLLLMathlib) bridges to the rational predicate
`isLLLReduced` via the integer correspondence
(`Hex.GramSchmidt.Int.scaledCoeffs_eq`, `basis_normSq`, `gramDet_pos`). -/
@[expose]
def lllReduced (b : Matrix Int n m) (δ η : Rat) : Bool :=
  let gs := GramSchmidt.Int.data b
  let d := gs.d
  let ν := gs.ν
  let independent :=
    (List.finRange n).all fun k =>
      decide (0 < d.get ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)
  let sizeReduced :=
    (List.finRange n).all fun i =>
      (List.finRange i.val).all fun j =>
        let iFin : Fin n := i
        let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
        let νij : Int := (ν.getRow iFin).get jFin
        let dj1 : Nat := d.get ⟨j.val + 1, Nat.succ_lt_succ
          (Nat.lt_trans j.isLt i.isLt)⟩
        decide ((η.den * νij.natAbs : Int) ≤ η.num * (dj1 : Int))
  let lovasz :=
    (List.finRange n).all fun i =>
      if hi : i.val + 1 < n then
        let iFin : Fin n := i
        let ip1Fin : Fin n := ⟨i.val + 1, hi⟩
        let di : Nat := d.get ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        let di1 : Nat := d.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        let di2 : Nat := d.get ⟨i.val + 2, Nat.succ_lt_succ hi⟩
        let B : Int := (ν.getRow ip1Fin).get iFin
        decide
          (δ.den * ((di2 : Int) * (di : Int) + B ^ 2) ≥
            δ.num * (di1 : Int) ^ 2)
      else
        true
  independent && sizeReduced && lovasz

namespace Internal

/-- Outcome of one certified-dispatch reducedness decision: decided by the
interval checker, decided by the exact checker because the size predictor
chose it (`exactPrimary`), or referred to the exact checker after an
indecisive interval pass (`exactFallback`). -/
inductive CheckerOutcome where
  | interval
  | exactPrimary
  | exactFallback
deriving Repr, BEq

/-- Tally of reducedness decisions, distinguishing enclosure-accepted from
the two exact-checker modes. Mirrors `LLLProvider.Diagnostics` for the
dispatch outcomes; this tally is the observability hook that lets
measurements verify the dispatch predictor and confirm the interval path
never reached indecision (`exactFallback = 0`). -/
structure CheckerTally where
  interval : Nat := 0
  exactPrimary : Nat := 0
  exactFallback : Nat := 0
deriving Repr, BEq, Inhabited

initialize checkerTallyRef : IO.Ref CheckerTally ← IO.mkRef {}

/-- Reset the certified-dispatch reducedness tally to zero. Bench and
conformance harnesses call this before a measured run so the subsequent
`checkerTally` snapshot describes only that run's interval/exact routing. -/
@[expose]
def resetCheckerTally : IO Unit :=
  checkerTallyRef.set {}

/-- Read the certified-dispatch reducedness tally accumulated since the last
`resetCheckerTally`. The counts expose whether calls were accepted by the
interval checker, sent directly to the exact checker, or needed an exact
fallback after interval indecision. -/
@[expose]
def checkerTally : IO CheckerTally :=
  checkerTallyRef.get

private def bumpChecker (t : CheckerTally) : CheckerOutcome → CheckerTally
  | .interval => { t with interval := t.interval + 1 }
  | .exactPrimary => { t with exactPrimary := t.exactPrimary + 1 }
  | .exactFallback => { t with exactFallback := t.exactFallback + 1 }

/-- Side-effecting tally bump callable from pure code; definitionally the
continuation `k`, with an `@[implemented_by]` side effect in compiled code.
The continuation value is returned *through* `unsafeBaseIO`, so the compiler
cannot eliminate the effect as an unused pure binding (the
`match unsafeBaseIO … with | () => k` shape of `LLLProvider.withRecordOutcome`
is erasable and its tally is known not to fire eagerly; see the workaround
comment on `runDispatchedFirstShortVectorChecksum`). -/
unsafe def withRecordCheckerOutcomeImpl {α : Type} (o : CheckerOutcome) (k : α) : α :=
  unsafeBaseIO do
    checkerTallyRef.modify (fun t => bumpChecker t o)
    pure k

/-- Pure-facing wrapper that records one reducedness-dispatch outcome in
compiled code and otherwise returns `k`. This keeps the checker API usable from
pure code while still giving benchmark harnesses routing diagnostics. -/
@[expose, implemented_by withRecordCheckerOutcomeImpl]
def withRecordCheckerOutcome {α : Type} (_o : CheckerOutcome) (k : α) : α := k

/-- Dispatch threshold of the size predictor `intervalWins`, as a multiple
of the working precision. Derived from the per-operation cost ratio of the
two checkers: the exact `d`/`ν` checker performs ~`n³/3` multiplications on
operands averaging ~`n·maxDiagBits/4` bits, while the interval pass
performs ~`n³/6` products on fixed `(intervalPrec + maxDiagBits)`-bit
mantissas, so enclosures win once `n·maxDiagBits` exceeds a fixed multiple
of `intervalPrec + maxDiagBits`. On the two committed bench families this
crosses over between n=25 and n=30 for harsh-cubic and between n=150 and
n=180 for random-bounded (paired bench on `carica`). The boundary rungs are
entangled: lowering the constant to pull harsh-cubic n=25 (where the
interval pass runs ~10% faster, about 0.5 ms) onto the interval side also
pulls random-bounded n=150 there, where the exact checker runs ~2% faster.
On that ~360 ms rung the ~7 ms cost outweighs the harsh-cubic saving, so the
constant stays at the value that keeps random-bounded n=150 on the exact
side and minimizes total absolute misroute cost across both families. -/
@[expose]
def dispatchFactor : Nat := 16

/-- `Nat.log2` (floor of the base-2 log) of the largest squared row norm. The
Gram diagonal dominates all Gram entries by Cauchy-Schwarz, so this single scalar
bounds the operand size of every checker and reducer pass. `O(n·m)` work —
negligible against either. A deterministic function of the input alone, so the
dispatches that read it keep per-input timing deterministic. -/
@[expose]
def maxDiagBits (b : Matrix Int n m) : Nat :=
  Fin.foldl n
    (fun acc i => max acc ((b.row i).normSq).natAbs.log2)
    0

/-- Size predictor for the reducedness dispatch: `true` when the
fixed-precision interval pass is predicted to beat the exact integer
checker on this input. Reads only `maxDiagBits`, so the predictor is a
function of the input alone, never of checker indecision, keeping per-input
timing deterministic. -/
@[expose]
def intervalWins (b : Matrix Int n m) : Bool :=
  let bits := maxDiagBits b
  decide (n * bits ≥ dispatchFactor * (intervalPrec + bits))

end Internal

/-- Reducedness clause of the certified dispatch. On the same integer
`d`/`ν` data, two checkers can decide reducedness: the exact integer
checker `lllReduced`, always complete, and a faster fixed-precision
interval pass. The size predictor `intervalWins` picks which to run first;
when the interval pass is indecisive it falls back to the exact checker,
so completeness stays structural rather than numerical. Records each
decision in the checker tally, distinguishing all three outcomes. -/
@[expose]
def lllReducedCheck (b : Matrix Int n m) (δ η : Rat) : Bool :=
  if intervalWins b then
    if lllReducedInterval b δ η then
      withRecordCheckerOutcome .interval true
    else
      withRecordCheckerOutcome .exactFallback (lllReduced b δ η)
  else
    withRecordCheckerOutcome .exactPrimary (lllReduced b δ η)

/-- Executable certified-dispatch checker: verifies that `(B', U, V)` is a valid
external candidate for reducing `B`, i.e. `B` and `B'` generate the same integer
row lattice (witnessed by `U`, `V`) and `B'` is `(δ, η)`-reduced.

Composes the Mathlib-free Bool checkers `Matrix.sameLatticeCert` and
`lllReducedCheck` (interval decision with exact `lllReduced` fallback).
Soundness (`certCheck_sound`, HexLLLMathlib) entails the property triple
`(same lattice, B' independent, isLLLReduced B' δ η)` and is the single
trusted bridge that the certified-dispatch path of `lll` depends on. -/
@[expose]
def certCheck (B B' : Matrix Int n m) (U V : Matrix Int n n) (δ η : Rat) : Bool :=
  Matrix.sameLatticeCert B B' U V && lllReducedCheck B' δ η

end Hex
