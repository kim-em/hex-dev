/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Native
public import HexLLL.Checker

public section

/-!
The approximation-steered reducer. `SteeredState` drives the exact
integer row operations from an untrusted floating-point Gram-Schmidt
approximation (the floats never enter a proof); `lllSteered` certifies
the candidate at `(δ, 11/20)` and falls back to `lllNative` on failure.
-/

namespace Hex

open Hex.Internal

/-! ## Approximation-steered native reducer

The steered reducer drives the *exact* integer row operations of the native
algorithm (`GramSchmidt.Int.sizeReduce`, `GramSchmidt.Int.adjacentSwap`) from an
*untrusted* floating-point Gram-Schmidt approximation. The basis `b` is the only
proof-relevant field of `SteeredState`; the `Float` fields `mu`/`bb` choose which
row operation to apply and never enter any proof, so lattice equality of the
output holds by construction (every step is a proven lattice-preserving basis
operation) regardless of the approximation's numerical behaviour. The output is
certified post hoc at `(δ, 11/20)`; on certification failure the public `lll`
falls back to the exact `d`/`ν` reducer `lllNative`. The steered path therefore
materializes no exact Gram-Schmidt state — exact `d`/`ν` data appears only in the
fallback. -/

namespace Internal

/-- Untrusted floating-point Gram-Schmidt state steering the native reducer.
`b` is the exact integer basis (the only proof-relevant field). `mu[i][j]` (for
`j < i`) approximates the Gram-Schmidt coefficient `μ[i][j]` and `bb[i]`
approximates `‖b*_i‖²`; both are untrusted and never enter a proof. -/
structure SteeredState (n m : Nat) where
  /-- The exact integer basis — the only proof-relevant field. -/
  b  : Matrix Int n m
  /-- Untrusted `Float` approximations of the Gram-Schmidt coefficients
  `μ[i][j]` (for `j < i`). -/
  mu : Array (Array Float)
  /-- Untrusted `Float` approximations of the squared norms `‖b*_i‖²`. -/
  bb : Array Float

namespace SteeredState

/-- Round to the nearest integer (ties away from zero). Steers only; soundness
never depends on the rounded value. -/
@[expose, inline] def fRound (x : Float) : Int := (Float.floor (x + 0.5)).toInt64.toInt

/-- Initial state: exact integer basis `b`, with `mu`/`bb` from one float
Cholesky pass over the exact Gram entries `⟨b_i, b_j⟩`. -/
@[expose]
def init (b : Matrix Int n m) : SteeredState n m :=
  let rows := b.rows.toArray
  let (mu, bb) := Id.run do
    let mut mu : Array (Array Float) := Array.replicate n (Array.replicate 0 0.0)
    let mut bb : Array Float := Array.replicate n 0.0
    for i in [0:n] do
      let mut c : Array Float := Array.replicate (i + 1) 0.0
      let mut mui : Array Float := Array.replicate i 0.0
      for j in [0:i+1] do
        let mut s := Float.ofInt (rows[i]!.dotProduct rows[j]!)
        let murow := if j == i then mui else mu[j]!
        for l in [0:j] do
          s := s - murow[l]! * c[l]!
        c := c.set! j s
        if j < i then
          let bj := bb[j]!
          mui := mui.set! j (if bj > 0.0 then s / bj else 0.0)
      mu := mu.set! i mui
      bb := bb.set! i c[i]!
    return (mu, bb)
  { b := b, mu := mu, bb := bb }

/-- Building the initial steered state preserves the basis: `init` only populates
the float `mu`/`bb` approximation and copies `b` through unchanged. -/
@[simp, grind =] theorem init_b (b : Matrix Int n m) : (init b).b = b := rfl

/-- Conditioning test on the float Gram-Schmidt: `true` when every approximate
squared norm `bb[i] ≈ ‖b*_i‖²` came out strictly positive.

A genuine Gram-Schmidt squared norm is strictly positive (the rows are
independent), so a non-positive `bb[i]` is a definitive signature that `Float64`
catastrophic cancellation has corrupted the approximation on this basis: the
initial `bb[i]` is formed by subtracting `Σ μ² · c` from `⟨b_i, b_i⟩`, and when
the true `‖b*_i‖²` is many mantissa bits smaller than those terms the difference
loses all significance and can even go negative. Steering from such a corrupted
approximation makes wrong swap and size-reduction decisions, so the exact-integer
candidate almost always misses `(δ, 11/20)`-certification and the whole steered
attempt is wasted before falling back to the exact reducer.

This is an empirically-calibrated routing heuristic, not a theorem: soundness
never depends on it (a candidate that does slip through still certifies, and any
basis routed here still gets an exact reduction). The four structured worst-case
families (ajtai / q-ary / ntru / knapsack) have a Gram-Schmidt dynamic range far
exceeding the 53-bit mantissa and produce many non-positive `bb[i]` (13+ of 32 on
the smallest steered rungs), all of which fail certification; the near-orthogonal
random-bounded and width-bound harsh-cubic families produce none across every
committed rung and seed, and all certify. Reading the signs is `O(n)` on the
`init` the steered path already builds. -/
@[expose]
def wellConditioned (s : SteeredState n m) : Bool :=
  s.bb.all fun x => decide (0.0 < x)

/-- Recompute `mu` row `k` and `bb[k]` from the exact Gram entries `⟨b_k, b_j⟩`
and the stored approximation of rows `< k`. The basis is unchanged. This is the
drift-control step: each working row's coefficients are recomputed from the exact
integer basis, so float error never accumulates across the run. -/
@[expose]
def refreshRow (s : SteeredState n m) (k : Nat) : SteeredState n m :=
  let rows := s.b.rows.toArray
  let (muk, bk) := Id.run do
    let mut c : Array Float := Array.replicate (k + 1) 0.0
    let mut muk : Array Float := Array.replicate k 0.0
    for j in [0:k+1] do
      let mut sm := Float.ofInt (rows[k]!.dotProduct rows[j]!)
      let murow := if j == k then muk else s.mu[j]!
      for l in [0:j] do
        sm := sm - murow[l]! * c[l]!
      c := c.set! j sm
      if j < k then
        let bj := s.bb[j]!
        muk := muk.set! j (if bj > 0.0 then sm / bj else 0.0)
    return (muk, c[k]!)
  { b := s.b, mu := s.mu.set! k muk, bb := s.bb.set! k bk }

/-- Refreshing row `k` recomputes only the float `mu`/`bb` approximation from the
exact Gram entries, so the integer basis `.b` is left unchanged. -/
@[simp, grind =] theorem refreshRow_b (s : SteeredState n m) (k : Nat) :
    (s.refreshRow k).b = s.b := rfl

/-- Single-column size reduction `b_k ← b_k − r·b_j` with `r` the rounded float
coefficient `μ[k][j]`. The basis update is the exact integer
`GramSchmidt.Int.sizeReduce`; `mu` row `k` is updated incrementally. -/
@[expose]
def reduceColumn (s : SteeredState n m) (j k : Fin n) (_hjk : j.val < k.val) :
    SteeredState n m :=
  let r := fRound ((s.mu[k.val]!)[j.val]!)
  if r = 0 then s
  else
    let rf := Float.ofInt r
    let muj := s.mu[j.val]!
    { b := GramSchmidt.Int.sizeReduce s.b j k r
      mu := s.mu.modify k.val fun muk => Id.run do
        let mut row := muk
        for i in [0:j.val] do
          row := row.set! i (row[i]! - rf * muj[i]!)
        row := row.set! j.val (row[j.val]! - rf)
        return row
      bb := s.bb }

/-- Size-reduce row `k` against rows `k-1, …, 0`. -/
@[expose]
def sizeReduce (s : SteeredState n m) (k : Nat) : SteeredState n m :=
  if hk : k < n then
    let kFin : Fin n := ⟨k, hk⟩
    ((List.finRange k).reverse).foldl
      (fun state j =>
        reduceColumn state ⟨j.val, Nat.lt_trans j.isLt hk⟩ kFin j.isLt)
      s
  else s

/-- Swap adjacent rows `k-1` and `k`. The basis update is the exact integer
`GramSchmidt.Int.adjacentSwap`; `mu`/`bb` are updated by the float swap
formulas (Cohen 2.6.3, rational form). -/
@[expose]
def swap (s : SteeredState n m) (k : Nat) : SteeredState n m :=
  if hk : k < n then
    if hk0 : 0 < k then
      let kFin : Fin n := ⟨k, hk⟩
      let km1 := k - 1
      let (mu', bb') := Id.run do
        let mut mu := s.mu
        let mut bb := s.bb
        let μ := (mu[k]!)[km1]!
        let Bkm1 := bb[km1]!
        let Bk := bb[k]!
        let newBkm1 := Bk + μ * μ * Bkm1
        let newMuKkm1 := if newBkm1 > 0.0 then μ * Bkm1 / newBkm1 else 0.0
        let newBk := if newBkm1 > 0.0 then Bkm1 * Bk / newBkm1 else 0.0
        for i in [k+1:n] do
          mu := mu.modify i fun row =>
            let t := row[k]!
            let nK := row[km1]! - μ * t
            let nKm1 := t + newMuKkm1 * nK
            (row.set! k nK).set! km1 nKm1
        let mut pKm1 : Array Float := Array.replicate km1 0.0
        let mut pK : Array Float := Array.replicate km1 0.0
        for j in [0:km1] do
          pKm1 := pKm1.set! j (mu[km1]!)[j]!
          pK := pK.set! j (mu[k]!)[j]!
        mu := mu.modify km1 fun row => Id.run do
          let mut r := row
          for j in [0:km1] do r := r.set! j pK[j]!
          return r
        mu := mu.modify k fun row => Id.run do
          let mut r := row
          for j in [0:km1] do r := r.set! j pKm1[j]!
          r := r.set! km1 newMuKkm1
          return r
        bb := bb.set! km1 newBkm1
        bb := bb.set! k newBk
        return (mu, bb)
      { b := GramSchmidt.Int.adjacentSwap s.b kFin hk0, mu := mu', bb := bb' }
    else s
  else s

/-- The per-iteration preparation step: optionally refresh the working row from
the exact Gram, then size-reduce it. Factored out so the loop proof can treat the
prepared state opaquely (only its lattice equality with `s` matters). -/
@[expose]
def prep (period : Nat) (s : SteeredState n m) (k cnt : Nat) : SteeredState n m :=
  (if period == 0 || cnt % period == 0 then s.refreshRow k else s).sizeReduce k

/-- Fuel-bounded outer steered loop, mirroring `lllLoop` but driven by the float
approximation. `period` controls how often the working row is refreshed from the
exact Gram (`0` = every visit). `δsteer` is the (untrusted) float Lovász
threshold; steering at a stricter `δ` than the certification target gives the
exact certifier margin against float slop. -/
@[expose]
def loop (δsteer : Float) (period : Nat) (s : SteeredState n m) (k cnt : Nat) :
    Nat → SteeredState n m
  | 0 => s
  | fuel + 1 =>
    if _hk : k < n then
      let s := prep period s k cnt
      if 0 < k then
        let km1 := k - 1
        let mukk := (s.mu[k]!)[km1]!
        if δsteer * s.bb[km1]! ≤ s.bb[k]! + mukk * mukk * s.bb[km1]! then
          loop δsteer period s (k + 1) (cnt + 1) fuel
        else
          loop δsteer period (s.swap k) (max km1 1) (cnt + 1) fuel
      else
        loop δsteer period s (k + 1) (cnt + 1) fuel
    else s

/-- Drift-free final sweep: refresh each row from the exact Gram and size-reduce
it, so the returned basis is genuinely size-reduced regardless of in-loop drift. -/
@[expose]
def finalSweep (s : SteeredState n m) : SteeredState n m :=
  (List.finRange n).foldl (fun st k => (st.refreshRow k.val).sizeReduce k.val) s

/-- Hadamard-based integer fuel bound: `3·Σ bitlen(‖b_i‖²)` advances per level.
Computed from the exact basis only (no Gram-determinant state). -/
@[expose]
def fuel (b : Matrix Int n m) : Nat :=
  let rows := b.rows.toArray
  Id.run do
    let mut s := 0
    for i in [0:n] do
      s := s + (rows[i]!.dotProduct rows[i]!).natAbs.log2 + 1
    return (3 * s + 1) * (n + 1)

end SteeredState

/-- Run the approximation-steered reducer: init float GSO, run the fuel-bounded
steered loop, then the drift-free final sweep, returning the exact reduced basis.
Steers with `δsteer = (δ + 2)/3` (stricter than the certification `δ`), `4/3` the
`(δ + 1)/2` margin: the wider gap absorbs more of the float `bb`/`mu` drift that
the periodic refresh leaves between exact recomputations, widening the slack the
final size-reduced basis has against the public-`δ` certification. This is a
best-effort heuristic, not a guarantee — `lllSteered` still certifies the output
and falls back to the exact reducer if it misses. Empirically (issue #6806)
`(δ + 2)/3` certifies the committed random-bounded and harsh-cubic ladders and
random-bounded n=30 across seeds 1..12, with one off-ladder residual at rb
n=65/seed=9 (where `(δ + 1)/2` also fails). It is the cheapest measured margin
that both certifies that binding set and keeps the extra-swap cost on the
already-steered rungs within 3% (the larger `(δ + 3)/4` is equally robust but
costs ~5% on random-bounded n=45). A stricter `δsteer` does not monotonically
help robustness or cost, because it steers a different swap trajectory through
different float-rounding boundaries. -/
@[expose]
def steeredReduceFrom (s0 : SteeredState n m) (δ : Rat) : Matrix Int n m :=
  let δf : Float := Float.ofInt δ.num / Float.ofNat δ.den
  let δsteer : Float := (δf + 2.0) / 3.0
  let s := SteeredState.loop δsteer 16 s0 1 0 (SteeredState.fuel s0.b)
  (SteeredState.finalSweep s).b

/-- Run the approximation-steered reducer by building the float GSO once with
`init` and driving the loop and final sweep from it. `lllSteered` builds the same
initial state, inspects its conditioning, and calls `steeredReduceFrom` directly
to avoid a second `init`. -/
@[expose]
def steeredReduce (b : Matrix Int n m) (δ : Rat) : Matrix Int n m :=
  steeredReduceFrom (SteeredState.init b) δ

/-! ### Lattice preservation of the steered reducer

Every `SteeredState` operation either leaves `.b` unchanged or applies one of the
proven lattice-preserving basis operations, so the steered output generates the
same lattice as the input — by construction, with no dependence on the `Float`
approximation. These proofs mirror the corresponding `LLLState` lemmas. -/

namespace SteeredState

/-- The single-column size reduction `reduceColumn` preserves the lattice: since
it adds an integer multiple of row `j` to row `k`, the resulting basis spans the
same integer lattice, so `v` is a member of the new basis exactly when it was a
member of the old one. -/
@[grind =] theorem reduceColumn_memLattice_iff
    (s : SteeredState n m) (j k : Fin n) (hjk : j.val < k.val) (v : Vector Int m) :
    Matrix.memLattice (s.reduceColumn j k hjk).b v ↔ Matrix.memLattice s.b v := by
  unfold reduceColumn
  by_cases hr : fRound ((s.mu[k.val]!)[j.val]!) = 0
  · rw [if_pos hr]
  · rw [if_neg hr]
    have hne : j ≠ k := fun h => Nat.lt_irrefl j.val (h ▸ hjk)
    exact rowAdd_memLattice_iff s.b hne _ v

/-- Folding `reduceColumn` over a list of source columns preserves the lattice:
each step adds an integer multiple of one row to row `k`, so by induction the
whole pass leaves the spanned integer lattice unchanged. Lifts
`reduceColumn_memLattice_iff` to the column sweep performed by size reduction. -/
private theorem sizeReduce_foldl_memLattice_iff (s : SteeredState n m) (k : Nat) (hk : k < n)
    (xs : List (Fin k)) (v : Vector Int m) :
    Matrix.memLattice
        (xs.foldl
          (fun state j =>
            reduceColumn state ⟨j.val, Nat.lt_trans j.isLt hk⟩ ⟨k, hk⟩ j.isLt)
          s).b v ↔ Matrix.memLattice s.b v := by
  induction xs generalizing s with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact reduceColumn_memLattice_iff s _ _ j.isLt v

/-- Size-reducing row `k` against every earlier row preserves the lattice: it is a
fold of lattice-preserving `reduceColumn` steps, so the spanned lattice (and hence
membership of `v`) is unchanged. -/
@[grind =] theorem sizeReduce_memLattice_iff (s : SteeredState n m) (k : Nat) (v : Vector Int m) :
    Matrix.memLattice (s.sizeReduce k).b v ↔ Matrix.memLattice s.b v := by
  unfold sizeReduce
  by_cases hk : k < n
  · rw [dif_pos hk]
    exact sizeReduce_foldl_memLattice_iff s k hk (List.finRange k).reverse v
  · rw [dif_neg hk]

/-- The adjacent-row swap step preserves the lattice: exchanging rows `k − 1` and
`k` only reorders the basis, so it spans the same integer lattice and membership of
`v` is unchanged. -/
@[grind =] theorem swap_memLattice_iff (s : SteeredState n m) (k : Nat) (v : Vector Int m) :
    Matrix.memLattice (s.swap k).b v ↔ Matrix.memLattice s.b v := by
  unfold swap
  by_cases hk : k < n
  · rw [dif_pos hk]
    by_cases hk0 : 0 < k
    · rw [dif_pos hk0]
      simpa [GramSchmidt.Int.adjacentSwap] using
        rowSwap_memLattice_iff s.b (GramSchmidt.prevRow ⟨k, hk⟩ hk0) ⟨k, hk⟩ v
    · rw [dif_neg hk0]
  · rw [dif_neg hk]

/-- The per-visit `prep` step preserves the lattice: an optional `refreshRow`
(which leaves `.b` fixed) followed by a `sizeReduce` of row `k`, both
lattice-preserving, so membership of `v` is unchanged. -/
@[grind =] theorem prep_memLattice_iff (period : Nat) (s : SteeredState n m) (k cnt : Nat)
    (v : Vector Int m) :
    Matrix.memLattice (prep period s k cnt).b v ↔ Matrix.memLattice s.b v := by
  unfold prep; grind

-- Keep the heavy `Float` computations opaque to the loop proof; the `.b`
-- projection is fully characterized by the `_memLattice_iff` lemmas above, so the
-- proof never needs to reduce the approximate Gram-Schmidt arithmetic.
attribute [irreducible] refreshRow reduceColumn sizeReduce swap prep

/-- The fuel-bounded steered loop preserves the lattice: every iteration applies
only `prep` and `swap`, each lattice-preserving, so however the float steering
chooses to advance or swap, the spanned lattice (and membership of `v`) is
unchanged across the whole run. -/
@[grind =] theorem loop_memLattice_iff (δsteer : Float) (period : Nat) (s : SteeredState n m)
    (k cnt : Nat) (fuel : Nat) (v : Vector Int m) :
    Matrix.memLattice (loop δsteer period s k cnt fuel).b v ↔
      Matrix.memLattice s.b v := by
  induction fuel generalizing s k cnt with
  | zero => rfl
  | succ f ih =>
    by_cases hk : k < n
    · simp only [loop, dif_pos hk]
      -- Replace the prepared state by a fresh variable `p`; only its lattice
      -- equality with `s` matters, keeping the float arithmetic out of the proof.
      have hp_lat := prep_memLattice_iff period s k cnt v
      generalize prep period s k cnt = p at hp_lat ⊢
      by_cases hk0 : 0 < k
      · simp only [if_pos hk0]
        split
        · exact (ih p (k + 1) (cnt + 1)).trans hp_lat
        · exact (ih (p.swap k) (max (k - 1) 1) (cnt + 1)).trans
            ((swap_memLattice_iff p k v).trans hp_lat)
      · simp only [if_neg hk0]
        exact (ih p (k + 1) (cnt + 1)).trans hp_lat
    · simp only [loop, dif_neg hk]

/-- The drift-free final sweep preserves the lattice: it folds a `refreshRow`
(no change to `.b`) and a `sizeReduce` over every row, both lattice-preserving, so
membership of `v` is unchanged. -/
@[grind =] theorem finalSweep_memLattice_iff (s : SteeredState n m) (v : Vector Int m) :
    Matrix.memLattice (finalSweep s).b v ↔ Matrix.memLattice s.b v := by
  unfold finalSweep
  suffices h : ∀ (xs : List (Fin n)) (t : SteeredState n m),
      Matrix.memLattice
        (xs.foldl (fun st k => (st.refreshRow k.val).sizeReduce k.val) t).b v ↔
        Matrix.memLattice t.b v by
    exact h (List.finRange n) s
  intro xs
  induction xs with
  | nil => intro t; simp
  | cons k ks ih =>
    intro t
    simp only [List.foldl_cons]
    rw [ih, sizeReduce_memLattice_iff, refreshRow_b]

end SteeredState

/-- Running the steered loop and final sweep from any initial state preserves the
lattice: both `loop` and `finalSweep` are lattice-preserving, so the output spans
the same integer lattice as `s0.b`, independent of the float approximation. -/
@[grind =] theorem steeredReduceFrom_memLattice_iff
    (s0 : SteeredState n m) (δ : Rat) (v : Vector Int m) :
    Matrix.memLattice (steeredReduceFrom s0 δ) v ↔ Matrix.memLattice s0.b v := by
  unfold steeredReduceFrom; grind

/-- The complete steered reducer preserves the lattice: `init`, `loop`, and
`finalSweep` are each lattice-preserving, so the steered output basis spans the
same integer lattice as the input `b` and membership of `v` is unchanged. This is
the soundness guarantee that holds by construction, with no dependence on the float
approximation. -/
@[grind =] theorem steeredReduce_memLattice_iff
    (b : Matrix Int n m) (δ : Rat) (v : Vector Int m) :
    Matrix.memLattice (steeredReduce b δ) v ↔ Matrix.memLattice b v := by
  unfold steeredReduce; grind


/-- Outcome of one steered reduction: the steered candidate certified at
`(δ, 11/20)`; the run attempted steering but the candidate failed certification,
so it fell back to the exact `lllNative`; or the conditioning test predicted the
float GSO was degenerate and the run skipped straight to `lllNative` without
attempting (and wasting) a steered reduction. -/
inductive SteeredOutcome where
  | certified
  | fellBack
  | skipped
deriving Repr, BEq

/-- Fallback-rate diagnostic for the steered reducer. `fellBack = 0` across a
bench ladder confirms the steered path certified every rung it attempted, so the
measured medians are honest (no exact-reducer time mixed in). `skipped` counts the
rungs the conditioning test routed straight to the exact reducer without a wasted
steered attempt; on the ill-conditioned structured families these previously
showed up as `fellBack`. -/
structure SteeredTally where
  certified : Nat := 0
  fellBack : Nat := 0
  skipped : Nat := 0
deriving Repr, BEq, Inhabited

initialize steeredTallyRef : IO.Ref SteeredTally ← IO.mkRef {}

/-- Reset the steered-reducer tally to zero. Bench harnesses call this before a
run so `steeredTally` reports only the certification/fallback behavior of that
run. -/
@[expose]
def resetSteeredTally : IO Unit := steeredTallyRef.set {}

/-- Read the steered-reducer tally accumulated since the last
`resetSteeredTally`. The two counters show how often the approximation-steered
candidate certified immediately versus falling back to the exact reducer. -/
@[expose]
def steeredTally : IO SteeredTally := steeredTallyRef.get

private def bumpSteered (t : SteeredTally) : SteeredOutcome → SteeredTally
  | .certified => { t with certified := t.certified + 1 }
  | .fellBack => { t with fellBack := t.fellBack + 1 }
  | .skipped => { t with skipped := t.skipped + 1 }

/-- Side-effecting tally bump callable from pure code; definitionally the
continuation `k`. Mirrors `withRecordCheckerOutcome`. -/
unsafe def withRecordSteeredOutcomeImpl {α : Type} (o : SteeredOutcome) (k : α) : α :=
  unsafeBaseIO do
    steeredTallyRef.modify (fun t => bumpSteered t o)
    pure k

/-- Pure-facing wrapper that records one steered-reducer outcome in compiled
code and otherwise returns `k`. This lets `lllSteered` keep a pure type while
benchmarks can still observe certification and fallback rates. -/
@[expose, implemented_by withRecordSteeredOutcomeImpl]
def withRecordSteeredOutcome {α : Type} (_o : SteeredOutcome) (k : α) : α := k

/-- Dimension floor of the steering dispatch, calibrated on the committed
benchmark families. Steering plus post-hoc certification carries a fixed
overhead, so below this dimension the exact `lllNative` is cheaper and runs
directly; at or above it the steered loop's float Gram-Schmidt repays that
overhead against the exact reducer's repeated wide-integer Gram-Schmidt. The
lowest committed rung is 30 and bz-recombination is n=3, so this floor keeps the
smallest inputs — including the µs-scale bz-recombination production family — on
the exact path with no regression. Routing only affects performance, never
output: `lllSteered` certifies every steered candidate and falls back to the
exact reducer if it does not certify. -/
@[expose]
def steerDimThreshold : Nat := 30

/-- Size predictor for the steering dispatch: `true` when the steered reducer plus
certification is predicted to beat the exact `lllNative` on this input. A single
dimension floor places both committed families once the steered reducer certifies
robustly at n=30 (issue #6806): the measured crossover for both the wide-operand
harsh-cubic family and the narrow-operand random-bounded family sits at n=30, so
no operand-width branch is needed. A deterministic function of the input
dimension alone.

Earlier the random-bounded crossover looked like it sat above 40 because the
steered output at n=30 failed certification (a float-drift swap miss) and fell
back to the exact reducer, so steering it regressed; that pushed the dispatch to
a narrow `steerDimThreshold = 40` arm and a separate wide `= 30` arm gated on
`maxDiagBits`. Fixing the drift (the `(δ + 3)/4` steering margin in
`steeredReduce`) makes random-bounded n=30 certify, dropping its measured
crossover to 30 and collapsing the two arms into one. The collapse newly steers
narrow-operand inputs at `30 ≤ n < 40`; this is calibrated for the committed
families, and certification with exact-reducer fallback keeps it correct on any
other input.

Realized routing on the committed ladders: harsh-cubic exact at n ≤ 25, steered
at n ≥ 30; random-bounded steered at n ≥ 30 (n=30 included); bz-recombination
(n=3) exact. -/
@[expose]
def steerWins (_b : Matrix Int n m) : Bool :=
  decide (n ≥ steerDimThreshold)

end Internal

/-- Approximation-steered native reducer with certified output. When `steerWins`
holds it builds the float Gram-Schmidt with `init` and consults its conditioning:
if the approximation is numerically usable (`wellConditioned`) it runs the steered
loop from that state (exact integer row operations driven by the untrusted float
Gram-Schmidt), certifies the candidate at the public `(δ, 11/20)` bound via
`lllReducedCheck`, and falls back to the exact `lllNative` on certification
failure. If the float GSO is degenerate (a non-positive approximate squared norm,
the signature of the structured worst-case families) it skips the predicted-futile
steered attempt and runs `lllNative` directly; below the dimension floor it also runs
`lllNative` directly. The output is therefore always a `(δ, 11/20)`-reduced basis
of the same lattice as `b`; the exact `d`/`ν` state is materialized only on the
small-input, skip, and fallback paths. -/
@[expose]
def lllSteered (b : Matrix Int n m) (δ : Rat)
    (hδ : (1 : Rat) / 4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) : Matrix Int n m :=
  if steerWins b then
    let s0 := SteeredState.init b
    if s0.wellConditioned then
      let candidate := steeredReduceFrom s0 δ
      if lllReducedCheck candidate δ (11 / 20) then
        withRecordSteeredOutcome .certified candidate
      else
        withRecordSteeredOutcome .fellBack (lllNative b δ hδ hδ' hn)
    else
      withRecordSteeredOutcome .skipped (lllNative b δ hδ hδ' hn)
  else
    lllNative b δ hδ hδ' hn

end Hex
