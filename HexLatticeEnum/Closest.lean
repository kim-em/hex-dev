/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Enumerate

@[expose] public section

namespace Hex.LatticeEnum

variable {n m : Nat} {b : Basis n m} {t : Vector Rat m}

/-- Babai nearest-plane coefficients, rounding centres from the last row down. -/
def nearestPlane (p : Prepared b t) : (k : Nat) → k ≤ n → Vector Int n → Vector Int n
  | 0, _, z => z
  | k + 1, hk, z =>
    let i : Fin n := ⟨k, by omega⟩
    nearestPlane p k (by omega) (z.set k (nearest (p.centre z i)) (by omega))

/-- A directly checked nearest-plane candidate, with no optimality assertion. -/
def babai (b : Basis n m) (t : Vector Rat m) : Point n m :=
  point b t (nearestPlane (prepare b t) n (Nat.le_refl n) 0)

/-- All minimizers and their common exact squared distance. -/
structure Minimum (n m : Nat) where
  /-- Complete list of minimizers in ambient lexicographic order. -/
  points : List (Point n m)
  /-- Common squared distance (squared norm for shortest-vector queries). -/
  distanceSq : Rat
  deriving DecidableEq, Repr

/-- The phase in which an optimization query exhausted its resources. -/
inductive SearchPhase where
  | optimum | ties
  deriving DecidableEq, Repr

/-- Completed optimization or explicitly incomplete progress. -/
inductive Optimization (n m : Nat) where
  /-- All minimizers and an exhaustive ball tree at the attained radius. -/
  | complete (minimum : Minimum n m) (tree : Tree) (counts : Counts)
  /-- A checked incumbent and partial leaves, without a global optimality claim. -/
  | incomplete (incumbent : Point n m) (points : List (Point n m))
      (pending : List (Work n)) (phase : SearchPhase) (counts : Counts)
  deriving Repr

/-- Shared two-pass optimization state. -/
structure OptimumRun (n m : Nat) where
  /-- Best directly reconstructed point. -/
  incumbent : Point n m
  /-- Latest traversal, with counts accumulated across passes. -/
  traversal : Traversal n m
  /-- Current pass. -/
  phase : SearchPhase

/-- Branch-and-bound followed by fixed-radius enumeration of every tie.
The initial candidate bounds the finite search even for a poor basis. -/
def optimize (budget : Budget) (b : Basis n m) (t : Vector Rat m)
    (p : Prepared b t) (mode : SearchMode) (seed : Point n m) : OptimumRun n m :=
  let first := traverse b t p budget mode n (Nat.le_refl n) 0 0
    { radius := seed.distanceSq, incumbent := some seed }
  let incumbent := first.state.incumbent.getD seed
  if !first.pending.isEmpty then ⟨incumbent, first, .optimum⟩ else
    let ties := traverse b t p budget .ball n (Nat.le_refl n) 0 0
      { radius := incumbent.distanceSq, incumbent := some incumbent, counts := first.state.counts }
    ⟨incumbent, ties, .ties⟩

/-- Retain nonzero leaves only for shortest-vector output. -/
def minimumPoints (mode : SearchMode) (ps : List (Point n m)) : List (Point n m) :=
  sortPoints (ps.filter fun p => mode != .shortest || p.ambient != 0)

/-- Classify optimization using actual exhaustion of the fixed-radius pass. -/
def OptimumRun.result (run : OptimumRun n m) (mode : SearchMode) : Optimization n m :=
  let ps := minimumPoints mode run.traversal.state.points
  match run.phase, run.traversal.tree with
  | .ties, some tree =>
    .complete ⟨ps, run.incumbent.distanceSq⟩ tree run.traversal.state.counts
  | _, _ => .incomplete run.incumbent ps run.traversal.pending run.phase run.traversal.state.counts

/-- Closest-vector search with separately counted node, answer and certificate limits. -/
def closestWith (budget : Budget) (b : Basis n m) (t : Vector Rat m) : Optimization n m :=
  let p := prepare b t
  let seed := point b t (nearestPlane p n (Nat.le_refl n) 0)
  (optimize budget b t p .closest seed).result .closest

/-- All closest vectors, including every boundary tie and rank-zero inputs. -/
def closest (b : Basis n m) (t : Vector Rat m) : Minimum n m :=
  let p := prepare b t
  let seed := point b t (nearestPlane p n (Nat.le_refl n) 0)
  let run := optimize {} b t p .closest seed
  ⟨minimumPoints .closest run.traversal.state.points, run.incumbent.distanceSq⟩

end Hex.LatticeEnum
