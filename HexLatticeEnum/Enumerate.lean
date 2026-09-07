/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Bounds
public import HexLatticeEnum.GramSchmidt

@[expose] public section

namespace Hex.LatticeEnum

/-- Independent deterministic limits. An absent limit is unlimited. -/
structure Budget where
  /-- Maximum visited search nodes across all passes. -/
  nodes : Option Nat := none
  /-- Maximum retained enumeration answers; the incumbent is fixed control state. -/
  answers : Option Nat := none
  /-- Maximum allocated nodes in the exhaustive certificate. -/
  certificateNodes : Option Nat := none
  deriving Repr

/-- Resource counts maintained by the traversal. -/
structure Counts where
  /-- Number of visited nodes. -/
  nodes : Nat := 0
  /-- Number of retained enumeration leaves. -/
  answers : Nat := 0
  /-- Number of allocated certificate nodes. -/
  certificateNodes : Nat := 0
  deriving DecidableEq, Repr

/-- An exhaustive fixed-radius coefficient tree. -/
inductive Tree where
  /-- A branch whose recomputed exact bound is empty. -/
  | empty
  /-- A complete coefficient vector inside the ball. -/
  | leaf
  /-- Every coefficient in the stored interval, with its exhaustive subtree. -/
  | node (interval : Interval) (children : List (Int × Tree))
  deriving Repr, Inhabited

/-- A pending suffix and, for siblings, the unconsumed coefficient streams. -/
structure Work (n : Nat) where
  /-- Number of coefficients still to choose. -/
  remaining : Nat
  /-- Chosen suffix in a full coefficient buffer. -/
  coefficients : Vector Int n
  /-- Accumulated squared cost of the suffix. -/
  cost : Rat
  /-- Remaining siblings at this level, if the first child has been visited. -/
  siblings : Option Coefficients := none
  deriving Repr

/-- Search purpose determines whether to collect leaves or improve an incumbent. -/
inductive SearchMode where
  | ball | closest | shortest
  deriving DecidableEq, Repr

/-- State shared by fixed-radius and branch-and-bound traversal. -/
structure SearchState (n m : Nat) where
  /-- Current exact radius, decreased only by a better incumbent. -/
  radius : Rat
  /-- Retained leaves in reverse traversal order. -/
  points : List (Point n m) := []
  /-- Best directly reconstructed point, when available. -/
  incumbent : Option (Point n m) := none
  /-- Resource consumption. -/
  counts : Counts := {}

/-- Completed traversal or a checked prefix with explicitly pending work. -/
structure Traversal (n m : Nat) where
  /-- Accumulated checked points and resource counts. -/
  state : SearchState n m
  /-- Exhaustive tree, present only after a completed fixed-radius traversal. -/
  tree : Option Tree
  /-- Unvisited suffixes and sibling streams, innermost first. -/
  pending : List (Work n) := []

/-- Whether another resource unit fits under an optional limit. -/
def room (limit : Option Nat) (used : Nat) : Bool :=
  match limit with
  | none => true
  | some cap => used < cap

/-- Fincke–Pohst traversal with exact finite intervals and lazy coefficient order.
The outer recursion decreases dimension; the inner recursion decreases the
exact number of children. Budget checks occur before resource allocation. -/
def traverseAux (b : Basis n m) (t : Vector Rat m) (p : Prepared b t)
    (budget : Budget) (mode : SearchMode) (residualSq : Rat) :
    (k : Nat) → k ≤ n → Vector Int n → Rat → SearchState n m → Traversal n m
  | k, hk, z, suffix, state => Id.run do
    let saveTree := mode == .ball
    let work : Work n := ⟨k, z, suffix, none⟩
    if !room budget.nodes state.counts.nodes ||
        (saveTree && !room budget.certificateNodes state.counts.certificateNodes) then
      return ⟨state, none, [work]⟩
    let counts := { state.counts with
      nodes := state.counts.nodes + 1
      certificateNodes := state.counts.certificateNodes + (if saveTree then 1 else 0) }
    let state := { state with counts }
    match hdim : k with
    | 0 =>
      let candidate := point b t z
      if candidate.distanceSq > state.radius then
        return ⟨state, if saveTree then some .empty else none, []⟩
      if saveTree then
        if !room budget.answers state.counts.answers then
          return ⟨state, none, [work]⟩
        return ⟨{ state with
          points := candidate :: state.points
          counts := { state.counts with answers := state.counts.answers + 1 } },
          some .leaf, []⟩
      else
        let eligible := mode == .closest || candidate.ambient != 0
        if eligible && candidate.distanceSq < state.radius then
          return ⟨{ state with
            radius := candidate.distanceSq
            incumbent := some candidate }, none, []⟩
        return ⟨state, none, []⟩
    | k + 1 =>
      let i : Fin n := ⟨k, by omega⟩
      let centre := p.centre z i
      let interval := bounds centre p.norms[i] (state.radius - residualSq - suffix)
      if interval.size == 0 then
        return ⟨state, if saveTree then some .empty else none, []⟩
      let visitChild := fun (a : Int) (s : SearchState n m) =>
        let z' := z.set k a (by omega)
        let delta := (a : Rat) - centre
        traverseAux b t p budget mode residualSq k (by omega) z'
          (suffix + p.norms[i] * delta * delta) s
      let rec children (fuel : Nat) (cursor : Coefficients)
          (s : SearchState n m) (trees : List (Int × Tree)) : Traversal n m :=
        match fuel with
        | 0 => ⟨s, if saveTree then some (.node interval trees.reverse) else none, []⟩
        | fuel + 1 => match cursor.next? with
          | none => ⟨s, if saveTree then some (.node interval trees.reverse) else none, []⟩
          | some (a, cursor') =>
            let child := visitChild a s
            if child.pending.isEmpty then
              children fuel cursor' child.state
                (if saveTree then (a, child.tree.getD .empty) :: trees else trees)
            else
              let siblings := if fuel == 0 then [] else
                [⟨k + 1, z, suffix, some cursor'⟩]
              ⟨child.state, none, child.pending ++ siblings⟩
      return children interval.size (coefficients interval centre) state []
termination_by k _ _ _ _ => k

/-- Traverse with the constant orthogonal residual norm computed once for the entire pass. -/
def traverse (b : Basis n m) (t : Vector Rat m) (p : Prepared b t)
    (budget : Budget) (mode : SearchMode) (k : Nat) (hk : k ≤ n)
    (z : Vector Int n) (suffix : Rat) (state : SearchState n m) : Traversal n m :=
  traverseAux b t p budget mode p.residual.normSq k hk z suffix state

/-- Public fixed-radius result, distinguishing exhaustion from partial progress. -/
inductive Enumeration (n m : Nat) where
  /-- All points in the ball and a complete coefficient tree. -/
  | complete (points : List (Point n m)) (tree : Tree) (counts : Counts)
  /-- Checked points and enough state to describe every remaining branch. -/
  | incomplete (points : List (Point n m)) (pending : List (Work n)) (counts : Counts)
  deriving Repr

/-- Enumerate a closed ball under independent resource limits. -/
def enumerateWith (budget : Budget) (b : Basis n m) (t : Vector Rat m)
    (radiusSq : Rat) : Enumeration n m :=
  let p := prepare b t
  let result := traverse b t p budget .ball n (Nat.le_refl n) 0 0 { radius := radiusSq }
  match result.tree with
  | some tree => .complete (sortPoints result.state.points) tree result.state.counts
  | none => .incomplete (sortPoints result.state.points) result.pending result.state.counts

/-- All points in the closed ball, in lexicographic ambient-coordinate order. -/
def enumerate (b : Basis n m) (t : Vector Rat m) (radiusSq : Rat) : List (Point n m) :=
  let p := prepare b t
  sortPoints (traverse b t p {} .ball n (Nat.le_refl n) 0 0 { radius := radiusSq }).state.points

end Hex.LatticeEnum
