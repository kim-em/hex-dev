/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Reducer
public import Std.Data.TreeSet

public section

/-! Critical pairs in a persistent leftist sugar-degree heap. Pair resolution is explicit:
the chain criterion only cites pairs already resolved, never queued pairs. -/

namespace Hex.Groebner
open Computation

/-- A critical pair, with stable basis indices, its actual LCM and sugar degree. -/
structure CriticalPair where
  left : Nat
  right : Nat
  lcm : Nat
  sugar : Nat
  deriving Inhabited

/-- Persistent leftist heap. Cached rank bounds the right spine; cached count
makes queue bounds constant-time. Checkpoints share untouched subtrees. -/
inductive PairHeap where
  | empty
  | node (rank count : Nat) (pair : CriticalPair) (left right : PairHeap)
  deriving Inhabited

namespace PairHeap

/-- Outstanding pair count, cached at each node. -/
def size : PairHeap → Nat
  | .empty => 0
  | .node _ count _ _ _ => count

/-- Whether no critical pair remains. -/
def isEmpty : PairHeap → Bool
  | .empty => true
  | .node .. => false

/-- Least pair, when present. -/
def first? : PairHeap → Option CriticalPair
  | .empty => none
  | .node _ _ pair _ _ => some pair

private def rank : PairHeap → Nat
  | .empty => 0
  | .node rank _ _ _ _ => rank

private def branch (pair : CriticalPair) (a b : PairHeap) : PairHeap :=
  let count := a.size + b.size + 1
  if rank a ≥ rank b then .node (rank b + 1) count pair a b
  else .node (rank a + 1) count pair b a

private def before (a b : CriticalPair) : Bool :=
  a.sugar < b.sugar || (a.sugar == b.sugar &&
    (a.left < b.left || (a.left == b.left && a.right < b.right)))

/-- Meld visits only the right spines. It preserves sharing with saved
checkpoints instead of copying the outstanding pair array. -/
def meld (a b : PairHeap) : PairHeap :=
  match a, b with
  | .empty, b => b
  | a, .empty => a
  | .node ra ca x left right, .node rb cb y left' right' =>
    if before x y then branch x left (meld right (.node rb cb y left' right'))
    else branch y left' (meld (.node ra ca x left right) right')
termination_by sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

end PairHeap

/-- Sugar-ordered queue plus resolved-pair obligations. -/
structure PairQueue where
  heap : PairHeap := .empty
  resolved : Std.TreeSet (Nat × Nat)
    (fun a b => (compare a.1 b.1).then (compare a.2 b.2)) := {}

namespace PairQueue

/-- Canonical unordered pair key. -/
def key (i j : Nat) : Nat × Nat := (min i j, max i j)

/-- Record a resolved obligation in a persistent balanced tree. Its logarithmic
comparison bound is charged even when insertion finds an existing key. -/
def resolve (limits : Limits) (queue : PairQueue) (i j : Nat) : Computation PairQueue := do
  spend limits (4 * (queue.resolved.size + 2).log2)
  return { queue with resolved := queue.resolved.insert (key i j) }

/-- Persistent heap insertion is logarithmic in the outstanding pair count. -/
def push (limits : Limits) (queue : PairQueue) (pair : CriticalPair) : Computation PairQueue := do
  spend limits (queue.heap.size.log2 + 2)
  return { queue with heap := queue.heap.meld (.node 1 1 pair .empty .empty) }

/-- Remove the least sugar pair, sharing all untouched checkpoint subtrees. -/
def pop (limits : Limits) (queue : PairQueue) : Computation (Option CriticalPair × PairQueue) := do
  match queue.heap with
  | .empty => return (none, queue)
  | .node _ count pair left right =>
    spend limits (2 * (count.log2 + 2))
    return (some pair, { queue with heap := left.meld right })

private def coprime (table : MonomialTable) (a b : Nat) : Bool := Id.run do
  if table.mask a &&& table.mask b == 0 then return true
  for i in [:table.arity] do
    if table.exponent a i != 0 && table.exponent b i != 0 then return false
  return true

/-- Install every pair involving the new basis element. Product pairs are
resolved immediately; no unresolved pair is removed by a degree heuristic. -/
def install (context : Context) (limits : Limits) (queue : PairQueue)
    (basis : Array BasisElement) (new : Nat) : Computation PairQueue := do
  let mut queue := queue
  for i in [:new] do
    let state ← get
    if state.statistics.pairs ≥ limits.pairs then throw (.exhausted .pairs)
    set { state with statistics.pairs := state.statistics.pairs + 1 }
    spend limits (context.variables + 1)
    let a := basis[i]!.polynomial.monomial 0
    let b := basis[new]!.polynomial.monomial 0
    if coprime (← get).table a b then
      queue ← queue.resolve limits i new
      modify fun s => { s with statistics.productPairs := s.statistics.productPairs + 1 }
    else
      let lcm ← combine limits .lcm a b
      let table := (← get).table
      let sugar := max (basis[i]!.sugar + table.degree lcm - table.degree a)
        (basis[new]!.sugar + table.degree lcm - table.degree b)
      queue ← queue.push limits ⟨i, new, lcm, sugar⟩
  return queue

/-- Buchberger's chain test with explicit resolved dependencies. -/
def chain (context : Context) (limits : Limits) (queue : PairQueue)
    (basis : Array BasisElement) (pair : CriticalPair) : Computation Bool := do
  let table := (← get).table
  for k in [:basis.size] do
    spend limits (context.variables + 1 + 8 * (queue.resolved.size + 2).log2)
    if k != pair.left && k != pair.right &&
        queue.resolved.contains (key pair.left k) && queue.resolved.contains (key k pair.right) &&
        table.divides (basis[k]!.polynomial.monomial 0) pair.lcm then return true
  return false

/-- Select one fair sugar batch; batch size is bounded independently of degree.
Skipped chain pairs become resolved only after the dependency test succeeds. -/
def select (context : Context) (limits : Limits) (queue : PairQueue)
    (basis : Array BasisElement) : Computation (Array CriticalPair × PairQueue) := do
  let mut queue := queue
  let mut selected := #[]
  let mut sugar : Option Nat := none
  let count := queue.heap.size
  for _ in [:count] do
    if queue.heap.isEmpty || selected.size ≥ max 1 limits.batchSize then break
    if let some d := sugar then
      if queue.heap.first?.any (fun pair => pair.sugar != d) then break
    let (pair, next) ← queue.pop limits
    queue := next
    if let some pair := pair then
      if ← queue.chain context limits basis pair then
        queue ← queue.resolve limits pair.left pair.right
        modify fun s => { s with statistics.chainPairs := s.statistics.chainPairs + 1 }
      else
        sugar := some pair.sugar
        selected := selected.push pair
  return (selected, queue)

end PairQueue
end Hex.Groebner
