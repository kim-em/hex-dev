/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Reducer
public import Std.Data.TreeSet

public section

/-! Critical pairs in a persistent leftist degree/sugar heap. Pair resolution is explicit:
the resolved chain criterion cites completed dependencies; Gebauer–Möller
installation and proper-LCM chains retain a separate deferred-obligation contract. -/

namespace Hex.Groebner
open Computation

/-- A critical pair, with stable basis indices, its actual LCM and sugar degree. -/
structure CriticalPair where
  left : Nat
  right : Nat
  lcm : Nat
  sugar : Nat
  /-- Cached scheduling key, distinct from the propagated sugar label. Queue
  installation supplies it explicitly; manually constructed pairs default to sugar. -/
  priority : Nat := sugar
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
  a.priority < b.priority || (a.priority == b.priority &&
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

/-- Priority-ordered queue plus completed pair obligations. Pairs omitted by GM
retain implicit dependencies on retained pairs; they are deliberately absent
from `resolved`. Retirement also leaves future pairs ungenerated. A complete
producer proof must cover queued, completed, installation-omitted and
retirement-omitted pairs. -/
structure PairQueue where
  heap : PairHeap := .empty
  resolved : Std.TreeSet (Nat × Nat)
    (fun a b => (compare a.1 b.1).then (compare a.2 b.2)) := {}
  /-- Stable indices eligible for future pairs. Retired polynomials and existing
  obligations remain in their original basis and queue positions. -/
  active : Array Nat := #[]
  /-- First basis index not yet considered for eligibility. -/
  frontier : Nat := 0

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

/-- Remove the least priority pair, sharing all untouched checkpoint subtrees. -/
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

private def installBuchberger (context : Context) (limits : Limits) (queue : PairQueue)
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
      let priority := match limits.scheduling with
        | .degree => table.degree lcm
        | .sugar => sugar
      queue ← queue.push limits ⟨i, new, lcm, sugar, priority⟩
  return queue

/-- Install minimal new LCMs using the Gebauer–Möller strategy (Becker and
Weispfenning, algorithm UPDATE). Product pairs remain available as divisibility
filters. Equal LCMs prefer a product pair, then the earliest basis index.
Omitted pairs are never marked resolved: their justification can still depend
on retained pairs. Coverage uses LCM, then maximum basis index, then a final
level: zero for a retained representative, one for another equal-LCM group
member, and one plus the prior retirement-chain depth for an ungenerated pair.
At installation of the larger index, active indices have depth zero; a removed
index has depth one plus the depth of its replacement. Replacement along that
chain decreases depth; connecting obligations have smaller maximum index.
Proper-LCM chains decrease the first component, even with retired reducers.
This is a dependency contract for the outstanding producer proof.

This is UPDATE’s removal from its eligible basis set G; the polynomial arena
retains the removed entries for reduction and derivations.

The drivers install indices in increasing order. `active` is ascending and lies
below `frontier`; every earlier index has been installed. A gap before `new`
consists of indices already installed by the Buchberger route. The helper also
allows isolated installations, which alone establish no global pair coverage.
A repeated earlier installation conservatively adds all Buchberger pairs and
retains eligibility metadata; the drivers do not need this fallback.

Proper old-pair pruning is deferred to selection. Retired basis entries remain
available as reducers and derivations; only future new-pair installation omits
them. Installation with the retiring polynomial precedes retirement, retaining
the necessary connecting obligation. -/
def install (context : Context) (limits : Limits) (queue : PairQueue)
    (basis : Array BasisElement) (new : Nat) : Computation PairQueue := do
  if !limits.gebauerMoller then return ← installBuchberger context limits queue basis new
  let mut queue := queue
  if new < queue.frontier then return ← installBuchberger context limits queue basis new
  let mut active := queue.active
  queue := { queue with active := #[] }
  spend limits (new - queue.frontier)
  for i in [queue.frontier:new] do active := active.push i
  let mut retained : Array Nat := #[]
  let mut retired := false
  let mut candidates : Std.HashMap Nat (CriticalPair × Bool) := {}
  let mut lcms : Array Nat := #[]
  for position in [:active.size] do
    let i := active[position]!
    let state ← get
    if state.statistics.pairs ≥ limits.pairs then throw (.exhausted .pairs)
    set { state with statistics.pairs := state.statistics.pairs + 1 }
    spend limits (context.variables + 1)
    let a := basis[i]!.polynomial.monomial 0
    let b := basis[new]!.polynomial.monomial 0
    let lcm ← combine limits .lcm a b
    if lcm == a then
      if !retired then
        spend limits position
        retained := active.extract 0 position
        retired := true
    else if retired then retained := retained.push i
    let table := (← get).table
    let product := coprime table a b
    let sugar := max (basis[i]!.sugar + table.degree lcm - table.degree a)
      (basis[new]!.sugar + table.degree lcm - table.degree b)
    let priority := match limits.scheduling with
      | .degree => table.degree lcm
      | .sugar => sugar
    let pair : CriticalPair := ⟨i, new, lcm, sugar, priority⟩
    if product then
      queue ← queue.resolve limits i new
      modify fun s => { s with statistics.productPairs := s.statistics.productPairs + 1 }
    match candidates[lcm]? with
    | none =>
      lcms := lcms.push lcm
      candidates := candidates.insert lcm (pair, product)
    | some (_, oldProduct) =>
      if !product || !oldProduct then
        modify fun s => { s with statistics.gmPairs := s.statistics.gmPairs + 1 }
      if product && !oldProduct then candidates := candidates.insert lcm (pair, true)
  -- Divisibility implies non-strict mathematical monomial order, so every
  -- proper divisor occurs first. Stable IDs make equal-LCM groups exact.
  let ordered ← sort context limits lcms
  let table := (← get).table
  let mut minimal : Array Nat := #[]
  for lcm in ordered.reverse do
    let mut dominated := false
    for divisor in minimal do
      spend limits (context.variables + 1)
      if table.divides divisor lcm then
        dominated := true
        break
    let (pair, product) := candidates[lcm]!
    if dominated then
      if !product then
        modify fun s => { s with statistics.gmPairs := s.statistics.gmPairs + 1 }
    else
      minimal := minimal.push lcm
      if !product then queue ← queue.push limits pair
  -- Conservatively charge a complete copy, even if retained is already unique.
  spend limits (active.size + 1)
  return { queue with active := (if retired then retained else active).push new, frontier := new + 1 }

/-- A completed chain and a proper-LCM chain have different dependency contracts. -/
inductive PairCriterion where
  | keep | resolved | proper
  deriving BEq, Repr

/-- Indexed chain criteria. A resolved chain cites two completed obligations.
A proper-LCM chain cites two strictly smaller LCMs; it can be omitted by
well-founded induction on the LCM, but must never enter the resolved-pair set. -/
def chain (context : Context) (limits : Limits) (queue : PairQueue)
    (index : ReducerIndex) (basis : Array BasisElement) (pair : CriticalPair) :
    Computation PairCriterion := do
  let table := (← get).table
  let left := basis[pair.left]!.polynomial.monomial 0
  let right := basis[pair.right]!.polynomial.monomial 0
  for k in ← index.divisors context limits pair.lcm do
    if k == pair.left || k == pair.right then continue
    spend limits (1 + 8 * (queue.resolved.size + 2).log2)
    if queue.resolved.contains (key pair.left k) && queue.resolved.contains (key k pair.right) then
      return .resolved
    if !limits.gebauerMoller then continue
    spend limits (2 * context.variables)
    let middle := basis[k]!.polynomial.monomial 0
    let mut properLeft := false
    let mut properRight := false
    for i in [:context.variables] do
      let bound := table.exponent pair.lcm i
      let value := table.exponent middle i
      if max (table.exponent left i) value < bound then properLeft := true
      if max (table.exponent right i) value < bound then properRight := true
    if properLeft && properRight then return .proper
  return .keep

/-- Select one fair priority batch; batch size is bounded independently of degree.
Only completed-dependency chains enter `resolved`. Proper-LCM omissions
remain distinct; both classes are removed atomically with the checkpoint. -/
def select (context : Context) (limits : Limits) (queue : PairQueue)
    (index : ReducerIndex) (basis : Array BasisElement) : Computation (Array CriticalPair × PairQueue) := do
  let mut queue := queue
  let mut selected := #[]
  let mut priority : Option Nat := none
  let count := queue.heap.size
  for _ in [:count] do
    if queue.heap.isEmpty || selected.size ≥ max 1 limits.batchSize then break
    if let some d := priority then
      if queue.heap.first?.any (fun pair => pair.priority != d) then break
    let (pair, next) ← queue.pop limits
    queue := next
    if let some pair := pair then
      match ← queue.chain context limits index basis pair with
      | .resolved =>
        queue ← queue.resolve limits pair.left pair.right
        modify fun s => { s with statistics.chainPairs := s.statistics.chainPairs + 1 }
      | .proper =>
        modify fun s => { s with statistics.gmPairs := s.statistics.gmPairs + 1 }
      | .keep =>
        priority := some pair.priority
        selected := selected.push pair
  return (selected, queue)

end PairQueue
end Hex.Groebner
