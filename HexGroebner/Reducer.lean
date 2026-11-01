/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Polynomial
public import HexGroebner.NativeTrie

public section

/-! Divisibility-trie reducer lookup. Edges store an exponent and child index
as two unsigned 32-bit scalars. Lookup explores only exponents bounded by the
queried monomial; leaf choice prefers sparse rows, then higher-degree reducers. -/

namespace Hex.Groebner
open Computation

/-- A basis polynomial together with its propagated sugar degree. -/
structure BasisElement where
  polynomial : Polynomial
  sugar : Nat
  deriving Inhabited

/-- A node of a divisibility trie. Edges are insertion ordered, not hash slots. -/
structure DivisorNode where
  edges : ByteArray := {}
  reducer : Option Nat := none
  /-- Path length from the root, so traversal stacks store only node IDs. -/
  depth : Nat := 0
  deriving Inhabited

/-- Leading-monomial index for one immutable basis version. `build` establishes
that every edge points to a distinct child whose depth is its parent depth plus
one; leaves have depth `context.variables`, and the root has depth zero. Lookup
requires this invariant, valid basis references and the associated monomial arena. -/
structure ReducerIndex where
  nodes : Array DivisorNode := #[{}]
  /-- Validated packed encoding for this immutable basis/index version. -/
  packed : Option Native.Trie.View := none

namespace ReducerIndex

/-- Encode small tries once, with charged validation and packed payload. Larger
indices and insufficient preparation allowances retain the ordinary traversal. -/
private def encode (context : Context) (limits : Limits) (nodes : Array DivisorNode)
    (basis : Array BasisElement) : Computation (Option Native.Trie.View) := do
  if context.variables > 4096 || nodes.isEmpty || nodes.size > 2048 then return none
  let edges := nodes.foldl (fun n node => n+node.edges.size/8) 0
  if edges+1 != nodes.size then return none
  let bytes := nodes.size*24+edges*8
  let charge := 16*(nodes.size+edges+1)
  let state ← get
  if state.statistics.work+charge > limits.work ||
      state.statistics.allocatedBytes+state.table.bytes+bytes > limits.packedBytes then return none
  spend limits charge
  allocate limits bytes
  let mut data := ByteArray.emptyWithCapacity (nodes.size*24)
  let mut links := ByteArray.emptyWithCapacity (edges*8)
  let mut maximum : UInt64 := 0
  for node in nodes do
    let mut key := 0
    let mut terms := 0
    let mut leading := 0
    if let some reducer := node.reducer then
      if reducer ≥ basis.size || reducer ≥ 4294967295 then return none
      let polynomial := basis[reducer]!.polynomial
      terms := polynomial.size
      leading := polynomial.monomial 0
      if terms == 0 || terms > 4294967295 || leading > 4294967295 then return none
      key := reducer+1
      maximum := max maximum leading.toUInt64
    for value in #[node.depth,links.size/8,node.edges.size/8,key,terms,leading] do
      if value > 4294967295 then return none
      data := Packed.push .u32 data value.toUInt64
    links := links++node.edges
  return Native.Trie.View.check context.variables data links maximum

/-- Build the index once for a symbolic-preprocessing pass. Duplicate leading
monomials retain the sparsest representative, with deterministic tie breaking. -/
def build (context : Context) (limits : Limits) (basis : Array BasisElement) :
    Computation ReducerIndex := do
  let table := (← get).table
  let mut nodes : Array DivisorNode := #[{}]
  for reducer in [:basis.size] do
    let p := basis[reducer]!.polynomial
    if p.size == 0 then continue
    let leading := p.monomial 0
    let mut node := 0
    for coordinate in [:context.variables] do
      let exponent := table.exponent leading coordinate
      let edges := nodes[node]!.edges
      spend limits (edges.size / 8 + 1)
      let mut child : Option Nat := none
      for i in [:edges.size / 8] do
        if Packed.read .u32 edges (2 * i) == exponent then
          child := some (Packed.read .u32 edges (2 * i + 1)).toNat
          break
      match child with
      | some id => node := id
      | none =>
        allocate limits 8
        let id := nodes.size
        if id > 4294967295 then throw (.representation .index)
        let edges := Packed.push .u32 (Packed.push .u32 edges exponent) id.toUInt64
        nodes := nodes.modify node fun n => { n with edges }
        nodes := nodes.push { depth := coordinate + 1 }
        node := id
    spend limits 1
    let old := nodes[node]!.reducer
    if old.isNone || p.size < basis[old.getD reducer]!.polynomial.size then
      nodes := nodes.modify node fun n => { n with reducer := some reducer }
  return { nodes, packed := ← encode context limits nodes basis }

/-- Exact divisibility lookup. Masks/degrees reject candidates; they never
replace the exponent tests performed by the trie path. -/
-- For a fixed immutable basis/index, selection depends only on the monomial.
-- Shared and separate symbolic closures rely on this deterministic choice.
def findPortable (context : Context) (index : ReducerIndex)
    (basis : Array BasisElement) (table : MonomialTable) (monomial initialWork maxWork : Nat) :
    Except ComputeError (Option Nat) × Nat := Id.run do
  let mut work := initialWork
  let mut pending := #[0]
  let mut result : Option Nat := none
  -- Each trie node has one parent, so at most nodes.size nodes can be visited.
  for _ in [:index.nodes.size] do
    if pending.isEmpty then break
    let node := pending.back!
    pending := pending.pop
    if work + 1 > maxWork then return (.error (.exhausted .work), work)
    work := work + 1
    let n := index.nodes[node]!
    let coordinate := n.depth
    if coordinate == context.variables then
      if let some candidate := n.reducer then
        let p := basis[candidate]!.polynomial
        let leading := p.monomial 0
        if table.degree leading ≤ table.degree monomial &&
            table.mask leading &&& table.mask monomial == table.mask leading then
          if let some old := result then
            let q := basis[old]!.polynomial
            if p.size < q.size || (p.size == q.size && table.degree leading > table.degree (q.monomial 0)) then
              result := some candidate
          else result := some candidate
    else
      let exponent := table.exponent monomial coordinate
      let charge := n.edges.size / 8
      if work + charge > maxWork then return (.error (.exhausted .work), work)
      work := work + charge
      for i in [:n.edges.size / 8] do
        if Packed.read .u32 n.edges (2 * i) ≤ exponent then
          pending := pending.push (Packed.read .u32 n.edges (2 * i + 1)).toNat
  return (.ok result, work)

/-- Perform the read-only trie traversal with local work accounting, then
commit its exact charged prefix once. This preserves exhausted-call statistics
without rebuilding the workspace and statistics at every visited node/edge. -/
def find (context : Context) (limits : Limits) (index : ReducerIndex)
    (basis : Array BasisElement) (monomial : Nat) : Computation (Option Nat) :=
  ExceptT.mk fun state =>
    let native : Native.Trie.Result := if let some view := index.packed then
      if state.table.count ≤ 4294967295 && monomial ≤ 4294967295 then
        Native.Trie.lookup view state.table.width.bytes.toUInt8 state.table.count.toUInt64 monomial.toUInt64
          state.table.exponents state.table.metadata
          (min (limits.work-state.statistics.work) 4096).toUInt64
      else { status := 3 }
      else { status := 3 }
    let (result, work) := if native.status == (3 : UInt8) then
      findPortable context index basis state.table monomial state.statistics.work limits.work
      else (if native.status == (2 : UInt8) then .error (.exhausted .work) else .ok native.reducer,
        state.statistics.work+native.work)
    (result, { state with statistics.work := work })

/-- Enumerate indexed divisors rather than scanning the entire basis. The trie
stores one representative per distinct leading monomial; F4 basis leading
monomials are distinct. Every returned identifier passes the exact path tests. -/
def divisors (context : Context) (limits : Limits) (index : ReducerIndex)
    (monomial : Nat) : Computation (Array Nat) := do
  let table := (← get).table
  let mut pending := #[0]
  let mut result := #[]
  for _ in [:index.nodes.size] do
    if pending.isEmpty then break
    let node := pending.back!
    pending := pending.pop
    spend limits 1
    let n := index.nodes[node]!
    let coordinate := n.depth
    if coordinate == context.variables then
      if let some reducer := n.reducer then result := result.push reducer
    else
      let exponent := table.exponent monomial coordinate
      spend limits (n.edges.size / 8)
      for i in [:n.edges.size / 8] do
        if Packed.read .u32 n.edges (2 * i) ≤ exponent then
          pending := pending.push (Packed.read .u32 n.edges (2 * i + 1)).toNat
  return result

end ReducerIndex
end Hex.Groebner
