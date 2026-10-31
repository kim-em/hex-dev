/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.Matrix

public section

namespace Hex.Groebner.Producer

structure Checkpoint where
  basis : Array Element := #[]
  queue : PairQueue := {}
  phase : F4.Phase := .input

def degree (limits : Limits) (p : Polynomial) : Work Nat := do
  lift (Computation.spend limits p.size)
  let table := (← lift get).table
  let mut total := 0
  for i in [:p.size] do total := max total (table.degree (p.monomial i))
  return total

def unit (limits : Limits) (basis : Array Element) : Work (Option Element) := do
  lift (Computation.spend limits basis.size)
  let table := (← lift get).table
  return basis.find? fun g => g.value.polynomial.size != 0 &&
    table.degree (g.value.polynomial.monomial 0) == 0

def install (context : Context) (limits : Limits) (basis : Array Element)
    (queue : PairQueue) (start : Nat) : Work PairQueue := do
  if basis.size > limits.basis then throw (.exhausted .basis)
  lift (Computation.spend limits basis.size)
  let values := plain basis
  let mut queue := queue
  for i in [start:basis.size] do queue ← lift (queue.install context limits values i)
  return queue

def initial (context : Context) (limits : Limits) (nodeLimit : Nat)
    (raw : Array RawPolynomial) : Work Checkpoint := do
  lift (Computation.spend limits raw.size)
  let mut inputs : Array Element := #[]
  for i in [:raw.size] do
    let p ← lift (Polynomial.normalize context limits i raw[i]!)
    let sugar ← degree limits p
    if p.size != 0 then
      let root ← emit limits nodeLimit (.generator i)
      inputs := inputs.push ⟨⟨p,sugar⟩,root⟩
  let matrix ← lift (SymbolicMatrix.prepare context limits #[] (plain inputs))
  let basis ← solve context limits nodeLimit #[] inputs matrix true false
  if let some g ← unit limits basis then
    if limits.basis == 0 then throw (.exhausted .basis)
    return { basis := #[g],phase := .complete }
  let queue ← install context limits basis {} 0
  return { basis,queue,phase := .pairs }

def round (context : Context) (limits : Limits) (nodeLimit : Nat)
    (checkpoint : Checkpoint) : Work Checkpoint := do
  if checkpoint.queue.heap.isEmpty then return { checkpoint with phase := .interreduce }
  let workspace ← lift get
  if workspace.statistics.rounds ≥ limits.rounds then throw (.exhausted .rounds)
  lift (modify fun s => { s with statistics.rounds := s.statistics.rounds+1 })
  lift (Computation.spend limits checkpoint.basis.size)
  let values := plain checkpoint.basis
  let index ← lift (ReducerIndex.build context limits values)
  let (pairs,queue) ← lift (checkpoint.queue.select context limits index values)
  lift (modify fun s => { s with statistics.largestBatch := max s.statistics.largestBatch pairs.size })
  if pairs.isEmpty then return { checkpoint with queue }
  let mut targets := #[]
  for pair in pairs do
    let p ← sPolynomial context limits nodeLimit checkpoint.basis[pair.left]! checkpoint.basis[pair.right]!
    if p.value.polynomial.size != 0 then targets := targets.push { p with value.sugar := pair.sugar }
  let matrix ← lift (SymbolicMatrix.prepareWith context limits index values (plain targets))
  let new ← solve context limits nodeLimit checkpoint.basis targets matrix true false
  let basis := checkpoint.basis ++ new
  if let some g ← unit limits new then
    if limits.basis == 0 then throw (.exhausted .basis)
    return { basis := #[g],phase := .complete }
  let mut queue := queue
  for pair in pairs do queue ← lift (queue.resolve limits pair.left pair.right)
  queue ← install context limits basis queue checkpoint.basis.size
  return { basis,queue,phase := .pairs }

def interreduce (context : Context) (limits : Limits) (nodeLimit : Nat)
    (basis : Array Element) : Work (Array Element) := do
  let table := (← lift get).table
  let mut minimal := #[]
  for i in [:basis.size] do
    let leading := basis[i]!.value.polynomial.monomial 0
    let mut redundant := false
    for j in [:basis.size] do
      lift (Computation.spend limits (context.variables+1))
      let other := basis[j]!.value.polynomial.monomial 0
      if j != i && table.divides other leading && (other != leading || j < i) then
        redundant := true
        break
    if !redundant then minimal := minimal.push basis[i]!
  let values := plain minimal
  let index ← lift (ReducerIndex.build context limits values)
  let mut inputs : Array Element := #[]
  for g in minimal do
    let p := g.value.polynomial
    let mut tail : Polynomial := {}
    if p.size > 1 then
      lift (Computation.allocate limits ((p.size-1)*(4+context.field.width.bytes)))
      lift (Computation.spend limits p.size)
      tail := { support := p.support.extract 4 p.support.size, coefficients := p.coefficients.extract context.field.width.bytes p.coefficients.size }
    inputs := inputs.push ⟨⟨tail,g.value.sugar⟩,g.root⟩
  let tails ← if limits.batchInterreduce then do
    lift (Computation.spend limits inputs.size)
    let nonzero := inputs.filter fun p => p.value.polynomial.size != 0
    if nonzero.isEmpty then pure inputs else
      let matrix ← lift (SymbolicMatrix.prepareWith context limits index values (plain nonzero))
      let remainders ← solve context limits nodeLimit minimal nonzero matrix false true
      let mut cursor := 0
      let mut output := #[]
      for p in inputs do
        lift (Computation.spend limits 1)
        if p.value.polynomial.size == 0 then output := output.push p else
          output := output.push remainders[cursor]!
          cursor := cursor+1
      pure output
  else inputs.mapM fun tail => do
    if tail.value.polynomial.size == 0 then return tail
    let matrix ← lift (SymbolicMatrix.prepareWith context limits index values #[tail.value])
    let rows ← solve context limits nodeLimit minimal #[tail] matrix false true
    return rows[0]!
  let mut reduced : Array Element := #[]
  for i in [:minimal.size] do
    let g := minimal[i]!
    let p := g.value.polynomial
    let tail := tails[i]!.value.polynomial
    lift (Computation.allocate limits ((tail.size+1)*(4+context.field.width.bytes)))
    lift (Computation.spend limits tail.size)
    let mut support := Packed.push .u32 {} (p.monomial 0).toUInt64
    let mut coefficients := Packed.push context.field.width {} (p.coefficient context.field 0)
    for j in [:tail.size] do
      support := Packed.push .u32 support (tail.monomial j).toUInt64
      coefficients := Packed.push context.field.width coefficients (tail.coefficient context.field j)
    let mut polynomial : Polynomial := { support,coefficients }
    let mut root := tails[i]!.root
    if polynomial.coefficient context.field 0 != 1 then
      let factor ← lift (Computation.inverse context.field limits (polynomial.coefficient context.field 0))
      polynomial ← lift (polynomial.scale context limits factor)
      root ← emit limits nodeLimit (.scale factor.toNat root)
    reduced := reduced.push ⟨⟨polynomial,g.value.sugar⟩,root⟩
  let leading := reduced.map fun g => g.value.polynomial.monomial 0
  let order ← lift (Computation.sort context limits leading)
  lift (Computation.spend limits reduced.size)
  let positions := (reduced.zipIdx).foldl (fun (m : Std.HashMap Nat Nat) (g,i) =>
    m.insert (g.value.polynomial.monomial 0) i) {}
  return order.map fun id => reduced[positions[id]!]!

def step (context : Context) (limits : Limits) (nodeLimit : Nat)
    (raw : Array RawPolynomial) (checkpoint : Checkpoint) : Work Checkpoint := do
  lift (Computation.spend limits 1)
  match checkpoint.phase with
  | .input => initial context limits nodeLimit raw
  | .pairs => round context limits nodeLimit checkpoint
  | .interreduce => return { checkpoint with
      basis := ← interreduce context limits nodeLimit checkpoint.basis,phase := .complete }
  | .complete => return checkpoint

end Hex.Groebner.Producer
