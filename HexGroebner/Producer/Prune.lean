/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Producer.Basic

public section

namespace Hex.Groebner.Producer

private def reference (mapping : Array Nat) (source : Nat) : Work Nat := do
  let some encoded := mapping[source]? | throw (.matrix .dimensions)
  if encoded == 0 then throw (.matrix .dimensions)
  return encoded - 1

/-- Keep exactly the shared derivation nodes reachable from the final roots.
The reverse pass checks backward references; the forward pass renumbers them.
All temporary storage and copied node payload consume the parent allowance. -/
def prune (limits : Limits) (nodes : Array Certificate.Node) (roots : Array Nat) :
    Work Certificate.Containment := do
  lift (Computation.spend limits (nodes.size * 16 + roots.size * 8))
  lift (Computation.allocate limits (64 + nodes.size))
  let mut reachable := ByteArray.emptyWithCapacity nodes.size
  for _ in [:nodes.size] do reachable := reachable.push 0
  for root in roots do
    if root ≥ nodes.size then throw (.matrix .dimensions)
    reachable := reachable.set! root 1
  for offset in [:nodes.size] do
    let index := nodes.size - 1 - offset
    if reachable[index]! != 0 then
      match nodes[index]! with
      | .zero | .generator _ => pure ()
      | .scale _ source | .multiply _ source =>
        if source ≥ index then throw (.matrix .dimensions)
        reachable := reachable.set! source 1
      | .add left right =>
        if left ≥ index || right ≥ index then throw (.matrix .dimensions)
        reachable := reachable.set! left 1
        reachable := reachable.set! right 1
  lift (Computation.allocate limits (64 + nodes.size * 8))
  let mut mapping := Array.replicate nodes.size 0
  let mut kept : Array Certificate.Node := #[]
  for index in [:nodes.size] do
    if reachable[index]! != 0 then
      lift (Computation.allocate limits 72)
      let node : Certificate.Node ← match nodes[index]! with
        | .zero => pure Certificate.Node.zero
        | .generator i => pure (.generator i)
        | .scale coefficient source => do
          let renamed ← reference mapping source
          pure (Certificate.Node.scale coefficient renamed)
        | .multiply factor source => do
          let renamed ← reference mapping source
          pure (Certificate.Node.multiply factor renamed)
        | .add left right => do
          let left ← reference mapping left
          let right ← reference mapping right
          pure (Certificate.Node.add left right)
      mapping := mapping.set! index (kept.size + 1)
      kept := kept.push node
  lift (Computation.allocate limits (64 + roots.size * 8))
  let mut renamed := Array.emptyWithCapacity roots.size
  for root in roots do renamed := renamed.push (← reference mapping root)
  lift (Computation.allocate limits (kept.size * 24))
  return ⟨kept.toList, renamed⟩

end Hex.Groebner.Producer
