/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Pairs
public import HexGroebner.Symbolic

public section

namespace Hex.Groebner
open Computation

/-- Multiplied critical-pair rows, with one known reducer per LCM. Every target
retains its source basis index and quotient for independent derivation recording. -/
structure PairRows where
  reducers : Array SymbolicReducer
  targets : Array SymbolicReducer
  cache : ReducerCache

namespace PairRows

private structure Group where
  basis : Nat
  sugar : Nat

private def prefer (basis : Array BasisElement) (a b : Nat) : Bool :=
  let x := basis[a]!.polynomial.size
  let y := basis[b]!.polynomial.size
  x < y || (x == y && a < b)

private def multiply (context : Context) (limits : Limits) (basis : Array BasisElement)
    (cache : ReducerCache) (source lcm sugar : Nat) :
    Computation (SymbolicReducer × ReducerCache) := do
  let f := basis[source]!.polynomial
  let multiplier ← combine limits .quotient lcm (f.monomial 0)
  let (polynomial, cache) ← cache.multiply context limits f multiplier
  return (⟨source, multiplier, polynomial, sugar⟩, cache)

/-- Form the usual F4 multiplied rows without expanding S-polynomial differences.
For each LCM choose its sparsest source as a known reducer and retain every other
source once. Their differences span all selected S-polynomials modulo these
reducers; disconnected same-LCM components may supply additional valid rows.
Requires a canonical nonzero monic basis and its actual critical-pair LCMs
from the associated arena. Selection is deterministic, and every product belongs
to the original basis ideal. -/
def prepare (context : Context) (limits : Limits) (basis : Array BasisElement)
    (pairs : Array CriticalPair) (cache : ReducerCache) : Computation PairRows := do
  let mut groups : Std.HashMap Nat Group := {}
  let mut order := #[]
  for pair in pairs do
    spend limits 4
    if pair.left ≥ basis.size || pair.right ≥ basis.size then throw (.matrix .dimensions)
    if basis[pair.left]!.polynomial.size == 0 || basis[pair.right]!.polynomial.size == 0 then
      throw (.matrix .dimensions)
    let source := if prefer basis pair.left pair.right then pair.left else pair.right
    if let some old := groups[pair.lcm]? then
      let source := if prefer basis source old.basis then source else old.basis
      groups := groups.insert pair.lcm { old with basis := source, sugar := max old.sugar pair.sugar }
    else
      groups := groups.insert pair.lcm { basis := source, sugar := pair.sugar }
      order := order.push pair.lcm
  let mut cache := cache
  let mut reducers := #[]
  for lcm in order do
    spend limits 1
    let some group := groups[lcm]? | throw (.representation .index)
    let (row, nextCache) ← multiply context limits basis cache group.basis lcm group.sugar
    cache := nextCache
    reducers := reducers.push row
  let mut targets := #[]
  let mut emitted : Std.HashSet (Nat × Nat) := {}
  for pair in pairs do
    for source in [pair.left, pair.right] do
      spend limits 3
      let some group := groups[pair.lcm]? | throw (.representation .index)
      if source == group.basis || emitted.contains (pair.lcm, source) then continue
      emitted := emitted.insert (pair.lcm, source)
      let (row, nextCache) ← multiply context limits basis cache source pair.lcm group.sugar
      cache := nextCache
      targets := targets.push row
  return ⟨reducers, targets, cache⟩

end PairRows
end Hex.Groebner
