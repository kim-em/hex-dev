/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Polynomial

public section

namespace Hex.Groebner
open Computation

private structure ReducerProduct where
  base : Polynomial
  product : Polynomial

/-- Multiplied reducers from one append-only monomial arena. F4 retains this
cache in its sealed checkpoint; it must not be reused with another arena.
The context binds field and order; complete base payloads identify each basis
polynomial. Raw callers must retain the associated arena. -/
structure ReducerCache where
  private mk ::
  private context : Option Context
  private rows : Std.HashMap UInt64 ReducerProduct

namespace ReducerCache

/-- An empty cache can be associated with any monomial arena. -/
def empty : ReducerCache := ⟨none, {}⟩

instance : Inhabited ReducerCache := ⟨empty⟩

private def bind (cache : ReducerCache) (context : Context) : ReducerCache :=
  match cache.context with
  | some previous => if decide (previous = context) then cache else ⟨some context, {}⟩
  | none => ⟨some context, {}⟩

private def sameBytes (left right : @& ByteArray) : Bool := Id.run do
  if left.size != right.size then return false
  let mut start := 0
  for _ in [:(left.size+4095)/4096] do
    let count := min 4096 (left.size-start)
    if !Native.Bytes.equal left right start count then return false
    start := start+count
  return true

/-- Multiply a valid nonzero reducer by an arena monomial, reusing an exact
previous product. Stable leading/multiplier IDs fit in one 64-bit key. The
complete base polynomial is checked before a hit, in bounded native slices.

At most 16384 entries are retained. Their eight-byte keys are charged before
insertion; base/product payloads share already charged immutable buffers. Lookup
and comparison work consumes the parent allowance. When key storage would not
fit, the computed product is returned without caching. Object headers and map
capacity follow the same exclusion as the other computation metadata. -/
def multiply (context : Context) (limits : Limits) (cache : ReducerCache)
    (base : Polynomial) (multiplier : Nat) : Computation (Polynomial × ReducerCache) := do
  let cache := cache.bind context
  if (← get).table.degree multiplier == 0 then return (base, cache)
  spend limits 1
  let leading := base.monomial 0
  -- Wider future identifiers must bypass this exact u32-pair cache key.
  if multiplier > 4294967295 || leading > 4294967295 then
    return (← base.multiply context limits multiplier, cache)
  let key := leading.toUInt64 <<< 32 ||| multiplier.toUInt64
  if let some entry := cache.rows[key]? then
    spend limits (base.support.size + base.coefficients.size)
    if sameBytes entry.base.support base.support && sameBytes entry.base.coefficients base.coefficients then
      return (entry.product, cache)
  let product ← base.multiply context limits multiplier
  let state ← get
  if cache.rows.size < 16384 && state.statistics.allocatedBytes + state.table.bytes + 8 ≤ limits.packedBytes then
    allocate limits 8
    return (product, ⟨some context, cache.rows.insert key ⟨base, product⟩⟩)
  return (product, cache)

end ReducerCache
end Hex.Groebner
