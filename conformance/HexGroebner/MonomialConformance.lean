/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Monomial

/-! Exact-collision, stable-identifier, exponent-widening and global-order checks. -/

namespace Hex.Groebner.MonomialConformance

private def campaign : Bool := Id.run do
  let mut t : MonomialTable := { arity := 3, hashBits := 0 }
  let mut ids := #[]
  for k in [:300] do
    match t.intern #[k.toUInt64, (k % 11).toUInt64, 1] 1000 1000000 with
    | .error _ => return false
    | .ok (id, next) =>
      if id != k then return false
      ids := ids.push id
      t := next
  if t.width != .u16 then return false
  for k in [:300] do
    if t.exponentsAt ids[k]! != #[k, k % 11, 1] then return false
    match t.intern #[k.toUInt64, (k % 11).toUInt64, 1] 300 1000000 with
    | .error _ => return false
    | .ok (id, next) =>
      if id != k || next.count != 300 then return false
  match t.intern #[65536, 1, 0] 1000 1000000 with
  | .error _ => return false
  | .ok (id, next) =>
    if next.width != .u32 || id != 300 || next.exponentsAt 299 != #[299, 2, 1] then return false
    t := next
  return t.divides 0 11 && !t.divides 1 0 && !t.divides 300 299

-- Compare on explicitly sized vectors: no proof recovery from raw buffers is
-- needed by clients that already know the fixed arity.
private def orderAgreement : Bool := Id.run do
  let mut t : MonomialTable := { arity := 3 }
  for k in [:100] do
    match t.intern #[(k / 25).toUInt64, (k / 5 % 5).toUInt64, (k % 5).toUInt64] 100 100000 with
    | .error _ => return false
    | .ok (_, next) => t := next
  for order in [TermOrder.lex, .grlex, .grevlex] do
    for i in [:100] do
      for j in [:100] do
        let a : Mono 3 := #v[i / 25, i / 5 % 5, i % 5]
        let b : Mono 3 := #v[j / 25, j / 5 % 5, j % 5]
        if t.compare order i j != order.cmp 3 a b then return false
  return true

-- Exercise every exponent width through the actual table methods, including
-- the portable dispatch beyond the 4096-coordinate native bound.
def orderChecks : Bool := Id.run do
  for n in [3,65,4096,4097] do
    for base in [2,257,65537] do
      let zero := Array.replicate n 0
      let common := Array.replicate n base
      let values := #[zero,common,common.set! 0 (base+1) |>.set! (n-1) (base-1),
        common.set! (n-1) (base+1),zero.set! (n-1) (base+2),
        (common.set! 0 (base+1)).set! 1 (base-1),
        (common.set! (n-2) (base+1)).set! (n-1) (base-1)]
      let mut table : MonomialTable := { arity := n }
      for exponents in values do
        let .ok (_, next) := table.intern (exponents.map Nat.toUInt64) 10 1000000 1000000000
          | return false
        table := next
      if table.width != (if base < 256 then Width.u8 else if base < 65536 then .u16 else .u32) then return false
      for i in [:values.size] do
        for j in [:values.size] do
          let a : Mono n := Vector.ofFn (fun k => values[i]![k.val]!)
          let b : Mono n := Vector.ofFn (fun k => values[j]![k.val]!)
          for order in [TermOrder.lex,.grlex,.grevlex] do
            if table.compare order i j != order.cmp n a b then return false
          let divides := (values[i]!.toList.zip values[j]!.toList).all (fun (x,y) => x ≤ y)
          if table.divides i j != divides then return false
  return true

#guard orderChecks

#guard campaign
#guard orderAgreement

private def bounds : Bool := Id.run do
  let t : MonomialTable := { arity := 2 }
  if (t.intern #[1] 10 1000).isOk then return false
  if (t.intern #[4294967296, 0] 10 1000).isOk then return false
  if (t.intern #[1, 0] 0 1000).isOk then return false
  if (t.intern #[1, 0] 10 1).isOk then return false
  match t.intern #[4294967295, 0] 10 1000 with
  | .error _ => return false
  | .ok (a, t) =>
    match t.intern #[1, 0] 10 1000 with
    | .error _ => return false
    | .ok (b, t) =>
      if (t.combine .product a b 10 1000).isOk then return false
      if (t.combine .quotient b a 10 1000).isOk then return false
      match t.combine .quotient a b 10 1000 with
      | .error _ => return false
      | .ok (id, t) => return t.exponentsAt id == #[4294967294, 0]

#guard bounds

private def same (a b : InternResult) : Bool :=
  (match a.result, b.result with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false) && a.table.count == b.table.count && a.table.width == b.table.width &&
    a.table.exponents.data == b.table.exponents.data && a.table.metadata.data == b.table.metadata.data &&
    a.table.work == b.table.work && a.table.bytes == b.table.bytes

private def packed : Bool := Id.run do
  for arity in [0, 1, 2, 10, 65, 4096, 4097] do
    let mut reference : MonomialTable := { arity, hashBits := 0 }
    for seed in [:5] do
      let values := (Array.range arity).map fun i => ((seed + i * 3) % 17).toUInt64
      let result := reference.internOwned values 200 1000000000 1000000000
      if !result.result.isOk then return false
      reference := result.table
    let mut native := reference
    for seed in [:(if arity > 65 then 10 else 100)] do
      let count := reference.count
      let a := seed % count
      let b := (seed * 7 + 1) % count
      let operation := match seed % 3 with
        | 0 => MonomialTable.Operation.lcm
        | 1 => .product
        | _ => .quotient
      let first := native.combineOwned operation a b 200 1000000000 1000000000 true
      let second := reference.combineOwned operation a b 200 1000000000 1000000000 false
      if !same first second then return false
      native := first.table
      reference := second.table
  for boundary in ([255, 65535, 4294967295] : List UInt64) do
    let .ok (a, t) := ({ arity := 1 } : MonomialTable).intern #[boundary] 10 10000 | return false
    let .ok (b, t) := t.intern #[1] 10 10000 | return false
    let native := t.combineOwned .product a b 10 10000 100000 true
    let portable := t.combineOwned .product a b 10 10000 100000 false
    if !same native portable then return false
  let .ok (a, t) := ({ arity := 2 } : MonomialTable).intern #[1, 0] 10 10000 | return false
  let .ok (b, t) := t.intern #[0, 1] 10 10000 | return false
  let output := t.combineOwned .product a b 10 114
  if !output.result.isOk || output.table.bytes != 114 then return false
  if (t.combineOwned .product a b 10 113).result.isOk then return false
  if (output.table.internOwned #[2, 0] 10 139).result.isOk then return false
  if !(output.table.internOwned #[2, 0] 10 140).result.isOk then return false
  for work in [:output.table.work] do
    let result := t.combineOwned .product a b 10 10000 work
    if result.result.isOk then return false
    match result.result with
    | .error failure => if failure.error != .work || failure.work > work then return false
    | _ => return false
  return true

#guard packed

private def exhaustion : Bool := Id.run do
  let .ok (a, t) := ({ arity := 3, hashBits := 0 } : MonomialTable).intern #[255, 0, 1] 10 10000
    | return false
  let .ok (b, t) := t.intern #[1, 1, 0] 10 10000 | return false
  let .ok (_, t) := t.intern #[0, 1, 1] 10 10000 | return false
  let cases := [(MonomialTable.Operation.lcm, a, a), (.product, a, b), (.quotient, b, a)]
  for cached in [false, true] do
    let t := if cached then (t.combineOwned .lcm a a 10 10000).table else t
    for (operation, a, b) in cases do
      for count in [:5] do
        for bytes in [:190] do
          if !same (t.combineOwned operation a b count bytes 10000 true)
              (t.combineOwned operation a b count bytes 10000 false) then return false
      for count in [t.count, t.count + 1] do
        for bytes in [t.bytes - 1, t.bytes, 168, 169] do
          for work in [:80] do
            if !same (t.combineOwned operation a b count bytes work true)
                (t.combineOwned operation a b count bytes work false) then return false
    let hit := t.combineOwned .lcm a a t.count (t.bytes - 1)
    match hit.result with
    | .error failure => if failure.error != .packedBytes then return false
    | _ => return false
    let widened := t.combineOwned .product a b 10 10000
    if !widened.result.isOk || widened.table.width != .u16 then return false
    let portable := t.combineOwned .product a b 10 10000 100000 false
    if !same widened portable then return false
    for i in [:t.count] do
      if widened.table.exponentsAt i != t.exponentsAt i then return false
  return true

#guard exhaustion

private def storage : Bool := Id.run do
  let .ok (_, t) := ({ arity := 2, hashBits := 0 } : MonomialTable).intern #[1, 0] 10 10000
    | return false
  for malformed in [{ t with exponents := t.exponents.push 0 },
      { t with metadata := t.metadata.push 0 },
      { t with buckets := t.buckets.insert 0 #[10] }] do
    for native in [false, true] do
      match (malformed.combineOwned .lcm 0 0 10 10000 10000 native).result with
      | .error error => if error.error != .storage then return false
      | _ => return false
    match (malformed.internOwned #[1, 0] 10 10000).result with
    | .error error => if error.error != .storage then return false
    | _ => return false
  return true

#guard storage

end Hex.Groebner.MonomialConformance
