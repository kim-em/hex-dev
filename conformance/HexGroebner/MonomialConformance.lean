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

end Hex.Groebner.MonomialConformance
