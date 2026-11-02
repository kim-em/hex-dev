/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Native

@[expose] public section

namespace Hex.Groebner.Native.Scan

/-- Layout mirrored in C (`matrix_scan.c`, `matrix_scan_impl.h`,
`matrix_eliminate.c`). -/
structure Pivot where
  columns : ByteArray
  coefficients : ByteArray
  sugar : Nat := 0
  deriving Inhabited

/-- Optional indices use index+1. A pending row is already charged in full.
Layout mirrored in C (`matrix_scan.c`, `matrix_scan_impl.h`, `matrix_eliminate.c`). -/
structure State where
  dense : ByteArray
  column : Nat
  last : Nat
  chargedUntil : Nat
  leading : Nat := 0
  pending : Nat := 0
  entry : Nat := 0
  sugar : Nat := 0
  factor : UInt64 := 0

/-- Status: 0 quantum ended, 1 complete, 2 work exhausted, 3 trace exhausted,
4 malformed. Events give pivot index and subtracted scalar, in execution order.
Layout mirrored in C (`matrix_scan.c`, `matrix_scan_impl.h`, `matrix_eliminate.c`). -/
structure Result where
  state : State
  events : Array (Nat × UInt64) := #[]
  work : Nat := 0
  reductions : Nat := 0
  traceNodes : Nat := 0
  status : UInt8 := 0

def rowSize (w : Nat) (row : Pivot) : Option Nat :=
  let size := row.columns.size / 4
  if row.columns.size % 4 != 0 || row.coefficients.size != size*w || size == 0 || size > 4294967295 then none
  else some size

/-- A bounded transition: a column visit, one entry update, or completion of
one reduction per iteration. Pending updates retain their charged work. -/
def portable (modulus : UInt64) (slots : @& ByteArray) (pivots : @& Array Pivot)
    (initial : State) (quantum workLimit traceLimit : Nat) (provenance : Bool) : Result := Id.run do
  let p := modulus.toNat
  let w := Native.width p
  let columns := initial.dense.size / w
  let mut out : Result := { state := initial }
  if p < 2 || p ≥ 2147483648 || quantum > 4096 || initial.dense.size % w != 0 ||
      columns > 4294967295 || slots.size != columns*4 || initial.column > columns ||
      (columns != 0 && initial.last ≥ columns) || initial.leading > columns ||
      initial.pending > pivots.size || pivots.size > 4294967295 ||
      initial.chargedUntil > columns || initial.entry > 4294967295 ||
      (initial.pending == 0 && initial.entry != 0) ||
      (initial.pending != 0 && initial.column ≥ columns) ||
      (columns == 0 && initial.last != 0) || initial.factor.toNat ≥ p then
    return { out with status := 4 }
  for _ in [:quantum] do
    let s := out.state
    if s.pending != 0 then
      let pivot := pivots[s.pending-1]!
      let some size := rowSize w pivot | return { out with status := 4 }
      if s.entry > size then return { out with status := 4 }
      if s.entry == size then
        out := { out with reductions := out.reductions+1 }
        if provenance then
          if out.traceNodes ≥ traceLimit then return { out with status := 3 }
          out := { out with events := out.events.push (s.pending - 1, s.factor), traceNodes := out.traceNodes+1 }
        out := { out with state := { s with pending := 0, entry := 0, column := s.column+1 } }
      else
        let j := Native.read pivot.columns 4 (4*s.entry)
        let b := Native.read pivot.coefficients w (w*s.entry)
        if j ≥ columns || b == 0 || b ≥ p || (s.entry > 0 &&
            Native.read pivot.columns 4 (4*(s.entry-1)) ≥ j) then
          return { out with status := 4 }
        let a := Native.read s.dense w (w*j)
        if a ≥ p then return { out with status := 4 }
        let product := s.factor.toNat * b % p
        let difference := a+p-product
        let value := if difference ≥ p then difference-p else difference
        out := { out with state := { s with dense := Native.write s.dense w (w*j) value, entry := s.entry+1 } }
    else
      if s.column ≥ columns || s.column > s.last then return { out with status := 1 }
      if s.column ≥ s.chargedUntil then
        let stop := min (s.column+64) (s.last+1)
        let charge := stop-s.column
        if out.work+charge > workLimit then return { out with status := 2 }
        out := { out with work := out.work+charge, state := { out.state with chargedUntil := stop } }
      let s := out.state
      let a := Native.read s.dense w (w*s.column)
      if a ≥ p then return { out with status := 4 }
      let slot := Native.read slots 4 (4*s.column)
      if a == 0 || slot == 0 then
        out := { out with state := { s with column := s.column+1, leading := if a != 0 && s.leading == 0 then s.column+1 else s.leading } }
      else
        if slot > pivots.size then return { out with status := 4 }
        let pivot := pivots[slot-1]!
        let some size := rowSize w pivot | return { out with status := 4 }
        if Native.read pivot.columns 4 0 != s.column || Native.read pivot.coefficients w 0 != 1 then
          return { out with status := 4 }
        let last := Native.read pivot.columns 4 (4*(size-1))
        if last ≥ columns then return { out with status := 4 }
        out := { out with state := { s with last := max s.last last, sugar := max s.sugar pivot.sugar } }
        if out.work+size > workLimit then return { out with status := 2 }
        out := { out with work := out.work+size, state := { out.state with
          pending := slot, entry := 0, factor := a.toUInt64 } }
  return out

@[extern "lean_hex_scan_transition"]
def transition (modulus : UInt64) (slots : @& ByteArray) (pivots : @& Array Pivot)
    (initial : State) (quantum workLimit traceLimit : @& Nat) (provenance : Bool) : Result :=
  portable modulus slots pivots initial quantum workLimit traceLimit provenance

end Hex.Groebner.Native.Scan
