/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.MonomialIndex
import HexGroebner.Native

namespace Hex.Groebner.SearchConformance

private def word (bytes : ByteArray) (value : UInt64) : ByteArray :=
  Packed.push .u32 (Packed.push .u32 bytes value) (value >>> 32)

/-- Runtime native/portable comparison over all widths, exact hash collisions,
work cutoffs, empty/invalid slices and arbitrary-precision allowances. -/
def runtimeChecks (seed : Nat) : Bool := Id.run do
  for width in [Width.u8, .u16, .u32] do
    for arity in [1,2,3,7,65] do
      let count := 12
      let mut exponents : ByteArray := {}
      let mut metadata : ByteArray := {}
      let mut links : ByteArray := {}
      let mut candidate : ByteArray := {}
      for id in [:count] do
        for coordinate in [:arity] do
          exponents := Packed.push width exponents (id+coordinate+seed%7).toUInt64
        metadata := word (word (word metadata 0) 0) (id%3).toUInt64
        links := Packed.push .u32 links id.toUInt64
      for coordinate in [:arity] do
        candidate := Packed.push .u32 candidate (7+coordinate+seed%7).toUInt64
      for _ in [:28] do candidate := candidate.push 0
      for hash in [0,1,2,19] do
        for link in [0,1,count,count+1,4294967295,18446744073709551615] do
          for quantum in [0,1,2,4096/arity,4097] do
            for allowance in [0,1,arity,arity+1,100000,2^90] do
              let a := Native.Monomial.search width.bytes.toUInt8 arity.toUInt64
                count.toUInt64 hash link.toUInt64 quantum.toUInt64 exponents metadata links candidate allowance
              let b := Native.Monomial.searchPortable width.bytes.toUInt8 arity.toUInt64
                count.toUInt64 hash link.toUInt64 quantum.toUInt64 exponents metadata links candidate allowance
              if a != b then return false
      for (es,ms,ls,cs) in [(exponents.push 0,metadata,links,candidate),
          (exponents,metadata.push 0,links,candidate), (exponents,metadata,links.push 0,candidate),
          (exponents,metadata,links,candidate.push 0), (links,links,links,links)] do
        let a := Native.Monomial.search width.bytes.toUInt8 arity.toUInt64 count.toUInt64 0
          count.toUInt64 1 es ms ls cs 1000
        let b := Native.Monomial.searchPortable width.bytes.toUInt8 arity.toUInt64 count.toUInt64 0
          count.toUInt64 1 es ms ls cs 1000
        if a != b || a.status != 4 then return false
  return true

/-- Resume a forced collision chain beyond one native coordinate quantum. -/
def longChecks (seed : Nat) : Bool := Id.run do
  let mut exponents : ByteArray := {}
  let mut metadata : ByteArray := {}
  let mut links : ByteArray := {}
  for id in [:5000] do
    exponents := Packed.push .u8 (Packed.push .u8 exponents (id%251).toUInt64)
      (id/251).toUInt64
    metadata := word (word (word metadata 0) 0) 0
    links := Packed.push .u32 links id.toUInt64
  let mut candidate := Packed.push .u32 (Packed.push .u32 {} 0) 0
  for _ in [:28] do candidate := candidate.push 0
  let quantum := 1 + seed%2048
  let mut link := 5000
  let mut work := 0
  for _ in [:5001] do
    let a := Native.Monomial.search 1 2 5000 0 link.toUInt64 quantum.toUInt64
      exponents metadata links candidate 100000
    let b := Native.Monomial.searchPortable 1 2 5000 0 link.toUInt64 quantum.toUInt64
      exponents metadata links candidate 100000
    if a != b then return false
    work := work + a.work
    if a.status == 1 then return a.id == 0 && work == 15000
    if a.status != 0 || a.link ≥ link then return false
    link := a.link
  return false

#guard runtimeChecks 0
#guard longChecks 2047

end Hex.Groebner.SearchConformance
