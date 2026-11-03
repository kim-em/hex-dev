/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.NativeDense
import HexGroebner.Packed

namespace Hex.Groebner.DenseConformance

private def modulus : UInt64 := 2147483647

private def source (n first step : Nat) : Native.Scan.Pivot := Id.run do
  let mut columns : ByteArray := {}
  let mut coefficients : ByteArray := {}
  for i in [:n] do
    columns := Packed.push .u32 columns (first+step*i).toUInt64
    coefficients := Packed.push .u32 coefficients (i+1).toUInt64
  return ⟨columns,coefficients,7⟩

/-- Literal coefficient formulas independently check dense gaps, monicity,
metadata and exact admission boundaries. Refusal leaves the input row intact. -/
def checks : Bool := Id.run do
  for step in [1,2] do
    let row := source 128 5 step
    let span := 127*step+1
    let bytes := span*4
    let cost := bytes+384+span+2
    for budget in [0,cost-1,cost,cost+1] do
      let result := Native.Dense.prepare modulus 1024 row budget bytes
      let reference := Native.Dense.preparePortable modulus 1024 row budget bytes
      if result.work != reference.work || result.packedBytes != reference.packedBytes ||
          result.row.dense != reference.row.dense || result.row.first != reference.row.first ||
          result.row.size != reference.row.size then return false
      if result.work > budget || result.packedBytes > bytes then return false
      if budget < cost then
        if !result.row.dense.isEmpty || result.work != 0 || result.packedBytes != 0 then return false
      else
        if result.work != cost || result.packedBytes != bytes || result.row.first != 5 ||
            result.row.size != 128 || result.row.source.sugar != 7 then return false
        for i in [:span] do
          let expected := if i%step == 0 then i/step+1 else 0
          if Native.read result.row.dense 4 (4*i) != expected then return false
        for dense in [Native.write result.row.dense 4 0 2,
            result.row.dense.extract 0 (bytes-1)] do
          if (Native.Dense.Row.check modulus 1024 row dense 5 128).isSome then return false
    let refused := Native.Dense.prepare modulus 1024 row cost (bytes-1)
    if !refused.row.dense.isEmpty || refused.work != 0 || refused.packedBytes != 0 then return false
    let bad := { row with coefficients := Native.write row.coefficients 4 (4*63) 0 }
    let rejected := Native.Dense.prepare modulus 1024 bad cost bytes
    if !rejected.row.dense.isEmpty || rejected.work != 129 || rejected.packedBytes != 0 then return false
  for row in [source 0 0 1,source 127 0 1,source 4097 0 1,source 128 0 3] do
    let result := Native.Dense.prepare modulus 20000 row 1000000 1000000
    if !result.row.dense.isEmpty || result.work != 0 || result.packedBytes != 0 then return false
  let row := source 128 0 2
  for p in [2,251,32003,65537] do
    let result := Native.Dense.prepare p 1024 row 1000000 1000000
    if !result.row.dense.isEmpty || result.work != 0 || result.packedBytes != 0 then return false
  -- A valid sparse row with a very wide gap cannot forge a dense-cache witness.
  let sparse := source 2 0 100
  let dense := Native.write (Native.write (Native.Dense.zeros 404) 4 0 1) 4 400 2
  if (Native.Dense.Row.check modulus 1024 sparse dense 0 2).isSome then return false
  return true

#guard checks

example (row : Native.Scan.Pivot) :
    Native.Dense.valid modulus 1024 (Native.Dense.Row.raw modulus 1024 row).source
      (Native.Dense.Row.raw modulus 1024 row).dense 0 0 = true := by rfl

end Hex.Groebner.DenseConformance
