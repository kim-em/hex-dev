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

/-- Maximum preparation spans, wide columns, malformed sparse rows and
arbitrary Nat allowances compare the actual foreign result with the model. -/
def boundaryChecks (seed : Nat) : Bool := Id.run do
  for n in [128,4096] do
    for first in [0,4294950000] do
      for step in [1,2] do
        let original := source n first step
        let original := { original with
          sugar := 2^90+seed
          coefficients := Native.write original.coefficients 4 68 2147483646 }
        for row in [original,
            { original with columns := Native.write original.columns 4 4 first },
            { original with columns := Native.write original.columns 4 68 4294967295 },
            { original with columns := original.columns.extract 0 (original.columns.size-1) },
            { original with coefficients := original.coefficients.extract 0 (original.coefficients.size-1) },
            { original with coefficients := Native.write original.coefficients 4 0 2 },
            { original with coefficients := Native.write original.coefficients 4 68 0 },
            { original with coefficients := Native.write original.coefficients 4 68 2147483647 },
            { original with coefficients := Native.write original.coefficients 4 68 4294967295 }] do
          for budget in [0,65535,65536,2^90] do
            let actual := Native.Dense.prepare modulus 4294967295 row budget 32768
            let model := Native.Dense.preparePortable modulus 4294967295 row budget 32768
            if actual.work != model.work || actual.packedBytes != model.packedBytes ||
                actual.row.first != model.row.first || actual.row.size != model.row.size ||
                actual.row.dense != model.row.dense || actual.row.source.columns != row.columns ||
                actual.row.source.coefficients != row.coefficients || actual.row.source.sugar != row.sugar then return false
  return true

private def same (a b : Native.Scan.Result) : Bool :=
  a.status == b.status && a.work == b.work && a.reductions == b.reductions &&
  a.traceNodes == b.traceNodes && a.events == b.events &&
  a.state.dense == b.state.dense && a.state.column == b.state.column &&
  a.state.last == b.state.last && a.state.chargedUntil == b.state.chargedUntil &&
  a.state.leading == b.state.leading && a.state.pending == b.state.pending &&
  a.state.entry == b.state.entry && a.state.sugar == b.state.sugar && a.state.factor == b.state.factor

/-- Every quantum and error returns the sparse model's exact update prefix,
including noncanonical target values in zero gaps and active vector lanes. -/
def scanChecks (seed : Nat) : Bool := Id.run do
  for step in [1,2] do
    let source := source 128 5 step
    let row := (Native.Dense.prepare modulus 300 source 100000 100000).row
    if row.dense.isEmpty then return false
    let slots := Native.write (Native.Dense.zeros 1200) 4 20 1
    let mut buffer := Native.Dense.zeros 1200
    for i in [:300] do buffer := Native.write buffer 4 (4*i) ((123*i+7+seed)%2147483647)
    for bad in [0,6,7,12,127,250,259,299,300] do
      let dense := if bad == 300 then buffer else Native.write buffer 4 (4*bad) 4294967295
      for entry in [0,1,7,8,127,128,129] do
        let initial : Native.Scan.State := {
          dense := dense
          column := 5
          last := 299
          chargedUntil := 300
          pending := 1
          entry := entry
          factor := 2147483646
          sugar := 3 }
        for quantum in [0,1,7,8,127,128,129,4096,4097] do
          for trace in [0,1] do
            let output := Native.Dense.transition modulus 300 slots #[row] initial quantum 100000 trace true
            let reference := Native.Dense.portable modulus 300 slots #[row] initial quantum 100000 trace true
            if !same output reference then return false
    for work in [0,63,64,127,128,191,192,100000] do
      let initial : Native.Scan.State := { dense := buffer,column := 5,last := 299,chargedUntil := 5 }
      let output := Native.Dense.transition modulus 300 slots #[row] initial 4096 work 1 true
      let reference := Native.Dense.portable modulus 300 slots #[row] initial 4096 work 1 true
      if !same output reference then return false
  return true

#guard boundaryChecks 0
#guard checks
#guard scanChecks 0


example (row : Native.Scan.Pivot) :
    Native.Dense.valid modulus 1024 (Native.Dense.Row.raw modulus 1024 row).source
      (Native.Dense.Row.raw modulus 1024 row).dense 0 0 = true := by rfl

end Hex.Groebner.DenseConformance
