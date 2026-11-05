/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGroebner.Elimination

namespace Hex.Groebner.SparseBinaryConformance

private def field : PrimeField :=
  ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩

private def same (a b : Elimination.Result) : Bool := Id.run do
  if a.stats != b.stats then return false
  match a.result,b.result with
  | .error a,.error b => return a == b
  | .ok (a,ar),.ok (b,br) =>
    if a.reducerRank != b.reducerRank || a.trace != b.trace ||
        a.rows.size != b.rows.size || ar.size != br.size then return false
    for (x,y) in a.rows.zip b.rows do
      if x.row.columns != y.row.columns || x.row.coefficients != y.row.coefficients ||
          x.fromTarget != y.fromTarget || x.derivation != y.derivation ||
          x.multiplier != y.multiplier || x.sugar != y.sugar then return false
    for (x,y) in ar.zip br do
      if x.row.columns != y.row.columns || x.row.coefficients != y.row.coefficients ||
          x.derivation != y.derivation || x.sugar != y.sugar then return false
    return true
  | _,_ => return false

private def sameAttempt (a b : Option Elimination.Result) : Bool :=
  match a,b with
  | none,none => true
  | some a,some b => same a b
  | _,_ => false

private def limits : MatrixLimits :=
  { columns := 2^20,rows := 2^20+4096,binaryPivots := true }

@[noinline] private def rows (columns nonce : Nat) :
    Option (Array SparseRow × Array SparseRow) := do
  if columns == 0 then return (#[],#[{},{}])
  let tail := columns-1
  let a ← SparseRow.ofEntries field columns
    (if columns > 1 then #[(0,1),(tail,1)] else #[(0,1)])
  let b ← if columns > 2 then SparseRow.ofEntries field columns #[(1,1),(tail,1)]
    else some ({} : SparseRow)
  let middle := (nonce%7) % min columns 5
  let target ← SparseRow.ofEntries field columns
    (if middle == 0 then #[(0,1)] else #[(0,1),(middle,1)])
  let last ← SparseRow.ofEntries field columns #[(tail,1)]
  return (#[a,b],#[target,a,last,{},target])

private def expected (forced : Bool) (budget : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :=
  if forced then Elimination.attemptSparsePortable field budget columns reducers targets sugars independent
  else Elimination.attemptPortable field budget columns reducers targets sugars independent

private def sameRows (a b : Array SparseRow) : Bool :=
  a.size == b.size && (a.zip b).all fun (x,y) =>
    x.columns == y.columns && x.coefficients == y.coefficients

/-- The forced native profile exercises sparse F2 on small matrices too.
Large dimensions are compiled runtime checks rather than kernel evaluation. -/
def checkRuntime (nonce : Nat) (forced : Bool := false) : Except String Unit := do
  if USize.size != 2^64 then return ()
  let sizes := if forced then [0,1,5,17,63,64,65,127,257]
    else [131072,131073,2^20-1,2^20]
  for columns in sizes do
    let some (er,et) := rows columns (nonce+7) | throw s!"reference rows C={columns}"
    let some (ar,actualTargets) := rows columns nonce | throw s!"native rows C={columns}"
    let sugars := (Array.range (er.size+et.size)).map fun i => 2^40+(i+nonce%11)*17
    for independent in [false,true] do
      let some reference := expected forced limits columns er et sugars independent
        | throw s!"portable declined C={columns} independent={independent}"
      let actual := Elimination.attempt field limits columns ar actualTargets sugars independent
      if !sameAttempt actual (some reference) then
        throw s!"result differs C={columns} independent={independent} native={actual.isSome}"
      if !sameRows ar er then throw s!"reducer buffers differ C={columns}"
      if !sameRows actualTargets et then throw s!"target buffers differ C={columns}"
      if forced || columns == 131073 then
        let scratch := if forced || Elimination.sparseBinary field limits columns er.size then
            Elimination.delayedBytes field columns er.size et.size
          else Elimination.binaryBytes columns er.size et.size
        let bytes := reference.stats.packedBytes+scratch
        let tight : MatrixLimits := { limits with packedBytes := bytes,work := reference.stats.work }
        if !sameAttempt (Elimination.attempt field tight columns ar actualTargets sugars independent)
            (expected forced tight columns er et sugars independent) then
          throw s!"tight budget differs C={columns} independent={independent}"
        for budget in ([{ tight with work := reference.stats.work-1 },
            { tight with packedBytes := bytes-1 },
            { tight with outputEntries := reference.stats.outputEntries-1 },
            { tight with inputEntries := reference.stats.inputEntries-1 }] : List MatrixLimits) do
          if !sameAttempt (Elimination.attempt field budget columns ar actualTargets sugars independent)
              (expected forced budget columns er et sugars independent) then
            throw s!"cut budget differs C={columns} independent={independent}"
  return ()

/-- Valid matrices immediately below, at and above the conservative 2^38 bound.
Only one reducer is nonempty and every target is empty, so replay stays small. -/
def shapeChecks : Bool := Id.run do
  if USize.size != 2^64 then return true
  for (columns,nr,entries,delta) in [(269193,459,995,0),(269194,39,12,1),(269194,179,3,2)] do
    let nt := 1009
    let bound := (nr+nt)*65+2*entries+5*columns+nt*(entries+(nt+3)*columns+64)+columns
    if bound != 2^38+delta-1 then return false
    let some row := SparseRow.ofEntries field columns ((Array.range entries).map (·,(1:UInt64)))
      | return false
    let reducers := (Array.replicate nr ({} : SparseRow)).set! 0 row
    let targets := Array.replicate nt ({} : SparseRow)
    let reference := Elimination.attemptPortable field limits columns reducers targets #[] false
    if reference.isSome != (delta != 2) then return false
    if !sameAttempt (Elimination.attempt field limits columns reducers targets #[] false) reference then
      return false
  return true

/-- Reducer-count widening, independent zero remainders, exact dimensional
ceilings and duplicate heads detected after sparse installation. -/
def cardinalityChecks : Bool := Id.run do
  if USize.size != 2^64 then return true
  let some row := SparseRow.ofEntries field 5 #[(0,1),(4,1)] | return false
  let reducers := (Array.replicate 131073 ({} : SparseRow)).set! 0 row
  for independent in [false,true] do
    let reference := Elimination.attemptPortable field limits 5 reducers #[row,{}] #[] independent
    if reference.isNone || !sameAttempt (Elimination.attempt field limits 5 reducers #[row,{}] #[] independent)
        reference then return false
  let duplicate := reducers.set! 131072 row
  if (Elimination.attempt field limits 5 duplicate #[] #[] false).isSome ||
      (Elimination.attemptPortable field limits 5 duplicate #[] #[] false).isSome then return false
  let tooMany := Array.replicate (2^20+1) ({} : SparseRow)
  for (columns,rs,ts) in [(2^20+1,#[],#[]),(5,tooMany,#[]),
      (131073,#[],Array.replicate 4097 ({} : SparseRow))] do
    let wide : MatrixLimits := { limits with columns := 2^20+1 }
    if (Elimination.attempt field wide columns rs ts #[] false).isSome ||
        (Elimination.attemptPortable field wide columns rs ts #[] false).isSome then return false
  return true

/-- Malformed buffers remain distinct from successful native frames. -/
def malformedChecks : Bool := Id.run do
  if USize.size != 2^64 then return true
  let columns := 131073
  let some valid := SparseRow.ofEntries field columns #[(0,1),(columns-1,1)] | return false
  let cs := valid.columns
  let zero : SparseRow := { columns := cs,coefficients := ByteArray.mk #[0,1] }
  let high : SparseRow := { columns := cs,coefficients := ByteArray.mk #[1,2] }
  let repeated : SparseRow := { columns := Packed.set .u32 cs 1 0,coefficients := valid.coefficients }
  let outside : SparseRow := { columns := Packed.set .u32 cs 1 columns.toUInt64,coefficients := valid.coefficients }
  let ragged : SparseRow := { columns := cs.push 0,coefficients := valid.coefficients }
  for bad in [zero,high,repeated,outside,ragged] do
    let actual := Elimination.attempt field limits columns #[bad] #[valid] #[] false
    let reference := Elimination.attemptPortable field limits columns #[bad] #[valid] #[] false
    if actual.isSome || !sameAttempt actual reference then return false
  for sugars in [#[1],#[2^100,0]] do
    if (Elimination.attempt field limits columns #[valid] #[valid] sugars false).isSome ||
        (Elimination.attemptPortable field limits columns #[valid] #[valid] sugars false).isSome then
      return false
  if (Elimination.attempt field limits (2^100) #[] #[] #[] false).isSome then return false
  let shared := #[valid,{}]
  let actual := Elimination.attempt field limits columns shared shared #[] true
  if !sameAttempt actual (Elimination.attemptPortable field limits columns shared shared #[] true) then
    return false
  return true

/-- A smaller test-native quantum forces a bounded refusal; the public matrix
operation still completes with the exact reference result and counters. -/
def capChecks (nonce : Nat) (cap : Nat := 2^34) : Option Nat := do
  let columns := 131073
  let (rs,ts) ← rows columns nonce
  let sugars := (Array.range (rs.size+ts.size)).map fun i => i+nonce%97
  let reference ← Elimination.attemptPortable field limits columns rs ts sugars false
  let actual := Elimination.attempt field limits columns rs ts sugars false
  if !sameAttempt actual (if reference.stats.work ≤ cap then some reference else none) then failure
  let completed := Elimination.run field limits columns rs ts false sugars true false
  if !same completed reference then failure
  return reference.stats.work

@[noinline] private def randomRows (columns nonce : Nat) :
    Option (Array SparseRow × Array SparseRow) := Id.run do
  let mut state := nonce % 2^32
  let mut reducers := #[]
  let mut targets := #[]
  for target in [false,true] do
    let count := if target then 32 else 24
    for i in [:count] do
      state := (1664525*state+1013904223) % 2^32
      let head := if !target || i%3 == 0 then columns-512+4*(i%24)
        else columns-320+2*(i%8)
      let mut support := #[head]
      if !target && i+1 < 24 then support := support.push (head+4)
      for _ in [:7] do
        state := (1664525*state+1013904223) % 2^32
        let column := head+1+state%(columns-head-1)
        if !support.contains column then support := support.push column
      let some row := SparseRow.ofEntries field columns
          ((support.qsort (· < ·)).map fun j => (j,(1:UInt64))) | return none
      if target then targets := targets.push (if i%11 == 0 then {} else row)
      else reducers := reducers.push row
  targets := targets.set! 29 targets[1]!
  return some (reducers,targets)

/-- Seeded short supports exercise dozens of known reducers and target pivots,
including reused target heads, independent remainders and aliased target rows. -/
def checkRandom (nonce : Nat) : Except String Unit := do
  if USize.size != 2^64 then return ()
  for trial in [:4] do
    let columns := 131073+trial*64
    let seed := nonce+trial*97
    let some (er,et) := randomRows columns seed | throw "random reference rows"
    let some (ar,nativeTargets) := randomRows columns (seed+2^32) | throw "random native rows"
    let sugars := (Array.range 56).map fun i => 2^40+i+seed%31
    if !Elimination.fitsSparse field limits columns er et sugars then
      throw "random sparse admission missing"
    for independent in [false,true] do
      let some reference := Elimination.attemptSparsePortable field limits columns er et sugars independent
        | throw "random sparse portable declined"
      if reference.stats.reductions ≤ 32 then throw "random reducer chains unused"
      let actual := Elimination.attempt field limits columns ar nativeTargets sugars independent
      if !sameAttempt actual (some reference) then
        throw s!"random sparse result differs trial={trial} independent={independent}"
      if !sameRows ar er || !sameRows nativeTargets et then throw "random sparse inputs mutated"
      if trial == 0 then
        let bytes := reference.stats.packedBytes+Elimination.delayedBytes field columns 24 32
        let tight : MatrixLimits := { limits with work := reference.stats.work,packedBytes := bytes }
        for budget in ([tight,{ tight with work := reference.stats.work-1 },
            { tight with packedBytes := bytes-1 }] : List MatrixLimits) do
          if !sameAttempt (Elimination.attempt field budget columns ar nativeTargets sugars independent)
              (Elimination.attemptSparsePortable field budget columns er et sugars independent) then
            throw "random sparse exact budget differs"
  return ()

/-- Definite packed payload refusals select one sparse attempt. The packed-only
native profile retains the original refusal as an independent control. -/
def checkSelection (nonce : Nat) (packedOnly : Bool := false) : Except String Unit := do
  if USize.size != 2^64 then return ()
  let columns := 16384
  let some erow := SparseRow.ofEntries field columns #[(0,1),(columns-1,1)]
    | throw "selection reference row"
  let some arow := SparseRow.ofEntries field columns #[(0,1),(columns-1,1)]
    | throw "selection native row"
  let er := (Array.replicate 128 ({} : SparseRow)).set! 0 erow
  let ar := (Array.replicate 128 ({} : SparseRow)).set! 0 arow
  let sugars := (Array.range 256).map fun i => 2^40+i+nonce%17
  for independent in [false,true] do
    let reference := Elimination.reference field limits columns er er sugars independent
    if !reference.result.isOk then throw "selection reference failed"
    let bytes := reference.stats.packedBytes+Elimination.delayedBytes field columns 128 128
    let tight : MatrixLimits := { limits with packedBytes := bytes,work := reference.stats.work }
    if !Elimination.selectSparse field tight columns er er then throw "sparse selection missing"
    if (Elimination.attemptPackedPortable field tight columns er er sugars independent).isSome then
      throw "packed-only payload admitted"
    let selected := Elimination.attemptPortable field tight columns er er sugars independent
    if selected.isNone then throw "selected portable backend declined"
    let budgets : List MatrixLimits := [tight,{ tight with work := reference.stats.work-1 },
      { tight with packedBytes := bytes-1 },
      { tight with inputEntries := reference.stats.inputEntries-1 },
      { tight with outputEntries := reference.stats.outputEntries-1 }]
    for budget in budgets do
      let expected := if packedOnly then
          Elimination.attemptPackedPortable field budget columns er er sugars independent
        else Elimination.attemptPortable field budget columns er er sugars independent
      let actual := Elimination.attempt field budget columns ar ar sugars independent
      if !sameAttempt actual expected then
        throw s!"selection budget differs independent={independent} packed={packedOnly}"
      if !sameRows ar er then throw "selection mutated shared buffers"
    let actual := Elimination.run field tight columns ar ar false sugars true independent
    if !same actual reference then throw "selected complete matrix differs"
    let disabled := { tight with binaryPivots := false }
    if Elimination.selectSparse field disabled columns er er ||
        (Elimination.attempt field disabled columns ar ar sugars independent).isSome then
      throw "selection ignored binary flag"
  let cs := arow.columns
  let invalid : Array SparseRow := #[
    { arow with columns := cs.push 0 },
    { arow with columns := Packed.set .u32 cs 0 (columns-1).toUInt64 },
    { arow with columns := Packed.set .u32 cs 1 columns.toUInt64 },
    { arow with coefficients := ByteArray.mk #[0,1] },
    { arow with coefficients := ByteArray.mk #[1,2] },
    { arow with coefficients := arow.coefficients.push 0 }]
  let budget : MatrixLimits := { limits with packedBytes := 220000 }
  for bad in invalid do
    let rs := ar.set! 0 bad
    if (Elimination.attempt field budget columns rs ar #[] false).isSome ||
        (Elimination.attemptPortable field budget columns rs ar #[] false).isSome then
      throw "selection accepted malformed row"
  let duplicate := ar.set! 1 arow
  if (Elimination.attempt field budget columns duplicate ar #[] false).isSome ||
      (Elimination.attemptPortable field budget columns duplicate ar #[] false).isSome then
    throw "selection accepted duplicate heads"
  let odd : PrimeField := ⟨3,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  if Elimination.selectSparse odd limits columns er er then throw "selected sparse odd field"
  return ()

def runtimeChecks (nonce : Nat) (forced : Bool := false) : Bool :=
  (checkRuntime nonce forced).isOk && (forced || (checkSelection nonce).isOk)

end Hex.Groebner.SparseBinaryConformance
