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

def runtimeChecks (nonce : Nat) (forced : Bool := false) : Bool :=
  (checkRuntime nonce forced).isOk

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

end Hex.Groebner.SparseBinaryConformance
