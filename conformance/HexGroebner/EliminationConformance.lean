/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGroebner.Elimination
import HexGroebner.Fixtures

namespace Hex.Groebner.EliminationConformance

private def field : PrimeField :=
  ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

private def same (a b : Elimination.Result) : Bool := Id.run do
  if a.stats != b.stats then return false
  match a.result,b.result with
  | .error a,.error b => return a == b
  | .ok (a,ar),.ok (b,br) =>
    if a.reducerRank != b.reducerRank || a.trace != b.trace ||
        a.rows.size != b.rows.size || ar.size != br.size then return false
    for i in [:a.rows.size] do
      let x := a.rows[i]!
      let y := b.rows[i]!
      if x.row.columns != y.row.columns || x.row.coefficients != y.row.coefficients ||
          x.fromTarget != y.fromTarget || x.derivation != y.derivation ||
          x.multiplier != y.multiplier || x.sugar != y.sugar then return false
    for i in [:ar.size] do
      let x := ar[i]!
      let y := br[i]!
      if x.row.columns != y.row.columns || x.row.coefficients != y.row.coefficients ||
          x.derivation != y.derivation || x.sugar != y.sugar then return false
    return true
  | _,_ => return false

def basic : Bool := Id.run do
  let some r := SparseRow.ofEntries field 3 #[(0,2),(2,1)] | return false
  let some t := SparseRow.ofEntries field 3 #[(0,4),(1,1)] | return false
  for independent in [false,true] do
    let some expected := Elimination.attemptPortable field {} 3 #[r] #[t] #[2,3] independent
      | return false
    let some actual := Elimination.attempt field {} 3 #[r] #[t] #[2,3] independent
      | return false
    if !same actual expected then return false
    if !independent && actual.stats.work != 41 then return false
  return true

#guard basic

private def sameAttempt (a b : Option Elimination.Result) : Bool :=
  match a,b with
  | none,none => true
  | some a,some b => same a b
  | _,_ => false

private def sameRows (a b : Array SparseRow) : Bool :=
  a.size == b.size && (a.zip b).all fun (x,y) =>
    x.columns == y.columns && x.coefficients == y.coefficients

/-- Different nonces produce equal independent buffers, retaining a separate
copy against which borrowed-input preservation can be checked. -/
@[noinline] private def rows (field : PrimeField) (columns reducers targets seed : Nat) :
    Option (Array SparseRow × Array SparseRow × Array Nat) := Id.run do
  let salt := seed % 7
  let reducers := min reducers columns
  let mut all := #[]
  let mut sugars := #[]
  for i in [:reducers+targets] do
    let mut entries := #[]
    if (salt+i)%5 != 0 then
      for column in [:columns] do
        let keep := if i < reducers then
          column ≥ i && (column == i || (column+i+salt)%4 == 0)
        else (column+3*i+salt)%4 == 0
        if keep then
          entries := entries.push (column,
            ((salt+3*i+5*column)%(field.modulus.toNat-1)+1).toUInt64)
    let some row := SparseRow.ofEntries field columns entries | return none
    all := all.push row
    sugars := sugars.push ((i+salt)%11)
  return some (all.extract 0 reducers,all.extract reducers all.size,sugars)

private def check (field : PrimeField) (limits : MatrixLimits) (columns nr nt seed : Nat)
    (independent : Bool) : Bool := Id.run do
  let some (er,et,es) := rows field columns nr nt (seed+7) | return false
  let expected := Elimination.attemptPortable field limits columns er et es independent
  let some (ar,actualTargets,actualSugars) := rows field columns nr nt (seed+14) | return false
  let actual := Elimination.attempt field limits columns ar actualTargets actualSugars independent
  return sameAttempt actual expected && sameRows ar er && sameRows actualTargets et

private def denseChecks (field : PrimeField) : Bool := Id.run do
  let columns := 4096
  let coefficient := if field.modulus == 2 then 1 else 2
  let some reducer := SparseRow.ofEntries field columns
    ((Array.range columns).map fun i => (i,1)) | return false
  let some target := SparseRow.ofEntries field columns
    ((Array.range columns).map fun i => (i,coefficient)) | return false
  for reducers in [#[],#[reducer]] do
    for independent in [false,true] do
      let some expected := Elimination.attemptPortable field {} columns reducers #[target] #[] independent
        | return false
      let some actual := Elimination.attempt field {} columns reducers #[target] #[] independent
        | return false
      if !same actual expected then return false
  return true

/-- Unsupported dimensions, noncanonical rows, arbitrary Nat allowances and
all resource limits retain the reference's rejection or completed outcome. -/
def boundaryChecks : Bool := Id.run do
  let some r := SparseRow.ofEntries field 3 #[(0,2),(2,1)] | return false
  let some t := SparseRow.ofEntries field 3 #[(0,4),(1,1)] | return false
  let malformed : Array SparseRow := #[
    { r with columns := r.columns.push 0 },
    { r with coefficients := r.coefficients.push 0 },
    { r with coefficients := Packed.set field.width r.coefficients 0 0 },
    { r with columns := Packed.set .u32 r.columns 0 3 },
    { r with columns := Packed.set .u32 r.columns 1 0 }]
  for independent in [false,true] do
    for row in malformed do
      for (reducers,targets) in [(#[row],#[t]),(#[r],#[row])] do
        let expected := Elimination.attemptPortable field {} 3 reducers targets #[] independent
        let actual := Elimination.attempt field {} 3 reducers targets #[] independent
        if !sameAttempt actual expected then return false
    for columns in [0,2,3,4096,4097,2^90] do
      for reducers in [#[r],#[r,r]] do
        for sugars in [#[],#[2,3],#[2],#[2,USize.size/2-1],#[2,USize.size/2],#[2,2^90]] do
          let expected := Elimination.attemptPortable field {} columns reducers #[t] sugars independent
          let actual := Elimination.attempt field {} columns reducers #[t] sugars independent
          if !sameAttempt actual expected then return false
    for n in [0,1,2,3,4,5,16,32,64,1000000,USize.size/2-1,USize.size/2,2^90] do
      for limits in ([{ columns := n },{ rows := n },{ inputEntries := n },
          { outputEntries := n },{ packedBytes := n },{ work := n },{ traceNodes := n }] :
          List MatrixLimits) do
        let expected := Elimination.attemptPortable field limits 3 #[r] #[t] #[] independent
        let actual := Elimination.attempt field limits 3 #[r] #[t] #[] independent
        if !sameAttempt actual expected then return false
  return true

#guard boundaryChecks

@[noinline] private def thresholdRows (columns nr entries nonce : Nat) :
    Option (Array SparseRow × Array SparseRow) := Id.run do
  let mut reducers := #[]
  if nr != 0 then
    let some row := SparseRow.ofEntries field columns #[(0,(nonce%7+1).toUInt64)] | return none
    reducers := #[row]
  let count := entries-nr
  let mut targets := #[]
  for i in [:64] do
    let length := count/64 + if i < count%64 then 1 else 0
    let values := (Array.range length).map fun j => (j+nr,(nonce%7+1).toUInt64)
    let some row := SparseRow.ofEntries field columns values | return none
    targets := targets.push row
  return some (reducers,targets)

/-- Both sides of the hand-copied work-quantum threshold, with valid sparse
rows and independently allocated expected inputs. -/
def thresholdChecks : Bool := Id.run do
  if USize.size != 2^64 then return true
  for (columns,nr,entries,bound) in [(205,0,2425,2^20),(222,1,1318,2^20+1)] do
    let some (er,et) := thresholdRows columns nr entries 7 | return false
    let actualEntries := (er ++ et).foldl (fun n row => n + row.size) 0
    let actualBound := (nr+64)*65+2*actualEntries+columns*(field.width.bytes+4)+
      64*(actualEntries+(64+3)*columns+64)+columns
    if actualEntries != entries || actualBound != bound then return false
    if Elimination.fits field {} columns er et #[] != (bound == 2^20) then return false
    for independent in [false,true] do
      let expected := Elimination.attemptPortable field {} columns er et #[] independent
      let some (ar,actualTargets) := thresholdRows columns nr entries 14 | return false
      let actual := Elimination.attempt field {} columns ar actualTargets #[] independent
      if (bound == 2^20 && actual.isNone) || !sameAttempt actual expected ||
          !sameRows ar er || !sameRows actualTargets et then return false
  return true

#guard thresholdChecks

/-- The reducer and target arrays are the same borrowed object. Independent
reference buffers detect mutation, and the native call must accept. -/
def sharedChecks (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let nonce := seed + if seed%7 == 0 || seed%7 == 5 then 1 else 0
  for independent in [false,true] do
    let some (er,_,_) := rows field 3 1 0 (nonce+7) | return false
    let some expected := Elimination.attemptPortable field {} 3 er er #[] independent
      | return false
    let some (ar,_,_) := rows field 3 1 0 nonce | return false
    let some actual := Elimination.attempt field {} 3 ar ar #[] independent | return false
    if !same actual expected || !sameRows ar er then return false
  return true

#guard sharedChecks 0

def runtimeChecks (seed : Nat) : Bool := Id.run do
  for field in Fixtures.fields do
    for columns in [0,1,3,9,65,257] do
      for (nr,nt) in [(0,0),(3,0),(0,3),(3,1),(3,3),(3,8),(3,9),(3,32),(3,64)] do
        for independent in [false,true] do
          let some (er,et,es) := rows field columns nr nt (seed+7) | return false
          let expected := Elimination.attemptPortable field {} columns er et es independent
          let some (actualReducers,actualTargets,actualSugars) := rows field columns nr nt seed | return false
          let actual := Elimination.attempt field {} columns actualReducers actualTargets actualSugars independent
          if !sameAttempt actual expected || !sameRows actualReducers er || !sameRows actualTargets et then return false
    if !denseChecks field then return false
    let some (rs,ts,sugars) := rows field 9 3 3 seed | return false
    for independent in [false,true] do
      let expected := Elimination.reference field {} 9 rs ts sugars independent
      for work in [:expected.stats.work+1] do
        let limits : MatrixLimits := { work }
        if !check field limits 9 3 3 (seed+7*work) independent then return false
      for entries in [:expected.stats.outputEntries+1] do
        let limits : MatrixLimits := { outputEntries := entries }
        if !check field limits 9 3 3 (seed+7*entries) independent then return false
      for bytes in [:expected.stats.packedBytes+1] do
        let limits : MatrixLimits := { packedBytes := bytes }
        if !check field limits 9 3 3 (seed+7*bytes) independent then return false
  return true

end Hex.Groebner.EliminationConformance
