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

/-- Check both sides of every separately copied matrix-size cap. -/
def sizeChecks (seed : Nat) : Bool := Id.run do
  for (columns,nr,nt) in [(3,0,64),(3,0,65),(1025,1024,1),(1025,1025,1)] do
    let some (er,et,es) := rows field columns nr nt (seed+7) | return false
    let some (ar,actualTargets,actualSugars) := rows field columns nr nt seed | return false
    let expected := Elimination.attemptPortable field {} columns er et es false
    let actual := Elimination.attempt field {} columns ar actualTargets actualSugars false
    if !sameAttempt actual expected || !sameRows ar er || !sameRows actualTargets et then return false
    if USize.size == 2^64 && ((nr == 1024 || nt == 64) && actual.isNone) then return false
    if (nr == 1025 || nt == 65) && actual.isSome then return false
  return true

#guard sizeChecks 0

@[noinline] private def binaryLargeRows (nonce : Nat) : Option (Array SparseRow × Array SparseRow) := do
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let salt := nonce%7
  let reducers ← (Array.range 2048).mapM fun i =>
    SparseRow.ofEntries field 8192 (#[ (i,(1:UInt64)) ] ++
      (Array.range 1024).map fun j => (4096+salt+j,(1:UInt64)))
  let targets ← (Array.range 128).mapM fun i =>
    SparseRow.ofEntries field 8192 (#[ (1900+i,(1:UInt64)) ] ++
      (if i == 0 then #[] else #[(2048+i-1,(1:UInt64))]) ++
      #[ (2048+i,(1:UInt64)) ] ++
      (Array.range 1024).map fun j => (4096+salt+j,(1:UInt64)))
  return (reducers,targets)

/-- Nonempty rows beyond all old caps, sparse wide updates, high leading
columns, and both sides of the physical bound with nonzero input entries. -/
def binaryLargeChecks (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  for independent in [false,true] do
    let some (er,et) := binaryLargeRows (seed+7) | return false
    let some (ar,actualTargets) := binaryLargeRows seed | return false
    let some expected := Elimination.attemptPortable field limits 8192 er et #[] independent | return false
    let some actual := Elimination.attempt field limits 8192 ar actualTargets #[] independent | return false
    if !same actual expected || !sameRows ar er || !sameRows actualTargets et then return false
  let some high := SparseRow.ofEntries field 8192 #[(7000,1),(8191,1)] | return false
  if (Elimination.attempt field limits 8192 #[high,high] #[] #[] false).isSome then return false
  if (Elimination.attempt field {} 8192 #[high] #[] #[] false).isSome ||
      (Elimination.attemptPortable field {} 8192 #[high] #[] #[] false).isSome then return false
  let other : PrimeField := ⟨3,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  if (Elimination.attempt other limits 8192 #[] #[] #[] false).isSome ||
      (Elimination.attemptPortable other limits 8192 #[] #[] #[] false).isSome then return false
  if !sameAttempt (Elimination.attempt field limits 0 #[] #[{}] #[] true)
      (Elimination.attemptPortable field limits 0 #[] #[{}] #[] true) then return false
  let some reducer := SparseRow.ofEntries field 129 #[(0,1),(128,1)] | return false
  let some target := SparseRow.ofEntries field 129 #[(0,1),(64,1)] | return false
  for sugar in [2^32+7,2^40+1,USize.size/2-1] do
    let some expected := Elimination.attemptPortable field limits 129 #[reducer] #[target] #[sugar,0] false
      | return false
    let some actual := Elimination.attempt field limits 129 #[reducer] #[target] #[sugar,0] false
      | return false
    if !same actual expected then return false
  if Elimination.binaryBound 16384 16313 62 14317 != 2^28-1 ||
      Elimination.binaryBound 16384 16313 62 14318 != 2^28+2 then return false
  for entries in [14317,14318] do
    let some row := SparseRow.ofEntries field 16384 ((Array.range entries).map (·,(1:UInt64))) | return false
    let reducers := (Array.replicate 16313 ({} : SparseRow)).set! 0 row
    let targets := Array.replicate 62 ({} : SparseRow)
    let expected := Elimination.attemptPortable field limits 16384 reducers targets #[] false
    let actual := Elimination.attempt field limits 16384 reducers targets #[] false
    if expected.isSome != (entries == 14317) || !sameAttempt actual expected then return false
  return true

/-- A target-built dense pivot is reused by an aliased target. The returned
amount is the complete private allocation expected in the native counter. -/
def binaryTargetChecks (seed : Nat) : Option Nat := do
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let some row := SparseRow.ofEntries field 257 ((Array.range 257).map (·,(1:UInt64))) | none
  let limits : MatrixLimits := { binaryPivots := true }
  let mut allocated := 0
  for count in [2,3] do
    let targets := Array.replicate count row
    let sugars := (Array.range count).map (seed+·)
    let some expected := Elimination.attemptPortable field limits 257 #[] targets sugars false | none
    let some actual := Elimination.attempt field limits 257 #[] targets sugars false | none
    if !same actual expected then none
    allocated := allocated+Elimination.binaryBytes 257 0 count
  return allocated

/-- The logical quantum is attained with 1024 nonempty targets while the
independent physical bound remains below its cap. One more entry is declined. -/
def binaryQuantum (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  let bound := fun entries => 1024*65+2*entries+3904*5+
    1024*(entries+(1024+3)*3904+64)+3904
  if bound 184384 != 2^32 || bound 184385 != 2^32+1026 ||
      Elimination.binaryBound 3904 0 1024 184385 > 2^28 then return false
  let some targets := (Array.range 1024).mapM fun i => SparseRow.ofEntries field 3904
      ((Array.range (if i < 64 then 181 else 180)).map (fun j => (j+seed%64,(1:UInt64)))) | return false
  let some expected := Elimination.attemptPortable field limits 3904 #[] targets #[] false | return false
  let some actual := Elimination.attempt field limits 3904 #[] targets #[] false | return false
  if !same actual expected then return false
  let some extra := SparseRow.ofEntries field 3904 ((Array.range 182).map (fun j => (j+seed%64,(1:UInt64)))) | return false
  let refused := targets.set! 0 extra
  return (Elimination.attemptPortable field limits 3904 #[] refused #[] false).isNone &&
    (Elimination.attempt field limits 3904 #[] refused #[] false).isNone


/-- All five private buffers are live in these two projected frames. Return
exact logical payload bytes for the compiled allocation counter assertion. -/
def binaryAllocationChecks (seed : Nat) : Option Nat := do
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  let some reducers := (Array.range 4).mapM fun head => SparseRow.ofEntries field 128
      ((Array.range (128-head)).map fun j => (head+j,(1:UInt64))) | none
  let some row := SparseRow.ofEntries field 128
      ((Array.range 128).filterMap fun j => if (j+seed)%3 != 0 then some (j,(1:UInt64)) else none) | none
  let targets := Array.replicate 64 row
  let sugars := (Array.range 68).map fun i => 2^40+seed%17+i
  for independent in [false,true] do
    let some expected := Elimination.attemptPortable field limits 128 reducers targets sugars independent | none
    let some actual := Elimination.attempt field limits 128 reducers targets sugars independent | none
    if !same actual expected then none
  return 2*Elimination.binaryBytes 128 4 64

#guard (binaryAllocationChecks 0).isSome

/-- Known reducers are unsorted and cross target-pivot columns. Projection
must preserve all factors, sugar maxima, independent rows and exact budgets. -/
def binaryProjectChecks (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  let heads := #[16,0,32,4]
  let some reducers := heads.mapM fun head => SparseRow.ofEntries field 129
      ((Array.range 129).filterMap fun j =>
        if j == head || (j > head && (j*7+head+seed)%11 < 5) then some (j,(1:UInt64)) else none)
    | return false
  let some targets := (Array.range 64).mapM fun i => SparseRow.ofEntries field 129
      ((Array.range 129).filterMap fun j =>
        if i%13 != 0 && (j*13+i*17+seed)%23 < 11 then some (j,(1:UInt64)) else none)
    | return false
  let sugars := (Array.range 68).map fun i => 2^40+i*17+seed
  for independent in [false,true] do
    let some expected := Elimination.attemptPortable field limits 129 reducers targets sugars independent
      | return false
    let some actual := Elimination.attempt field limits 129 reducers targets sugars independent
      | return false
    if !same actual expected then return false
    let packed := expected.stats.packedBytes+Elimination.binaryBytes 129 4 64
    for bounded in [{ limits with packedBytes := packed },
        { limits with packedBytes := packed-1 },
        { limits with work := expected.stats.work },
        { limits with work := expected.stats.work-1 }] do
      if !sameAttempt (Elimination.attempt field bounded 129 reducers targets sugars independent)
          (Elimination.attemptPortable field bounded 129 reducers targets sugars independent) then return false
  return true

/-- All triangular four-pivot patterns and every incoming head mask, with
common tails that cancel while reference charges and sugar maxima persist. -/
def binaryTableChecks (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  let heads := #[0,3,7,11]
  for pattern in [:64] do
    let some rows := (Array.range 4).mapM fun k => SparseRow.ofEntries field 129
        ((Array.range 129).filterMap fun j =>
          let bit := if k == 0 then (if j == 3 then 0 else if j == 7 then 1 else 2)
            else if k == 1 then (if j == 7 then 3 else 4) else 5
          if j == heads[k]! || (64 ≤ j && j < 96) ||
              (j > heads[k]! && heads.contains j && (pattern/2^bit)%2 == 1) then
            some (j,(1:UInt64)) else none)
      | return false
    -- Reversing the supplied reducers must not change column-order projection.
    let reducers := rows.reverse
    let some targets := (Array.range 64).mapM fun i => SparseRow.ofEntries field 129
        ((Array.range 129).filterMap fun j =>
          let bit := if j == 0 then 0 else if j == 3 then 1 else if j == 7 then 2 else 3
          if (heads.contains j && (i/2^bit)%2 == 1) ||
              (j == 1 && i/16%2 == 1) || (j == 5 && i/32 == 1) ||
              (j == 100+seed%7 && i/32 == 1) then some (j,(1:UInt64)) else none)
      | return false
    let sugars := (Array.range 68).map fun i =>
      if i < 4 then 2^40+1000+(3*i+seed)%4 else seed%17+i-4
    for independent in [false,true] do
      let some expected := Elimination.attemptPortable field limits 129 reducers targets sugars independent
        | return false
      let some actual := Elimination.attempt field limits 129 reducers targets sugars independent
        | return false
      if !same actual expected then return false
  return true

/-- Unsorted dense runs and sparse interruptions preserve reducer labels
above target labels. Targets ending at the heads expose single-pivot extensions. -/
def binaryGroupChecks (seed : Nat) : Option Nat := do
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  let some rows := (#[0,3,7,11,65,68,72,76] : Array Nat).mapM fun head =>
      SparseRow.ofEntries field 129 (#[ (head,(1:UInt64)) ] ++
        (Array.range 33).map fun j => (96+j,(1:UInt64))) | none
  let some gap := SparseRow.ofEntries field 129 #[(5,1),(127,1)] | none
  let some gap' := SparseRow.ofEntries field 129 #[(66,1)] | none
  let specs : Array (Array Nat) := #[#[0],#[5],#[66],#[0,3,7,11,65,68,72,76]]
  let some targets := (Array.range 64).mapM fun i =>
      SparseRow.ofEntries field 129 (specs[i%4]!.map (·,(1:UInt64))) | none
  let tail := (Array.range 33).map (fun j => (96+j,(1:UInt64)))
  let cases := #[(rows.reverse.push {},2),((rows.push gap).reverse,1),
    ((rows.push gap |>.push gap').reverse,0)]
  let mut total := 0
  for (reducers,groups) in cases do
    if Elimination.binaryGroups 129 reducers != groups then none
    let labels := (Array.range reducers.size).map fun i => 2^40+1000+(7*i+seed)%reducers.size
    let sugars := labels ++ (Array.range 64).map (seed%17+·)
    let label := fun head => (Array.range reducers.size).foldl (fun value i =>
      if reducers[i]!.size != 0 && (Packed.read .u32 reducers[i]!.columns 0).toNat == head then
        labels[i]! else value) 0
    for independent in [false,true] do
      let some expected := Elimination.attemptPortable field limits 129 reducers targets sugars independent | none
      let some actual := Elimination.attempt field limits 129 reducers targets sugars independent | none
      if !same actual expected then none
      let .ok (echelon,remainders) := actual.result | none
      if independent then
        if remainders.size != 64 || remainders[0]!.row.entries field != tail ||
            remainders[0]!.sugar != label 0 then none
        if groups < 2 && (remainders[1]!.row.entries field != #[(127,1)] ||
            remainders[1]!.sugar != label 5) then none
        if groups == 0 && (remainders[2]!.row.size != 0 ||
            remainders[2]!.sugar != label 66) then none
      else if !(echelon.rows.any fun pivot => pivot.fromTarget &&
          pivot.row.entries field == tail && pivot.sugar == label 0) then none
      total := total+groups
  return total

/-- Seeded wide matrices mix sparse interruptions, triangular known heads,
empty targets, non-monotone source labels and absent label arrays. -/
def binaryRandomChecks (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  for trial in [:8] do
    for columns in [193,1031] do
      let some rows := (Array.range 40).mapM fun i => SparseRow.ofEntries field columns
          ((Array.range columns).filterMap fun j =>
            if j == 3*i || (i%5 != 0 && j > 3*i &&
                ((i+3)*(j+7)+13*i*i+trial*17+seed)%29 < 13) then
              some (j,(1:UInt64)) else none) | return false
      let reducers := rows.reverse
      let count := 64+16*(trial%3)
      let some targets := (Array.range count).mapM fun i => SparseRow.ofEntries field columns
          ((Array.range columns).filterMap fun j =>
            if i%17 != 0 && ((j+1)*(i+5)+trial*29+seed)%31 < 8 then
              some (j,(1:UInt64)) else none) | return false
      let labels := (Array.range (40+count)).map fun i =>
        if i < 40 then 2^40+1000+(17*i+seed+trial)%40 else seed%17+i-40
      for sugars in [#[],labels] do
        for independent in [false,true] do
          let some expected := Elimination.attemptPortable field limits columns reducers targets sugars independent
            | return false
          let some actual := Elimination.attempt field limits columns reducers targets sugars independent
            | return false
          if !same actual expected then return false
  return true

/-- A nonempty 154-table frame is two visits below the physical cap; one
additional input entry exceeds it. Few nonempty targets keep replay bounded. -/
def binaryTableBoundary (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  let some reducers := (Array.range 3472).mapM fun i => SparseRow.ofEntries field 4559
      (#[ (i,(1:UInt64)) ] ++ if i < 616 then
        (Array.range 73).map (fun j => (4486+j,(1:UInt64))) else #[]) | return false
  let some full := SparseRow.ofEntries field 4559 ((Array.range 4559).map (·,(1:UInt64))) | return false
  let some fragment := SparseRow.ofEntries field 4559 ((Array.range 986).map (·,(1:UInt64))) | return false
  let targets := (Array.replicate 810 ({} : SparseRow)).mapIdx fun i empty =>
    if i < 185 then full else if i == 185 then fragment else empty
  if Elimination.binaryGroups 4559 reducers != 154 ||
      Elimination.binaryCost 4559 reducers targets 892841 != 2^28-2 then return false
  let sugars := (Array.range (3472+810)).map (fun i => seed+i%7)
  let some expected := Elimination.attemptPortable field limits 4559 reducers targets sugars false | return false
  let some actual := Elimination.attempt field limits 4559 reducers targets sugars false | return false
  if !same actual expected then return false
  let some extra := SparseRow.ofEntries field 4559 ((Array.range 987).map (·,(1:UInt64))) | return false
  let rejected := targets.set! 185 extra
  if Elimination.binaryCost 4559 reducers rejected 892842 != 2^28+1 then return false
  return (Elimination.attemptPortable field limits 4559 reducers rejected sugars false).isNone &&
    (Elimination.attempt field limits 4559 reducers rejected sugars false).isNone

@[noinline] private def binaryWorkRows (nonce : Nat) : Option (Array SparseRow) :=
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let tail := 1024+nonce%7
  (Array.range 1024).mapM fun i =>
    SparseRow.ofEntries field 2055 (#[ (i,(1:UInt64)) ] ++
      (Array.range 1024).map fun j => (tail+j,(1:UInt64)))

/-- Expanded shape caps and adjacent sides of the physical-work guard, plus
malformed rows and arbitrary natural-number limits in the packed F2 route. -/
def binaryBounds : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let limits : MatrixLimits := { binaryPivots := true }
  let empty : SparseRow := {}
  let reducers := Array.replicate 16384 empty
  let targets := Array.replicate 61 empty
  if Elimination.binaryBound 16384 16384 61 0 > 2^28 ||
      Elimination.binaryBound 16384 16384 62 0 <= 2^28 then return false
  let some expected := Elimination.attemptPortable field limits 16384 reducers targets #[] false | return false
  let some actual := Elimination.attempt field limits 16384 reducers targets #[] false | return false
  if !same actual expected then return false
  for (columns,rs,ts) in [(16385,#[],#[]),(1,Array.replicate 16385 empty,#[]),
      (1,#[],Array.replicate 1025 empty),(16384,reducers,targets.push empty),
      (16384,reducers,Array.replicate 1024 empty)] do
    if (Elimination.attempt field limits columns rs ts #[] false).isSome ||
        (Elimination.attemptPortable field limits columns rs ts #[] false).isSome then return false
  let some row := SparseRow.ofEntries field 3 #[(0,1),(2,1)] | return false
  let malformed : Array SparseRow := #[
    { row with columns := row.columns.push 0 },
    { row with coefficients := row.coefficients.push 0 },
    { row with coefficients := Packed.set .u8 row.coefficients 0 0 },
    { row with coefficients := Packed.set .u8 row.coefficients 0 2 },
    { row with columns := Packed.set .u32 row.columns 1 3 },
    { row with columns := Packed.set .u32 row.columns 1 0 }]
  for bad in malformed do
    for (rs,ts) in [(#[bad],#[row]),(#[row],#[bad])] do
      if !sameAttempt (Elimination.attempt field limits 3 rs ts #[] false)
          (Elimination.attemptPortable field limits 3 rs ts #[] false) then return false
  for amount in [0,1,15,16,31,32,63,64,2^90] do
    for cap in ([{ limits with packedBytes := amount },{ limits with work := amount },
        { limits with inputEntries := amount },{ limits with outputEntries := amount }] : List MatrixLimits) do
      if !sameAttempt (Elimination.attempt field cap 3 #[row] #[row] #[] false)
          (Elimination.attemptPortable field cap 3 #[row] #[row] #[] false) then return false
  return true

/-- A successful F2 frame with actual charged work above the old quantum and
an aliased target reduced by a packed known pivot. Runs in compiled conformance. -/
def binaryWorkChecks (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  if !binaryBounds then return false
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let some er := binaryWorkRows (seed+7) | return false
  let some ar := binaryWorkRows seed | return false
  let limits : MatrixLimits := { binaryPivots := true }
  let some expected := Elimination.attemptPortable field limits 2055 er #[er[1023]!] #[] false | return false
  let some actual := Elimination.attempt field limits 2055 ar #[ar[1023]!] #[] false | return false
  return expected.stats.work > 2^20 && same actual expected && sameRows ar er

@[noinline] private def binaryRows (columns nonce : Nat) :
    Option (Array SparseRow × Array SparseRow) := do
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let value : UInt64 := 1
  let salt := nonce%7
  let support := Array.range columns
  let r0 ← SparseRow.ofEntries field columns ((support.filter (fun i => (i+salt)%2 == 0)).map (·,value))
  let r1 ← SparseRow.ofEntries field columns ((support.filter (fun i => (i+salt)%2 == 1)).map (·,value))
  let both ← SparseRow.ofEntries field columns (support.map (·,value))
  let tail ← SparseRow.ofEntries field columns ((support.filter (fun i => (i+salt)%3 == 2)).map (·,value))
  return (#[r0,r1],#[both,tail,tail])

/-- Byte/word boundaries, zero rows, nonzero target installation, shared inputs,
independent targets and near-success parent budget refusals over ordinary F2. -/
def binaryChecks (seed : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  for columns in [1,2,7,8,9,63,64,65,127,128,129,257,4096] do
    for independent in [false,true] do
      let some (er,et) := binaryRows columns (seed+7) | return false
      let some expected := Elimination.attemptPortable field { binaryPivots := true } columns er et #[1,2,3,4,5] independent
        | return false
      let some (ar,actualTargets) := binaryRows columns seed | return false
      let some actual := Elimination.attempt field { binaryPivots := true } columns ar actualTargets #[1,2,3,4,5] independent
        | return false
      if !same actual expected || !sameRows ar er || !sameRows actualTargets et then return false
      let scratch := Elimination.binaryBytes columns er.size et.size
      let tight : MatrixLimits := { binaryPivots := true,packedBytes := expected.stats.packedBytes+scratch }
      if !(Elimination.attempt field tight columns ar actualTargets #[1,2,3,4,5] independent).isSome then return false
      for limits in ([{ binaryPivots := true,work := expected.stats.work-1 },
          { binaryPivots := true,packedBytes := expected.stats.packedBytes+scratch-1 },
          { binaryPivots := true,outputEntries := expected.stats.outputEntries-1 }] : List MatrixLimits) do
        if !sameAttempt (Elimination.attempt field limits columns ar actualTargets #[1,2,3,4,5] independent)
            (Elimination.attemptPortable field limits columns er et #[1,2,3,4,5] independent) then return false
  return true

#guard binaryChecks 0

/-- Complete F4 forwards the policy into real native pair matrices. Dynamic
input degrees prevent compile-time reuse of this ownership/counter window. -/
def binaryFresh (seed : Nat) : Bool := Id.run do
  let field : PrimeField := ⟨2,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let context : Context := ⟨field,2,.grevlex⟩
  let generators : Array RawPolynomial := #[
    #[⟨#[2+seed%7,0],1⟩,⟨#[0,1],1⟩],#[⟨#[1,1],1⟩,⟨#[0,0],1⟩]]
  let .candidate actual stats := computeWith context { binaryPivots := true } generators | return false
  let .candidate expected reference := computeWith context
    { binaryPivots := true,nativeRows := false,nativeMonomials := false } generators | return false
  return actual.polynomials == expected.polynomials && stats == reference

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
