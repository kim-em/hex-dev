/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGroebner.Elimination
import HexGroebner.Fixtures

namespace Hex.Groebner.DelayedConformance

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

/-- Different nonces allocate independent, equal packed rows. Empty rows,
nonmonic reducers, duplicate targets and high coefficients exercise reset and
normalization. The final sparse tail also extends the scan beyond its input. -/
@[noinline] private def rows (field : PrimeField) (columns nonce : Nat) :
    Option (Array SparseRow × Array SparseRow) := do
  let salt := nonce%7
  let p := field.modulus.toNat
  let mut reducers := #[]
  for h in [:min 5 columns] do
    let mut entries := #[(h,(p-1).toUInt64)]
    for j in [h+1:columns] do
      if (j+salt+h)%3 == 0 || j+1 == columns then
        entries := entries.push (j,((j+salt)%(p-1)+1).toUInt64)
    reducers := reducers.push (← SparseRow.ofEntries field columns entries)
  let mut targets := #[]
  for t in [:8] do
    let mut entries := #[]
    if t%4 != 0 then
      for j in [:columns] do
        if (j+t+salt)%4 == 0 then entries := entries.push (j,(p-1).toUInt64)
    targets := targets.push (← SparseRow.ofEntries field columns entries)
  let empty ← SparseRow.ofEntries field columns #[]
  return (reducers,targets ++ #[targets[1]!,empty,targets[1]!])

/-- Native admission, complete result and immutable inputs agree with the
portable provider actualTargets every coefficient width and neighboring budget cuts. -/
def runtimeChecks (nonce : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let nonce := nonce%2^32
  for field in Fixtures.fields do
    for columns in [0,1,5,17,63,64,65,127,257] do
      let some (er,et) := rows field columns (nonce+7) | return false
      let some (ar,actualTargets) := rows field columns nonce | return false
      let sugars := (Array.range (er.size+et.size)).map (fun i => (i*13+nonce)%97)
      for independent in [false,true] do
        let limits : MatrixLimits := { delayedReduction := true }
        let some expected := Elimination.attemptPortable field limits columns er et sugars independent
          | return false
        let some actual := Elimination.attempt field limits columns ar actualTargets sugars independent
          | return false
        if !same actual expected then return false
        if !((ar.zip er).all fun (a,b) => a.columns == b.columns && a.coefficients == b.coefficients) ||
            !((actualTargets.zip et).all fun (a,b) => a.columns == b.columns && a.coefficients == b.coefficients) then
          return false
        let scratch := if Elimination.delayedEnabled field limits then
          Elimination.delayedBytes field columns er.size et.size else 0
        let bytes := expected.stats.packedBytes+scratch
        let tight : MatrixLimits := { limits with packedBytes := bytes,work := expected.stats.work }
        if !(Elimination.attempt field tight columns ar actualTargets sugars independent).isSome then return false
        for budget in ([{ tight with work := expected.stats.work-1 },
            { tight with packedBytes := bytes-1 },
            { tight with outputEntries := expected.stats.outputEntries-1 },
            { tight with inputEntries := expected.stats.inputEntries-1 }] : List MatrixLimits) do
          if !sameAttempt (Elimination.attempt field budget columns ar actualTargets sugars independent)
              (Elimination.attemptPortable field budget columns er et sugars independent) then return false
  return true

/-- Sparse high columns cross the ordinary frame ceilings without allocating
a dense set of input entries. Independent mode retains each target's scalar. -/
def boundaryChecks (nonce : Nat) : Bool := Id.run do
  if USize.size != 2^64 then return true
  let field : PrimeField := ⟨65521,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  for columns in [4097,65536,131071,131072] do
    let some r := SparseRow.ofEntries field columns #[(0,65520),(columns-1,65520)] | return false
    let some t := SparseRow.ofEntries field columns #[(0,(nonce%65520+1).toUInt64)] | return false
    let limits : MatrixLimits := { delayedReduction := true,work := 2^40,packedBytes := 2^30 }
    for independent in [false,true] do
      let some actual := Elimination.attempt field limits columns #[r] #[t,t] #[7,3,9] independent
        | return false
      let expected := Elimination.reference field limits columns #[r] #[t,t] #[7,3,9] independent
      if !same actual expected then return false
  return true

/-- The F4 producer forwards the option while retaining exact scalar behavior. -/
def producerChecks (nonce : Nat) : Bool := Id.run do
  let field : PrimeField := ⟨251,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let context : Context := ⟨field,2,.grevlex⟩
  let generators : Array RawPolynomial := #[
    #[⟨#[2+nonce%7,0],250⟩,⟨#[0,1],1⟩],#[⟨#[1,1],249⟩,⟨#[0,0],1⟩]]
  let .candidate actual stats := computeWith context { delayedReduction := true } generators | return false
  let .candidate expected reference := computeWith context
    { delayedReduction := true,nativeRows := false,nativeMonomials := false } generators | return false
  return actual.polynomials == expected.polynomials && stats == reference


/-- Newly admitted reducer/target counts exercise real reductions. The optional
cap models the harness's smaller native work ceiling at its exact boundary. -/
def wideChecks (nonce : Nat) (cap : Nat := 2^34) : Option Nat := do
  let field : PrimeField := ⟨65521,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let columns := 2305
  let reducers ← (Array.range 1100).mapM fun h =>
    SparseRow.ofEntries field columns #[(h,65520),(columns-1,65520)]
  let target ← SparseRow.ofEntries field columns
    (((Array.range 1100).map fun h => (h,(65520:UInt64))).push (columns-1,65520))
  let targets := Array.replicate 80 target
  let sugars := (Array.range 1180).map fun i => (i+nonce%17)%101
  let limits : MatrixLimits := { delayedReduction := true }
  let mut work := 0
  for independent in [false,true] do
    let expected ← Elimination.attemptPortable field limits columns reducers targets sugars independent
    let actual := Elimination.attempt field limits columns reducers targets sugars independent
    if !sameAttempt actual (if expected.stats.work ≤ cap then some expected else none) then failure
    work := max work expected.stats.work
  return work

/-- Small delayed matrices also agree directly with fully scalar Lean updates,
including every joint-elimination row, label, alias and logical counter. -/
def scalarChecks (nonce : Nat) : Bool := Id.run do
  for field in Fixtures.fields do
    if field.modulus > 2 && field.modulus < 65536 then
      for columns in [1,5,17,65] do
        let some (rs,ts) := rows field columns nonce | return false
        let limits : MatrixLimits := { delayedReduction := true }
        let sugars := (Array.range (rs.size+ts.size)).map (·+nonce%97)
        let actual := Elimination.run field limits columns rs ts false sugars true false
        let expected := eliminateWith field limits columns rs ts false sugars false
        if !same actual ⟨expected.result.map (fun e => (e,#[])),expected.stats⟩ then return false
  return true

end Hex.Groebner.DelayedConformance
