/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Input
import Lean.Data.Json

namespace Hex.SignDetBench
open Hex.SignDet
open scoped Hex

/-- Both comparison arms receive the same prepared domain and ordered queries.
Exact agreement with the known two-root table is checked outside timing. -/
def smallInput (s : Nat) : Input :=
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let p := x * x - 1
  let qs := List.replicate s x
  match Sturm.prepare Sturm.orderSign p .negInf .posInf with
  | none => ⟨p, qs, none, none, none⟩
  | some domain =>
    match buildPrepared (10377 : Nat) domain qs false, referencePrepared (10377 : Nat) domain qs with
    | .ok reduced, .ok full =>
      let expected := if s == 0 then [([], (2 : Int))]
        else [(List.replicate s (-1), (1 : Int)), (List.replicate s 1, 1)]
      if entries reduced.val.node.system == expected && entries full.system == expected &&
          full.check Sturm.orderSign 10377 p .negInf .posInf qs then
        ⟨p, qs, some domain, some reduced.val, none⟩
      else ⟨p, qs, none, none, none⟩
    | _, _ => ⟨p, qs, none, none, none⟩

/-- Construct and replay a reduced-support table. The `false` flag disables
query-polynomial reduction, not BKR support reduction. -/
@[noinline] def runSmallReduced (i : Input) : Option UInt64 := do
  let domain ← i.domain
  match buildPrepared (10377 : Nat) domain i.queries false with
  | .error _ => none
  | .ok tree => some (hash (entries tree.val.node.system))

/-- Construct and replay the complete ternary table over the same prepared
domain, with query-polynomial reduction likewise disabled. -/
@[noinline] def runSmallFull (i : Input) : Option UInt64 := do
  let domain ← i.domain
  match referencePrepared (10377 : Nat) domain i.queries with
  | .error _ => none
  | .ok node =>
    if node.check Sturm.orderSign 10377 i.head .negInf .posInf i.queries then
      some (hash (entries node.system))
    else none

private def bits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1

/-- Literal counts, dimensions and stored inverse bits are checked independently
of the timed hashes. They do not measure peak intermediate arithmetic bits. -/
def inspectSmall : IO UInt32 := do
  for s in #[1, 2, 3, 4, 5] do
    let i := smallInput s
    let some domain := i.domain | throw (IO.userError "invalid comparison input")
    let some tree := i.tree | throw (IO.userError "missing reduced tree")
    let .ok full := referencePrepared (10377 : Nat) domain i.queries
      | throw (IO.userError "full reference failed")
    let expected := [(List.replicate s (-1 : Int), (1 : Int)), (List.replicate s (1 : Int), 1)]
    let ns := nodes tree
    let queryCount := ns.foldl (fun k n => k + n.size) 0
    let maxSize := ns.foldl (fun k n => max k n.size) 0
    let inverseBits := full.system.inverse.rows.toArray.foldl (fun k row =>
      row.toArray.foldl (fun k z => max k (bits z)) k) 0
    unless full.size == 3^s && queryCount == 7*s-4 && maxSize ≤ 4 &&
        entries tree.node.system == expected && entries full.system == expected &&
        full.system.denominator.natAbs == 2^s && inverseBits ≤ s+1 do
      throw (IO.userError s!"comparison inventory failed at {s}")
    IO.println <| (Lean.Json.mkObj [
      ("queries", Lean.toJson s), ("headDegree", Lean.toJson i.head.natDegree),
      ("queryDegree", Lean.toJson (1 : Nat)), ("rootCount", Lean.toJson (2 : Nat)),
      ("reducedQueries", Lean.toJson queryCount), ("fullQueries", Lean.toJson full.size),
      ("maxReducedMatrixSize", Lean.toJson maxSize),
      ("fullMatrixSize", Lean.toJson full.size),
      ("fullInverseBits", Lean.toJson inverseBits),
      ("fullDenominatorBits", Lean.toJson (bits full.system.denominator)),
      ("inputHash", Lean.toJson (hash i).toNat),
      ("resultHash", Lean.toJson (hash (some (hash expected))).toNat)]).compress
  return 0

/-- Observe the actual full-system elimination one column at a time. The checked
nonzero diagonal means pivot search selects the current row without swapping.
Other rows retain their column entry until their own elimination, so counting
those nonzero entries counts the actual `eliminateColumn` updates. This is an
untimed finite-input inventory, not a general operation-count theorem. -/
def inspectFull : IO UInt32 := do
  for s in #[1, 2, 3, 4, 5] do
    let r := 3^s
    let rows := (words [0, 1, 2] s).toArray
    let cols := (words [-1, 0, 1] s).toArray
    unless rows.size == r && cols.size == r do
      throw (IO.userError "incorrect full matrix dimensions")
    let m : Matrix Rat r r := Matrix.ofFn fun i j => (entry rows[i.val]! cols[j.val]! : Rat)
    let mut state : Matrix.RowReduceState Rat r r := ⟨0, m, Matrix.identity r, []⟩
    let mut updates := 0
    let mut columns : Array Nat := #[]
    for col in List.finRange r do
      unless state.row == col.val && state.echelon[(col, col)] != 0 do
        throw (IO.userError s!"unexpected pivot at {s}/{col.val}")
      let count := (List.finRange r).countP fun row =>
        row != col && state.echelon[(row, col)] != 0
      updates := updates + count
      columns := columns.push count
      state := Matrix.rowReduceLoop col.val 1 state
    let some inv := Matrix.inverse? m | throw (IO.userError "full inverse failed")
    unless state.row == r && state.pivots == List.finRange r &&
        state.echelon == Matrix.identity r && state.transform == inv do
      throw (IO.userError s!"one-column traversal differs from full inverse at {s}")
    IO.println <| (Lean.Json.mkObj [
      ("queries", Lean.toJson s), ("matrixSize", Lean.toJson r),
      ("eliminatedRows", Lean.toJson updates), ("updatesPerColumn", Lean.toJson columns),
      ("rowAddCalls", Lean.toJson (2 * updates)),
      ("rowAddScalarPairs", Lean.toJson (2 * updates * r)),
      ("rowScaleScalarProducts", Lean.toJson (2 * r * r)),
      ("inverseIdentityScalarPairs", Lean.toJson (r * r * r)),
      ("matchesInverse", Lean.toJson true)]).compress
  return 0

end Hex.SignDetBench
