/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

-- The dispatcher owns the provenance/scalar calls into the carrier implementation.
import all HexGroebner.EliminationKernel
public import HexGroebner.EliminationKernel
import HexGroebner.MatrixState
import HexGroebner.EliminationProof

public section

namespace Hex.Groebner

namespace Elimination

/-- Select bounded bulk elimination for untraced native calls. Declined frames
continue in owned bounded phases with the reference result and exact counters. -/
def run (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (provenance : Bool) (sugars : Array Nat)
    (native independent : Bool) : Result :=
  if native && !provenance then
    match attempt field limits columns reducers targets sugars independent with
    | some result => result
    | none =>
      let output := MatrixState.finishWith 64 (MatrixState.start field limits columns reducers targets sugars independent)
      ⟨output.1,output.2⟩
  else
    let (result,stats) :=
      (eliminate field limits columns reducers targets provenance sugars native independent).run {}
    ⟨result,stats⟩

/-- The optimized untraced route has exactly the deterministic reference result. -/
theorem run_spec (field : PrimeField) (limits : MatrixLimits) (columns : Nat)
    (reducers targets : Array SparseRow) (sugars : Array Nat) (independent : Bool) :
    run field limits columns reducers targets false sugars true independent =
      reference field limits columns reducers targets sugars independent := by
  unfold run attempt
  simp only [MatrixState.finish_reference]
  change (match attemptPortable field limits columns reducers targets sugars independent with
    | some result => result
    | none => reference field limits columns reducers targets sugars independent) = _
  have h := attemptPortable_spec field limits columns reducers targets sugars independent
  cases hx : attemptPortable field limits columns reducers targets sugars independent with
  | none => rfl
  | some result => simpa only [hx, Option.getD_some] using h

/-- info: 'Hex.Groebner.Elimination.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_spec

end Elimination

/-- Deterministic finite-prime-field Macaulay elimination, with sparse reducers,
packed dense accumulation, monic output, stable columns and optional provenance.
`native := false` retains scalar Lean updates; the default uses bounded native
chunks with identical rows, provenance and counters. Untraced native 64-bit calls first
try a complete frame bounded by 4096 columns, 1024 reducers, 64 targets and
`2^20` work, then continue in bounded native phases when that frame declines.
Cancellation is observed between calls. Input rows must be canonical
and use the field's coefficient width. Limits cover
validation and nested arithmetic as well as elimination. Successful rows span
the input row space; they are echelon, not reduced echelon. The polynomial layer
is responsible for supplying columns in the chosen lawful monomial order. -/
def eliminateWith (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (provenance : Bool := false)
    (sugars : Array Nat := #[]) (native : Bool := true) : MatrixResult :=
  let output := Elimination.run field limits columns reducers targets provenance sugars native false
  ⟨output.result.map Prod.fst, output.stats⟩

/-- Reduce each target by the same reducer echelon space, preserving its scalar
and input position. Targets never reduce each other. Validation, sparse reducer
installation, bounded native updates and allowances are shared with elimination.
Untraced native 64-bit calls use the same optional `2^20`-work matrix frame and shape
caps as `eliminateWith`; other untraced native calls use bounded continuation
phases. Provenance calls retain the reference scan/gather chunks.
`native := false` uses scalar Lean operations.
This is a linear triangular solve; polynomial normal-form claims additionally
require the symbolic closure and a Gröbner basis. -/
def reduceRowsWith (field : PrimeField) (limits : MatrixLimits)
    (columns : Nat) (reducers targets : Array SparseRow) (provenance : Bool := false)
    (sugars : Array Nat := #[]) (native : Bool := true) : RemainderResult :=
  let output := Elimination.run field limits columns reducers targets provenance sugars native true
  ⟨output.result.map (fun (e, rows) => ⟨rows, e.trace⟩), output.stats⟩

end Hex.Groebner
