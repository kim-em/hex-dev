/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner.Fixtures

/-!
Oracle: independent Python modular RREF and derivation replay.
Mode: always (no optional dependencies).
Covered operations: packed read/write, canonical sparse construction,
deterministic Macaulay elimination with and without provenance.
Covered properties: monic echelon shape, reducer/target rank split, canonical
residues, packed widths, shared budgets and exact boundary acceptance.
Covered edge cases: empty matrices, zero columns/rows, rank defects, later
reducer pivots, characteristic two, 8/16/32-bit boundaries, maximal prime,
malformed lengths/columns/residues, every exhaustion category.
-/

namespace Hex.Groebner.Conformance
open Fixtures

private def field : PrimeField := ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩

local instance : ZMod64.PrimeModulus 2 := ⟨Hex.Nat.isPrimeTrial_isPrime (by decide)⟩
#guard (PrimeField.ofZMod64 2).modulus == 2

private def typical : Case :=
  ⟨"typical", 3, #[#[0, 2, 2]], #[#[2, 2, 0], #[0, 0, 0], #[0, 4, 4]]⟩

private def shape (field : PrimeField) (e : Echelon) : Bool := Id.run do
  let mut previous : Option Nat := none
  for pivot in e.rows do
    let entries := pivot.row.entries field
    if entries.isEmpty || entries[0]!.2 != 1 then return false
    let column := entries[0]!.1
    if let some p := previous then
      if column ≤ p then return false
    previous := some column
    if entries.any (fun (_, c) => c == 0 || c ≥ field.modulus) then return false
  return e.reducerRank == (e.rows.filter (!·.fromTarget)).size

#guard fields.map (·.width) == #[.u8, .u8, .u8, .u16, .u16, .u32, .u32]

#guard (SparseRow.ofEntries field 4 #[(0, 3), (3, 6)]).map (·.entries field) ==
  some #[(0, 3), (3, 6)]
#guard (SparseRow.ofEntries field 0 #[]).isSome
#guard (SparseRow.ofEntries field (2 ^ 32) #[]).isNone
#guard (SparseRow.ofEntries field 4 #[(1, 0)]).isNone
#guard (SparseRow.ofEntries field 4 #[(1, 7)]).isNone
#guard (SparseRow.ofEntries field 4 #[(4, 1)]).isNone
#guard (SparseRow.ofEntries field 4 #[(2, 1), (2, 3)]).isNone
#guard (SparseRow.ofEntries field 4 #[(2, 1), (1, 3)]).isNone

#guard (Packed.read .u32 (Packed.push .u32 {} 4294967295) 0).toNat == 4294967295
#guard (Packed.read .u16 (Packed.set .u16 (Packed.push .u16 {} 65535) 0 256) 0) == 256
-- Downstream ordinary-kernel evaluation of the literal byte encoding.
/-- Literal storage decoding reduces in the ordinary downstream kernel. -/
theorem decode_literal :
    (Packed.read .u16 (Packed.push .u16 {} 65535) 0).toNat = 65535 := by decide

/-- info: 'Hex.Groebner.Conformance.decode_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decode_literal

private def summary : Except String (Array (Array (Nat × UInt64)) × Nat × Nat) := do
  let r ← run field typical
  match r.result with
  | .error e => throw (reprStr e)
  | .ok e => pure (e.rows.map (·.row.entries field), e.reducerRank, r.stats.zeroRows)

/-- info: Except.ok (#[#[(0, 1), (2, 6)], #[(1, 1), (2, 1)]], 1, 2) -/
#guard_msgs in #eval summary

#guard fields.all fun field => (cases field).all fun c =>
  match run field c with
  | .ok ⟨.ok e, _⟩ => shape field e
  | _ => false

#guard (match run field typical {} false, run field typical {} true with
  | .ok ⟨.ok a, sa⟩, .ok ⟨.ok b, sb⟩ =>
    a.rows.map (·.row.entries field) == b.rows.map (·.row.entries field) &&
      a.trace.isEmpty && sa.traceNodes == 0 && b.trace.size == sb.traceNodes
  | _, _ => false)

private def fails (limits : MatrixLimits) (resource : Resource) : Bool :=
  match run field typical limits with
  | .ok r => match r.result with
    | .error e => e == .exhausted resource
    | _ => false
  | _ => false

#guard fails { columns := 2 } .columns
#guard fails { rows := 3 } .rows
#guard fails { inputEntries := 1 } .inputEntries
#guard fails { outputEntries := 1 } .outputEntries
#guard fails { packedBytes := 1 } .packedBytes
#guard fails { work := 0 } .work
#guard fails { traceNodes := 0 } .traceNodes

-- Inclusive boundaries, also ensuring nested inversion and validation work
-- contribute to the same counters as the outer call.
#guard match run field typical with
  | .ok r =>
    let s := r.stats
    let limits : MatrixLimits := {
      work := s.work, packedBytes := s.packedBytes
      inputEntries := s.inputEntries, outputEntries := s.outputEntries
      traceNodes := s.traceNodes }
    match run field typical limits with
    | .ok ⟨.ok _, t⟩ => t.work == s.work &&
      fails { limits with work := s.work - 1 } .work &&
      fails { limits with packedBytes := s.packedBytes - 1 } .packedBytes &&
      fails { limits with traceNodes := s.traceNodes - 1 } .traceNodes
    | _ => false
  | _ => false

private def rejects (row : SparseRow) (error : MatrixError) : Bool :=
  match (eliminateWith field {} 3 #[] #[row]).result with
  | .error e => e == error
  | _ => false

#guard rejects ⟨ByteArray.empty.push 0, {}⟩ (.rowLength 0)
#guard rejects ⟨Packed.push .u32 {} 0, {}⟩ (.rowLength 0)
#guard rejects ⟨Packed.push .u32 {} 3, ByteArray.empty.push 1⟩ (.column 0 0)
#guard rejects ⟨Packed.push .u32 {} 0, ByteArray.empty.push 0⟩ (.coefficient 0 0)
#guard rejects ⟨Packed.push .u32 {} 0, ByteArray.empty.push 7⟩ (.coefficient 0 0)
#guard rejects ⟨Packed.push .u32 (Packed.push .u32 {} 1) 1,
  (ByteArray.empty.push 1).push 2⟩ (.column 0 1)
#guard match (eliminateWith field {} (2 ^ 32) #[] #[]).result with
  | .error e => e == .dimensions
  | _ => false

end Hex.Groebner.Conformance
