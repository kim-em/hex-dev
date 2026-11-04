/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.FieldIndex
public import HexRCF.RealCoefficients.FieldCells
public section

namespace Hex.RCF.RealCoefficients
open Hex
variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
local notation "E" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

namespace Field

/-- Authentication makes even duplicate recorded hits agree. Untrusted routing
therefore preserves exact optional lookup, including missing entries. -/
theorem lookupIndex_eq (table : LiteralSign.Table E) (compare : E → E → Ordering)
    (index : LiteralSign.Index) (checked : checkSignTable p s hw hp table = true) (a : E) :
    table.lookupIndex compare index a = table.lookup? a := by
  cases routed : index.lookup table.entries.toArray compare a with
  | none => simp only [LiteralSign.Table.lookupIndex, routed]
  | some observed =>
    cases linear : table.lookup? a with
    | none =>
      exfalso
      obtain ⟨entry, member, same, _⟩ := index.lookup_entry
        table.entries.toArray compare a observed routed
      have member : entry ∈ table.entries := by simpa using member
      have absent : table.entries.find? (fun entry => Decidable.decide (entry.key = a)) = none := by
        unfold LiteralSign.Table.lookup? at linear
        cases found : table.entries.find? (fun entry => Decidable.decide (entry.key = a)) with
        | none => rfl
        | some chosen => simp [found] at linear
      have impossible := List.find?_eq_none.mp absent entry member
      simp [same] at impossible
    | some expected =>
      have indexed := checkSignTable_index p s hw hp table compare index checked a
      simp only [LiteralSign.Table.signIndex, LiteralSign.Table.lookupIndex, routed] at indexed
      have ordinary := checkSignTable_lookup p s hw hp table checked a expected linear
      have same : observed = expected := indexed.trans ordinary.symm
      simp only [LiteralSign.Table.lookupIndex, routed, same]

end Field

namespace FieldQuery

/-- Checked routing preserves the exact executable sign function. -/
theorem cachedIndex_eq (table : LiteralSign.Table E) (compare : E → E → Ordering)
    (index : LiteralSign.Index) (checked : Field.checkSignTable p s hw hp table = true) :
    cachedWith (table.lookupIndex compare index) = cached table := by
  have same : table.lookupIndex compare index = table.lookup? :=
    funext (Field.lookupIndex_eq table compare index checked)
  rw [same]
  rfl

end FieldQuery
namespace FieldCells
variable {Ctx : Type u} [DecidableEq Ctx] {n : Nat}

/-- The original finite envelope with indexed retrieval for every sign read.
The sign data and full original row inventory are still authenticated. -/
@[expose] def checkIndex (signs : LiteralSign.Table E) (compare : E → E → Ordering)
    (index : LiteralSign.Index) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : RealFormula.QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : Bool :=
  checkWith signs (signs.lookupIndex compare index) context query formula radical cert rows

/-- Indexing preserves the full Boolean result for every supplied packet,
including malformed headers, routes, missing signs and corrupt evidence. -/
theorem checkIndex_eq (signs : LiteralSign.Table E) (compare : E → E → Ordering)
    (index : LiteralSign.Index) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : RealFormula.QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) :
    checkIndex signs compare index context query formula radical cert rows =
      check signs context query formula radical cert rows := by
  cases header : Field.checkSignTable p s hw hp signs with
  | false => simp only [checkIndex, check, checkWith, header, Bool.false_and]
  | true =>
    have same : signs.lookupIndex compare index = signs.lookup? :=
      funext (Field.lookupIndex_eq signs compare index header)
    simp only [checkIndex, check, same]

end FieldCells
end Hex.RCF.RealCoefficients
