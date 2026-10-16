/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CompleteReplay
public import HexRCF.RealCoefficients.CellPacketTransport
public import HexRealClosure.RecordReaders
public section

/-! Complete replay using the owners' equal supplied arithmetic operations.
The dictionary changes computation, while all checked results retain canonical
source/root indices. No native producer is invoked. Source authentication and
strict compiled missing-record rejection remain separate obligations. -/
namespace Hex.RCF.RealCoefficients.CellOperations
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Specialize using the supplied arithmetic, retaining canonical coefficient storage. -/
@[expose] def prepare (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) : List parent.Poly :=
  @RepresentationSpecialize.prepare parent.Value (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) operations.one operations.add operations.mul
    operations.neg operations.natCast n values formula

theorem prepare_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) :
    prepare operations values formula = RepresentationSpecialize.prepare values formula := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    rfl

/-- Validate the original product/radical identities with supplied operations. -/
@[expose] def radical (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (cert : RadicalCert parent.Value Signature) : Bool :=
  let product := @RepresentationCarrier.product parent.Value (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) operations.one operations.add operations.mul
    (prepare operations values formula)
  @RadicalCert.check parent.Value Signature (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) operations.one operations.add operations.sub operations.mul
    inferInstance parent.signature product cert

theorem radical_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (cert : RadicalCert parent.Value Signature) :
    radical operations values formula cert = cert.check parent.signature
      (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    rfl

abbrev descriptor (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (original : Descriptor parent.Value Signature parent.sign parent.signature) :=
  @Descriptor.changeOps parent.Value Signature (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) inferInstance operations.one operations.add
    operations.sub operations.mul operations.natCast
    (Tower.instOneValue parent) (Tower.instAddValue parent)
    (Tower.instSubValue parent) (Tower.instMulValue parent) (Tower.instNatCastValue parent)
    operations.one_eq.symm operations.add_eq.symm operations.sub_eq.symm
    operations.mul_eq.symm operations.natCast_eq.symm parent.sign parent.signature original

abbrev Signs (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (original : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List parent.Poly) :=
  @SelectedSigns parent.Value Signature (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) operations.one operations.add operations.sub
    operations.mul operations.natCast inferInstance parent.sign parent.signature
    (descriptor operations original) queries

/-- Return checked row data to the original descriptor without changing its values or evidence. -/
@[expose] def restore (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (original : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List parent.Poly) (source : Signs operations original queries) :
    SelectedSigns original queries :=
  let restored := RowOperations.changeOps operations.one operations.add operations.sub
    operations.mul operations.natCast operations.one_eq operations.add_eq operations.sub_eq
    operations.mul_eq operations.natCast_eq parent.sign parent.signature
    (descriptor operations original) queries source
  have same : Descriptor.changeOps operations.one operations.add operations.sub
      operations.mul operations.natCast operations.one_eq operations.add_eq operations.sub_eq
      operations.mul_eq operations.natCast_eq parent.sign parent.signature
      (descriptor operations original) = original := by
    cases operations with
    | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
      cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
      simp only [descriptor, Descriptor.changeOps_self]
  RowOperations.retarget parent.sign parent.signature same rfl restored

/-- Read one original-descriptor row with supplied arithmetic after original guard preflight. -/
@[expose] def row (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (original : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List parent.Poly) (packet : Codec.Json) :
    Except Replay.Error (SelectedSigns original queries) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let source ← @RowOperations.read parent.Value Signature (Tower.instZeroValue parent)
      (Tower.instDecidableEqValue parent) inferInstance operations.one operations.add
      operations.sub operations.mul operations.natCast value Signature.codec parent.sign parent.signature
      (descriptor operations original) queries packet
  return restore operations original queries source

private abbrev ordinary : Hex.RealClosure.Replay.Operations parent.sign :=
  ⟨Tower.instOneValue parent, Tower.instAddValue parent, Tower.instNegValue parent,
    Tower.instSubValue parent, Tower.instMulValue parent, Tower.instInvValue parent,
    Tower.instDivValue parent, Tower.instNatCastValue parent,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, parent.sign, rfl⟩

theorem row_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (original : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List parent.Poly) (packet : Codec.Json) :
    row operations value guards original queries packet = RowReplay.read value guards original queries packet := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc; cases hsign
    change row ordinary value guards original queries packet = _
    unfold row RowReplay.read
    split
    · exact RowOperations.retarget_read value Signature.codec parent.sign parent.signature
        (Descriptor.changeOps_self parent.sign parent.signature original) rfl packet
    · rfl
end Hex.RCF.RealCoefficients.CellOperations


namespace Hex.RCF.RealCoefficients.CellOperations
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Construct the boundary comparison polynomial using the supplied operations. -/
@[expose] def pointQuery (operations : Hex.RealClosure.Replay.Operations parent.sign) (point : parent.Value) :=
  @Isolation.pointQuery parent.Value (Tower.instZeroValue parent)
    (Tower.instDecidableEqValue parent) operations.one operations.sub point

theorem pointQuery_eq (operations : Hex.RealClosure.Replay.Operations parent.sign) (point : parent.Value) :
    pointQuery operations point = Isolation.pointQuery point := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    rfl

/-- Read boundary signs and retain the canonical point-query index. -/
@[expose] def pointRow (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (point : parent.Value) (packet : Codec.Json) :
    Except Replay.Error (SelectedSigns root [Isolation.pointQuery point]) := do
  let source ← row operations value [] root [pointQuery operations point] packet
  return RowOperations.retarget parent.sign parent.signature rfl
    (congrArg List.singleton (pointQuery_eq operations point)) source

theorem pointRow_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (point : parent.Value) (packet : Codec.Json) :
    pointRow operations value root point packet =
      RowOperations.read value Signature.codec parent.sign parent.signature root [Isolation.pointQuery point] packet := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    simp only [pointRow, pointQuery, row_eq, RowReplay.read, List.all_nil, ite_true, Except.bind, bind, RowOperations.retarget]
    cases RowOperations.read value Signature.codec parent.sign parent.signature root [Isolation.pointQuery point] packet <;> rfl

/-- Restore a supplied descriptor with equal operations and retain its literal data. -/
@[expose] def selected (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (subject graph : Codec.Json) :
    Except String (Descriptor parent.Value Signature parent.sign parent.signature) :=
  (@Algebraic.RootReplay.readDescriptor parent.Value Signature
    (Tower.instZeroValue parent) (Tower.instDecidableEqValue parent) inferInstance
    operations.one operations.add operations.sub operations.mul operations.natCast
    value Signature.codec parent.sign parent.signature subject graph).map
    (@Descriptor.changeOps parent.Value Signature (Tower.instZeroValue parent)
      (Tower.instDecidableEqValue parent) inferInstance
      (Tower.instOneValue parent) (Tower.instAddValue parent) (Tower.instSubValue parent)
      (Tower.instMulValue parent) (Tower.instNatCastValue parent)
      operations.one operations.add operations.sub operations.mul operations.natCast
      operations.one_eq operations.add_eq operations.sub_eq operations.mul_eq operations.natCast_eq
      parent.sign parent.signature)

theorem selected_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (subject graph : Codec.Json) :
    selected operations value subject graph =
      Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign parent.signature subject graph := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    unfold selected
    cases Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign parent.signature subject graph with
    | error cause => rfl
    | ok root => simp only [Except.map, Descriptor.changeOps_self]

/-- Check the ordinary-point linear-head identity using supplied subtraction. -/
@[expose] def linear (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (root : Descriptor parent.Value Signature parent.sign parent.signature) (point : parent.Value) : Bool :=
  (@DensePoly.sub parent.Value (Tower.instZeroValue parent) (Tower.instDecidableEqValue parent)
    operations.sub root.raw.head (pointQuery operations point)).isZero

theorem linear_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (root : Descriptor parent.Value Signature parent.sign parent.signature) (point : parent.Value) :
    linear operations root point = (root.raw.head - Isolation.pointQuery point).isZero := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    rfl

/-- Read the unchanged sector layout while keeping every original root and cut index. -/
@[expose] def sector (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (roots : List (Descriptor parent.Value Signature parent.sign parent.signature))
    (cut : Fin (roots.length+1)) (queries : List parent.Poly) (packet : Codec.Json) :
    Except Replay.Error (CellPackets.Sector parent.sign parent.signature roots cut queries) :=
  CellPacketRead.readUsing value Signature.codec parent.sign parent.signature guards roots cut queries packet
    (fun root queries packet => row operations value [] root queries packet)
    (pointRow operations value) (selected operations value)
    (fun root point => ⟨linear operations root point, linear_eq operations root point⟩)

theorem sector_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (roots : List (Descriptor parent.Value Signature parent.sign parent.signature))
    (cut : Fin (roots.length+1)) (queries : List parent.Poly) (packet : Codec.Json) :
    sector operations value guards roots cut queries packet =
      CellPacketRead.read value Signature.codec parent.sign parent.signature guards roots cut queries packet := by
  have rows : (fun root queries packet => row operations value [] root queries packet) =
      RowOperations.read value Signature.codec parent.sign parent.signature := by
    funext root queries packet
    rw [row_eq]
    rfl
  have boundary : pointRow operations value =
      (fun root point => RowOperations.read value Signature.codec parent.sign parent.signature root [Isolation.pointQuery point]) := by
    funext root point packet
    exact pointRow_eq operations value root point packet
  have selected : selected operations value =
      Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign parent.signature := by
    funext subject graph
    exact selected_eq operations value subject graph
  have linear : (fun root point => (⟨linear operations root point, linear_eq operations root point⟩ :
      {test : Bool // test = (root.raw.head - Isolation.pointQuery point).isZero})) =
      (fun root point => ⟨(root.raw.head - Isolation.pointQuery point).isZero, rfl⟩) := by
    funext root point
    apply Subtype.ext
    exact linear_eq operations root point
  unfold sector
  rw [rows, boundary, selected, linear]
  rfl

/-- Read and transport a section row for the fixed shared source formula. -/
@[expose] def formulaRow (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    Except Replay.Error (SelectedSigns root (RepresentationSpecialize.prepare values formula)) := do
  let source ← row operations value [] root (prepare operations values formula) packet
  return RowOperations.retarget parent.sign parent.signature rfl (prepare_eq operations values formula) source

theorem formulaRow_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    formulaRow operations value root values formula packet =
      RowReplay.read value [] root (RepresentationSpecialize.prepare values formula) packet := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    simp only [formulaRow, prepare, row_eq, RowOperations.retarget]
    cases RowReplay.read value [] root (RepresentationSpecialize.prepare values formula) packet <;> rfl

/-- Read and transport a sector row for the fixed shared source formula. -/
@[expose] def formulaSector (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (roots : RootReplay.Result p .negInf .posInf)
    (cut : Fin (roots.roots.length+1)) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    Except Replay.Error (SectorReplay.Result roots cut values formula) := do
  let source ← sector operations value [] roots.roots cut (prepare operations values formula) packet
  return SectorReplay.fromPacket
    (CellPackets.Sector.changeQueries parent.sign parent.signature (prepare_eq operations values formula) source)

theorem formulaSector_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (roots : RootReplay.Result p .negInf .posInf)
    (cut : Fin (roots.roots.length+1)) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    formulaSector operations value roots cut values formula packet =
      SectorReplay.read value [] roots cut values formula packet := by
  cases operations with
  | mk one add neg sub mul inv div nat ho ha hn hs hm hi hd hc sign hsign =>
    cases ho; cases ha; cases hn; cases hs; cases hm; cases hi; cases hd; cases hc
    simp only [formulaSector, prepare, sector_eq, SectorReplay.read, List.all_nil,
      bind, Except.bind, CellPackets.Sector.changeQueries,
      CellPackets.Point.changeQueries]
    cases CellPacketRead.read value Signature.codec parent.sign parent.signature [] roots.roots cut
        (RepresentationSpecialize.prepare values formula) packet <;> rfl

/-- Restore all cells in strict index order with equal supplied arithmetic. -/
@[expose] def readCells (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (roots : RootReplay.Result p .negInf .posInf) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    Except Replay.Error (CellReplay.Evidence roots values formula) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let fields ← match Codec.tuple 2 packet with
    | .error _ => .error .evidence
    | .ok fields => .ok fields
  let sectionFields ← match Codec.tuple roots.roots.length fields[0] with
    | .error _ => .error .evidence
    | .ok fields => .ok fields
  let sectorFields ← match Codec.tuple (roots.roots.length+1) fields[1] with
    | .error _ => .error .evidence
    | .ok fields => .ok fields
  let sections ← CellRead.collect (fun i => SelectedSigns (roots.roots.get i)
      (RepresentationSpecialize.prepare values formula)) (fun i =>
    formulaRow operations value (roots.roots.get i) values formula sectionFields[i])
  let sectors ← CellRead.collect (fun cut => SectorReplay.Result roots cut values formula) (fun cut =>
    formulaSector operations value roots cut values formula sectorFields[cut])
  return ⟨sections, fun cut => (sectors cut).sector, fun cut => (sectors cut).row⟩

theorem readCells_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (roots : RootReplay.Result p .negInf .posInf) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (packet : Codec.Json) :
    readCells operations value guards roots values formula packet =
      CellRead.read value guards roots values formula packet := by
  simp only [readCells, CellRead.read, formulaRow_eq, formulaSector_eq]
  rfl

/-- Validate original divisors and radical identities before the strict quantified fold. -/
@[expose] def fold (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : CellReplay.Evidence roots values formula) (quantifier : RealFormula.Quantifier) :
    Except Replay.Error Bool :=
  if guards.all (fun d => Decidable.decide (d ≠ 0)) = true then
    if radical operations values formula cert = true then
      match data.run quantifier with
      | none => .error .binding
      | some verdict => .ok verdict
    else .error .binding
  else .error .divisor

theorem fold_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : CellReplay.Evidence roots values formula) (quantifier : RealFormula.Quantifier) :
    fold operations values formula guards cert roots data quantifier =
      CellReplay.check values formula guards cert roots data quantifier := by
  simp only [fold, CellReplay.check, radical_eq]
  rfl

/-- Restore the complete root table and cell payload with equal supplied arithmetic. -/
@[expose] def read (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (rootGraph cells : Codec.Json) :
    Except Replay.Error (Σ roots : RootReplay.Result p .negInf .posInf,
      CellReplay.Evidence roots values formula) := do
  let roots ← RootReplay.readWith value guards p .negInf .posInf
    operations.one operations.add operations.sub operations.mul operations.natCast
    operations.one_eq operations.add_eq operations.sub_eq operations.mul_eq operations.natCast_eq rootGraph
  let rows ← readCells operations value guards roots values formula cells
  return ⟨roots,rows⟩

theorem read_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (guards : List parent.Value)
    (p : DensePoly parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (rootGraph cells : Codec.Json) :
    read operations value guards p values formula rootGraph cells =
      CompleteReplay.read value guards p values formula rootGraph cells := by
  simp only [read, CompleteReplay.read, RootReplay.readWith_eq, readCells_eq]

/-- Check the entire supplied packet, preserving every error and both verdicts. -/
@[expose] def check (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json) : Except Replay.Error Bool := do
  let restored ← read operations value guards cert.core values formula rootGraph cells
  fold operations values formula guards cert restored.1 restored.2 quantifier

theorem check_eq (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json) :
    check operations value values formula guards cert quantifier rootGraph cells =
      CompleteReplay.check value values formula guards cert quantifier rootGraph cells := by
  simp only [check, CompleteReplay.check, read_eq, fold_eq]
/-- The owner assembly API checks an optional success predicate. Only an
accepted true verdict is a success; the public checker retains typed failures
and the diagnostic false result. -/
@[expose] def accept? (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json) : Option Unit :=
  match check operations value values formula guards cert quantifier rootGraph cells with
  | .ok true => some ()
  | _ => none

theorem accept?_iff (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json) :
    accept? operations value values formula guards cert quantifier rootGraph cells = some () ↔
      CompleteReplay.check value values formula guards cert quantifier rootGraph cells = .ok true := by
  rw [← check_eq operations value values formula guards cert quantifier rootGraph cells]
  unfold accept?
  cases check operations value values formula guards cert quantifier rootGraph cells with
  | error cause => simp
  | ok verdict => cases verdict <;> simp

/-- Accepted replay establishes every original real divisor guard. -/
theorem check_domains (model : Model parent ℝ)
    (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json) (verdict : Bool)
    (accepted : check operations value values formula guards cert quantifier rootGraph cells = .ok verdict) :
    ∀ d ∈ guards, model.value d ≠ 0 :=
  CompleteReplay.check_domains model value values formula guards cert quantifier rootGraph cells verdict
    ((check_eq operations value values formula guards cert quantifier rootGraph cells).symm.trans accepted)

/-- Equal supplied arithmetic preserves the complete original quantified
sentence theorem, with no source-identity or coverage premise added. -/
theorem check_sound (model : Model parent ℝ)
    (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json)
    (accepted : check operations value values formula guards cert quantifier rootGraph cells = .ok true) :
    (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
      (fun i => model.value (values i)) :=
  CompleteReplay.check_sound model value values formula guards cert quantifier rootGraph cells
    ((check_eq operations value values formula guards cert quantifier rootGraph cells).symm.trans accepted)
end Hex.RCF.RealCoefficients.CellOperations
