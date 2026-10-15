/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellReplay
public import HexRCF.RealCoefficients.SectorReplay
public import HexRCF.RealCoefficients.RowReplay
public section
namespace Hex.RCF.RealCoefficients.CellRead
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value}

/-- Retain and check every finite index before transporting its dependent data.
The same strict collection serves native production and literal replay. -/
@[expose] def collectWith {ε : Type} {m : Nat} (failure : ε) (P : Fin m → Type)
    (read : (i : Fin m) → Except ε (P i)) : Except ε ((i : Fin m) → P i) := do
  let entries : Vector (Sigma P) m ← Vector.ofFnM (fun i => do return ⟨i, ← read i⟩)
  if aligned : ∀ i, (entries[i]).1 = i then
    return fun i => (aligned i) ▸ (entries[i]).2
  else throw failure

/-- Literal replay retains its existing binding diagnostic. No missing index
receives a default record. -/
@[expose] def collect {m : Nat} (P : Fin m → Type)
    (read : (i : Fin m) → Except Replay.Error (P i)) : Except Replay.Error ((i : Fin m) → P i) :=
  collectWith .binding P read

/-- Successful child calls produce the complete dependent family in index order. -/
theorem collectWith_success {ε : Type} {m : Nat} (failure : ε) (P : Fin m → Type)
    (read : (i : Fin m) → Except ε (P i))
    (total : ∀ i, ∃ value, read i = .ok value) :
    ∃ values, collectWith failure P read = .ok values ∧ ∀ i, read i = .ok (values i) := by
  classical
  choose values produced using total
  have same : (fun i => (do return ⟨i, ← read i⟩ : Except ε (Sigma P))) =
      (fun i => (pure ⟨i, values i⟩ : Except ε (Sigma P))) := by
    funext i
    simp [produced i, bind, Except.bind, pure, Except.pure]
  refine ⟨values, ?_, produced⟩
  unfold collectWith
  rw [same, Vector.ofFnM_pure]
  simp only [bind, Except.bind, pure, Except.pure]
  have aligned : ∀ i : Fin m,
      (Vector.ofFn (fun i => (⟨i,values i⟩ : Sigma P)))[i].1 = i := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [dite_eq_left aligned]
  simp only [Except.ok.injEq]
  funext i
  have cast_entry (entry : Sigma P) (same : entry = ⟨i,values i⟩) (index : entry.1 = i) :
      index ▸ entry.2 = values i := by
    cases same
    rfl
  apply cast_entry
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

/-- Restore every section and sector in exact order after original guard
preflight. All child errors propagate through the strict finite collection. -/
@[expose] def read (value : ValueCodec parent.Value) (guards : List parent.Value)
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
  let sections ← collect (fun i => SelectedSigns (roots.roots.get i)
      (RepresentationSpecialize.prepare values formula)) (fun i =>
    RowReplay.read value [] (roots.roots.get i) (RepresentationSpecialize.prepare values formula)
      sectionFields[i])
  let sectors ← collect (fun cut => SectorReplay.Result roots cut values formula) (fun cut =>
    SectorReplay.read value [] roots cut values formula sectorFields[cut])
  return ⟨sections, fun cut => (sectors cut).sector, fun cut => (sectors cut).row⟩
end Hex.RCF.RealCoefficients.CellRead
