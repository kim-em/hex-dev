/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RootReplay
public import HexSignDet.Produce
public import HexRealClosureTheory.TowerModel
public import HexRCF.RealCoefficients.RadicalProgress
public section
namespace Hex.RCF.RealCoefficients.RootBuild
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
inductive Error where
  | domain
  | radical
  | production (error : BuildError)
  deriving Repr

/-- Retain the full checked derivative tree while using the existing shared
root extraction. This is native production, separate from frozen replay. -/
def build (p : DensePoly parent.Value) : Except Error (RootReplay.Result p .negInf .posInf) := do
  let raw := RootReplay.subject p .negInf .posInf
  match hd : Sturm.prepare parent.sign p .negInf .posInf with
  | none => throw .domain
  | some domain =>
    let table ← buildPrepared parent.signature domain (raw.full []).queries |>.mapError Error.production
    have bindings := Sturm.prepare_eq_some parent.sign p .negInf .posInf domain hd
    have checked : table.val.check parent.sign parent.signature p .negInf .posInf
        (raw.full []).queries = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using table.property
    match extracted : RootReplay.extract p .negInf .posInf table.val checked with
    | .error error => throw (.production error)
    | .ok roots =>
      return ⟨table.val, checked, roots,
        (RootReplay.extract_eq p .negInf .posInf table.val checked).symm.trans extracted⟩


/-- Retain precisely the root list returned by the owner producer, together
with its actual checked tree and full extraction equation. -/
theorem from_production (p : DensePoly parent.Value)
    (out : List (Descriptor parent.Value Signature parent.sign parent.signature))
    (produced : Descriptor.buildRoots parent.sign parent.signature p .negInf .posInf = .ok (some out)) :
    ∃ result, build p = .ok result ∧ result.roots = out := by
  obtain ⟨domain, hd, table, ht, extracted⟩ := Descriptor.buildRoots_spec produced
  have bindings := Sturm.prepare_eq_some parent.sign p .negInf .posInf domain hd
  have checked : table.val.check parent.sign parent.signature p .negInf .posInf
      ((RootReplay.subject p .negInf .posInf).full []).queries = true := by
    simpa only [RootReplay.subject, bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using table.property
  have selected : RootReplay.extract p .negInf .posInf table.val checked = .ok out := by
    simpa only [RootReplay.extract_eq, RootReplay.subject, SignDet.Replay.table_rows] using extracted
  let result : RootReplay.Result p .negInf .posInf :=
    ⟨table.val, checked, out, (RootReplay.extract_eq p .negInf .posInf table.val checked).symm.trans selected⟩
  refine ⟨result, ?_, rfl⟩
  unfold build
  dsimp only
  split
  · rename_i absent
    have impossible : (some domain : Option _) = none := hd.symm.trans absent
    cases impossible
  · rename_i actual ha
    have same : actual = domain := Option.some.inj (ha.symm.trans hd)
    subst actual
    simp only [RootReplay.subject, ht, Except.mapError, bind, Except.bind]
    split
    · rename_i error rejected
      rw [selected] at rejected
      cases rejected
    · rename_i output accepted
      have same : output = out := Except.ok.inj (accepted.symm.trans selected)
      subst output
      rfl


/-- The owner's total lawful root enumeration constructs the complete table
for every squarefree interpreted head in an ordinary real parent model. -/
theorem success (model : Model parent ℝ) (p : DensePoly parent.Value)
    (squarefree : Squarefree (HexPolyTheory.Interpret.interpret model.value model.zero_iff p)) :
    ∃ result, build p = .ok result := by
  classical
  have domain : HexSturmTheory.Domain model.value model.zero_iff p .negInf .posInf :=
    ⟨squarefree.ne_zero, squarefree, trivial, trivial, trivial⟩
  obtain ⟨out, produced⟩ := Descriptor.buildRoots_success model.value model.zero_iff
    model.one model.add model.sub model.mul model.nat model.sign model.neg model.inv
    parent.signature p .negInf .posInf domain
  obtain ⟨result, checked, _⟩ := from_production p out produced
  exact ⟨result, checked⟩

/-- Construct the reduced carrier and retain its complete native root table.
The original input remains bound by the radical certificate's literal check. -/
def prepare (input : DensePoly parent.Value) :
    Except Error (Σ cert : RadicalCert parent.Value Signature,
      RootReplay.Result cert.core .negInf .posInf) := do
  let some cert := RadicalCert.buildMonic parent.signature input | throw .radical
  let roots ← build cert.core
  return ⟨cert, roots⟩

/-- Actual radical progress supplies squarefreeness; root construction then
succeeds without an assumed carrier, root list or production equation. -/
theorem prepare_success (model : Model parent ℝ) (input : DensePoly parent.Value)
    (nonzero : input ≠ 0) :
    ∃ packet, prepare input = .ok packet ∧ packet.1.check parent.signature input = true := by
  obtain ⟨cert, proposed⟩ := RadicalCert.buildMonic_success_real model.value model.zero_iff
    model.one model.add model.sub model.mul model.div model.inv model.nat
    parent.signature input nonzero
  have squarefree := RadicalCert.buildMonic_squarefree model.value model.zero_iff
    model.sub model.mul model.div model.inv model.nat parent.signature input cert proposed
  obtain ⟨roots, produced⟩ := success model cert.core squarefree
  refine ⟨⟨cert, roots⟩, ?_, RadicalCert.buildMonic_checked parent.signature input cert proposed⟩
  simp only [prepare, proposed, produced, bind, Except.bind, pure, Except.pure]

end Hex.RCF.RealCoefficients.RootBuild
