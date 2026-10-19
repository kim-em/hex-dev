/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Scalars
import HexRCF.SelectedRoot.RowTools
import HexRCF.RealCoefficients.ScalarPacket
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
elab "#algebraic_seed_facts" : command => liftTermElabM do
  let entries : Array (Expr × Expr × Expr) := #[
    (Lean.mkConst ``Scalars.p0, Lean.mkConst ``Scalars.s0, Lean.mkConst ``Scalars.g0),
    (Lean.mkConst ``Scalars.p1, Lean.mkConst ``Scalars.s1, Lean.mkConst ``Scalars.g1),
    (Lean.mkConst ``Scalars.p2, Lean.mkConst ``Scalars.s2, Lean.mkConst ``Scalars.g2),
    (Lean.mkConst ``Scalars.p3, Lean.mkConst ``Scalars.s3, Lean.mkConst ``Scalars.g3),
    (Lean.mkConst ``Scalars.p4, Lean.mkConst ``Scalars.s4, Lean.mkConst ``Scalars.g4),
    (Lean.mkConst ``Scalars.p5, Lean.mkConst ``Scalars.s5, Lean.mkConst ``Scalars.g5),
    (Lean.mkConst ``Scalars.p6, Lean.mkConst ``Scalars.s6, Lean.mkConst ``Scalars.g6),
    (Lean.mkConst ``Scalars.p7, Lean.mkConst ``Scalars.s7, Lean.mkConst ``Scalars.g7),
    (Lean.mkConst ``Scalars.p8, Lean.mkConst ``Scalars.s8, Lean.mkConst ``Scalars.g8),
    (Lean.mkConst ``Scalars.p9, Lean.mkConst ``Scalars.s9, Lean.mkConst ``Scalars.g9),
    (Lean.mkConst ``Scalars.p10, Lean.mkConst ``Scalars.s10, Lean.mkConst ``Scalars.g10),
    (Lean.mkConst ``Scalars.p11, Lean.mkConst ``Scalars.s11, Lean.mkConst ``Scalars.g11),
    (Lean.mkConst ``Scalars.p12, Lean.mkConst ``Scalars.s12, Lean.mkConst ``Scalars.g12),
    (Lean.mkConst ``Scalars.p13, Lean.mkConst ``Scalars.s13, Lean.mkConst ``Scalars.g13),
    (Lean.mkConst ``Scalars.p14, Lean.mkConst ``Scalars.s14, Lean.mkConst ``Scalars.g14),
    (Lean.mkConst ``Scalars.p15, Lean.mkConst ``Scalars.s15, Lean.mkConst ``Scalars.g15),
    (Lean.mkConst ``Scalars.p16, Lean.mkConst ``Scalars.s16, Lean.mkConst ``Scalars.g16),
    (Lean.mkConst ``Scalars.p17, Lean.mkConst ``Scalars.s17, Lean.mkConst ``Scalars.g17),
    (Lean.mkConst ``Scalars.p18, Lean.mkConst ``Scalars.s18, Lean.mkConst ``Scalars.g18),
    (Lean.mkConst ``Scalars.p19, Lean.mkConst ``Scalars.s19, Lean.mkConst ``Scalars.g19),
    (Lean.mkConst ``Scalars.p20, Lean.mkConst ``Scalars.s20, Lean.mkConst ``Scalars.g20)]
  let value ← mkAppM ``Tower.Context.codec #[Lean.mkConst ``Data.base]
  let context := Lean.mkConst ``Data.native
  let factType ← mkAppM ``Algebraic.SignFact #[Lean.mkConst ``Data.native]
  let mut facts ← mkAppOptM ``List.nil #[some factType]
  for i in [:entries.size] do
    let (polynomial, claimed, graph) := entries[i]!
    let args := #[Lean.mkConst ``Data.rational, value, context, polynomial, claimed, graph]
    let read ← mkAppM ``ScalarPacket.read args
    let type ← mkEq (← mkAppM ``Option.isSome #[read]) (Lean.mkConst ``Bool.true)
    let proof ← mkDecideProof type
    let name := Name.str `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records s!"accepted{i}"
    KernelCheck.addChecked name type proof #[``ScalarPacket.build, ``ScalarPacket.buildLiteral, ``Descriptor.ofReplay?]
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected scalar seed axiom"
    let fact ← mkAppM ``ScalarPacket.restore (args.push (Lean.mkConst name))
    facts ← mkAppM ``List.cons #[fact, facts]
  let declaration := Declaration.defnDecl {
    name := `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records.facts
    levelParams := []
    type := ← inferType facts
    value := facts
    hints := .regular 0
    safety := .safe }
  addDecl declaration
  compileDecl declaration (logErrors := true)
  logInfo m!"checked {entries.size} frozen scalar proposals"
#algebraic_seed_facts
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records
