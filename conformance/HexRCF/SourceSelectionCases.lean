/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SourceSelection
public import HexRCF.NativeSelectionLiterals
public import HexRealClosure.RootReplay
public import HexRCF.RealCoefficients.RootQuote
public meta import HexRCF.RealCoefficients.RootQuote
public section
/-! The existing frozen count-one descriptor is quoted with ordinary public
module imports. Every emitted declaration receives ordinary kernel checking. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SourceSelectionCases
@[expose] def reader := Algebraic.RootReplay.readDescriptor ValueCodec.rat ValueCodec.nat
  Hex.Sturm.orderSign 7 Hex.RCF.RealCoefficients.NativeSelectionLiterals.subject
    Hex.RCF.RealCoefficients.NativeSelectionLiterals.graph
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 32768 in
run_meta do
  withOptions (fun options => debug.skipKernelTC.set (Elab.async.set options false) false) do
   withExporting (isExporting := false) do
    -- This literal regression measures quotation separately from the public default limit.
    let basic : Hex.RealFormula.Reify.Config := {}
    let config := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := 2000000}}}
    let quoted ← match ← RootQuote.quote (mkConst ``reader) (config := config) with
      | .ok result => pure result
      | .error error => throwError "source-selection root quotation: {Hex.RealFormula.Reify.Error.toMessageData error}"
    logInfo m!"source-selection root quotation proofNodes={quoted.usage.proofNodes}"
    withExporting (isExporting := true) do
      let declaration := Declaration.defnDecl {
        name := `Hex.RCF.SourceSelectionCases.root,
        levelParams := [],type := mkApp (mkConst ``Root) (mkNatLit 7),value := quoted.value,
        hints := .regular 0,safety := .safe}
      addDecl declaration (forceExpose := true)
      compileDecl declaration (logErrors := true)
      let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``reader])
        (← mkAppM ``Option.some #[mkConst `Hex.RCF.SourceSelectionCases.root])
      let proof := mkExpectedPropHint quoted.proof statement
      addDecl (.thmDecl {
        name := `Hex.RCF.SourceSelectionCases.reader_eq,levelParams := [],
        type := statement,value := proof})
theorem accepted : reader.toOption.isSome = true := by rw [reader_eq]; rfl

@[expose] def head : DensePoly Rat := ⟨#[-2,0,1], Or.inr (by decide)⟩

@[expose] def rawSubject : RawDescriptor Rat Nat :=
  ⟨7, head, .finite (7/5), .finite (3/2), [1,2], [1,1]⟩

theorem head_eq : head = DensePoly.ofCoeffs #[-2,0,1] :=
  (DensePoly.ofCoeffs_toArray head).symm

@[expose] def bindingReader := Algebraic.SignRequests.readBinding ValueCodec.rat ValueCodec.nat
  rawSubject Hex.RCF.RealCoefficients.NativeSelectionLiterals.subject

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 32768 in
run_meta do
  withoutExporting do
    let quoted ← match ← RootQuote.quote (mkConst ``bindingReader) with
      | .ok result => pure result
      | .error error => throwError "source-header binding: {Hex.RealFormula.Reify.Error.toMessageData error}"
    logInfo m!"source-header binding proofNodes={quoted.usage.proofNodes}"
    let proof ← mkAppM ``RootQuote.read_eq #[mkConst ``bindingReader, quoted.value, quoted.proof]
    let okUnit := mkAppN (mkConst ``Except.ok [.zero,.zero])
      #[mkConst ``String,mkConst ``Unit,mkConst ``Unit.unit]
    let statement ← mkEq (mkConst ``bindingReader) okUnit
    let proof ← Hex.RCF.checkProof `literalHeader statement proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.SourceSelectionCases.binding_checked, levelParams := [],
        type := statement, value := mkExpectedPropHint proof statement})

theorem parsed : Algebraic.SignRequests.readRoot ValueCodec.rat ValueCodec.nat
    Hex.RCF.RealCoefficients.NativeSelectionLiterals.subject = .ok rawSubject :=
  Algebraic.SignRequests.readBinding_checked _ _ _ _ binding_checked

/-- The exact original reader and the owner's descriptor-binding law identify
its supplied raw subject without normalizing the checked root again. -/
theorem subject : root.raw = rawSubject := by
  have checked := RootQuote.read_eq reader root reader_eq
  unfold reader Algebraic.RootReplay.readDescriptor at checked
  rw [parsed] at checked
  simp only [bind, Except.bind] at checked
  cases graph : Codec.readGraph ValueCodec.rat ValueCodec.nat 7 rawSubject.head
      rawSubject.lower rawSubject.upper Hex.RCF.RealCoefficients.NativeSelectionLiterals.graph with
  | error message => simp [graph] at checked
  | ok data =>
      simp only [graph, Except.bind] at checked
      cases accepted : data.descriptor? Hex.Sturm.orderSign 7 rawSubject with
      | none => simp [accepted] at checked
      | some value =>
          simp only [accepted] at checked
          have same := Except.ok.inj checked
          exact (congrArg Descriptor.raw same).symm.trans (Dag.descriptor_raw accepted)

/-- The selected value is the positive conjugate, using the checked original
head and strict interval rather than another selected-root search. -/
theorem selected : root.real = Real.sqrt 2 := by
  have nonzero := root.head_ne_zero ratCast ratZero
  have spec := (HexRealRootsTheory.Tarski.mem_rootsIn_iff _ nonzero _ _ _).mp root.real_spec.1
  obtain ⟨polynomial, interval⟩ := spec
  obtain ⟨lower, upper⟩ := (HexRealRootsTheory.Tarski.inInterval_iff _ _ _).mp interval
  rw [subject] at polynomial lower upper
  change (realPoly head).eval root.real = 0 at polynomial
  rw [head_eq] at polynomial
  norm_num [realPoly, HexPolyTheory.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
    HexPolyTheory.toPolynomial_ofCoeffs, Finset.sum_range_succ, ratCast,
    rawSubject, head, Endpoint.map] at polynomial lower upper
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

end Hex.RCF.SourceSelectionCases
