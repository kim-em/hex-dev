/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.GeneratorWindowInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.GeneratorWindowInputs
public meta import HexRCF.ProofEvidence
@[expose] public section

namespace Hex.RCF.GeneratorWindowTests
open Hex RealCoefficients LiteralSign

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

-- This negative sign straddles zero in the original interval. A checked
-- tighter window replaces its full rational query with a Horner sign.
#guard match table? [close, theta, 0] with
  | none => false
  | some original =>
    original.entries.map (·.evidence.isSome) == [true, false, false] &&
      match FieldBuild.refineSigns SquareTwo.polynomial SquareTwo.square hw hp original 1 with
      | .error _ => false
      | .ok refined =>
        let table := refined.val
        Field.checkSignTable SquareTwo.polynomial SquareTwo.square hw hp table &&
          table.refinement.isSome &&
          table.head == original.head && table.lower == original.lower &&
          table.upper == original.upper &&
          table.entries.map (·.key) == original.entries.map (·.key) &&
          table.entries.map (·.value) == [-1, 1, 0] &&
          table.entries.map (·.evidence.isSome) == [false, false, false]

-- Already separated, zero and empty tables need no window. A zero step
-- budget retains the original checked full-query evidence.
#guard [[], [theta], [0], [theta, 0]].all fun keys =>
  match table? keys with
  | none => false
  | some table =>
    match FieldBuild.refineSigns SquareTwo.polynomial SquareTwo.square hw hp table 4 with
    | .error _ => false
    | .ok refined => refined.val.refinement.isNone

#guard match table? [close] with
  | none => false
  | some table =>
    match FieldBuild.refineSigns SquareTwo.polynomial SquareTwo.square hw hp table 0 with
    | .error _ => false
    | .ok refined => refined.val.refinement.isNone &&
        refined.val.entries.all (·.evidence.isSome)

-- A bounded attempt which cannot separate a close nonzero sign must retain
-- the original evidence, rather than adding a useless second count certificate.
private def hard : K := theta - (13043817825332782212 : K) / (9223372036854775808 : K)
#guard match table? [hard] with
  | none => false
  | some original =>
    original.entries.any (·.evidence.isSome) &&
      match FieldBuild.refineSigns SquareTwo.polynomial SquareTwo.square hw hp original 1 with
      | .error _ => false
      | .ok result => result.val.refinement.isNone &&
          result.val.entries.map (·.key) == original.entries.map (·.key) &&
          result.val.entries.map (·.value) == original.entries.map (·.value) &&
          result.val.entries.all (·.evidence.isSome)

-- Corrupted original evidence is terminal before proposing any refinement.
#guard match table? [close] with
  | none => false
  | some table =>
    match FieldBuild.refineSigns SquareTwo.polynomial SquareTwo.square hw hp
        {table with count := {table.count with value := 0}} 4 with
    | .error .invalidReplay => true
    | _ => false

-- A valid inner count must be contained in the original positive-root
-- interval. A valid count for the negative conjugate is still rejected.
#guard match table? [close] with
  | none => false
  | some original =>
    match FieldBuild.refineSigns SquareTwo.polynomial SquareTwo.square hw hp original 1 with
    | .error _ => false
    | .ok refined =>
      let table := refined.val
      match table.refinement with
      | none => false
      | some window =>
        !({table with refinement := some {window with count := {window.count with value := 0}}}).check PolyQuot.coeffs &&
        !({table with entries := original.entries}).check PolyQuot.coeffs &&
        !({table with entries := table.entries.map fun (entry : Entry K) =>
          {entry with value := entry.value + 1}}).check PolyQuot.coeffs &&
        !({table with refinement := some {window with lower := window.upper}}).check PolyQuot.coeffs &&
        !({table with refinement := some {window with lower := window.upper, upper := window.lower}}).check PolyQuot.coeffs &&
        !({table with refinement := some {window with lower := original.lower - 1}}).check PolyQuot.coeffs &&
        match Table.build (ZPoly.toRatPoly SquareTwo.polynomial) (-2) (-1) ([] : List K) PolyQuot.coeffs with
        | none => false
        | some negative =>
          !({table with refinement := some ⟨negative.lower, negative.upper, negative.count⟩}).check PolyQuot.coeffs

-- An endpoint root is outside the open count domain. Empty and reversed
-- refinements are rejected rather than erasing the original root obligation.
#guard match Table.build (DensePoly.ofList [0, 1] : DensePoly Rat) (-1) 1
    ([DensePoly.ofList [0, 1]] : List (DensePoly Rat)) id with
  | none => false
  | some table =>
    (table.refine 0 1 id).isNone && (table.refine (-1) 0 id).isNone &&
      (table.refine 0 0 id).isNone && (table.refine 1 (-1) id).isNone

-- Production of a further root supplies real isolation/cell/root-sign keys.
-- Refinement preserves every key and its value in the original order.
#guard match FieldBuild.produceWithin SquareTwo.polynomial SquareTwo.square hw hp real
    values matrix () 256 5 (monicCore := true) with
  | .error _ => false
  | .ok data =>
    match FieldBuild.refineSigns SquareTwo.polynomial SquareTwo.square hw hp data.signs 4 with
    | .error _ => false
    | .ok refined =>
      Field.checkSignTable SquareTwo.polynomial SquareTwo.square hw hp refined.val &&
        refined.val.refinement.isSome &&
        refined.val.entries.map (·.key) == data.signs.entries.map (·.key) &&
        refined.val.entries.map (·.value) == data.signs.entries.map (·.value) &&
        (refined.val.entries.filter (·.evidence.isSome)).length <
          (data.signs.entries.filter (·.evidence.isSome)).length

set_option rcf.algebraic.signRefinements 4

-- The meta producer returns the exact refined data used by quotation.
run_meta do
  let (proof, certificate, data, _) ← FieldLiteral.proveRefiningWithCertificate
    (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
    (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .existsReal
  unless data.signs.refinement.isSome do
    throwError "quotation omitted the producer's checked generator window"
  let quoted ← Lean.Meta.mkAppM ``FieldBuild.Result.signs #[certificate]
  let quotedWindow ← Lean.Meta.whnf (← Lean.Meta.mkAppM ``Table.refinement #[quoted])
  unless quotedWindow.isAppOfArity ``Option.some 2 do
    throwError "quotation lost the frozen window"
  Hex.RCF.checkAxioms `Hex.RCF.GeneratorWindowTests proof
  let quotedTrue ← Lean.withOptions (fun opts => opts.setBool `rcf.algebraic.intervalSigns true) do
    FieldLiteral.resultExpr (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
      (Lean.mkConst ``matrix) matrix data
  let quotedFalse ← Lean.withOptions (fun opts => opts.setBool `rcf.algebraic.intervalSigns false) do
    FieldLiteral.resultExpr (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
      (Lean.mkConst ``matrix) matrix data
  unless quotedTrue == quotedFalse do
    throwError "frozen window quotation changed under a producer option"
  let falseValid ← try
    let _ ← FieldLiteral.replay (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
      (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .forallReal data
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  unless falseValid == some "rcf: the universal sentence is false on the prepared cells" do
    throwError "valid refined evidence changed the false verdict: {falseValid}"
  let (_, _, control, _) ← Lean.withOptions (fun opts =>
      opts.setBool `rcf.algebraic.intervalSigns false) do
    FieldLiteral.proveRefiningWithCertificate (Lean.mkConst ``SquareTwo.polynomial)
      (Lean.mkConst ``root) (Lean.mkConst ``values) (Lean.mkConst ``matrix)
      values matrix .existsReal
  unless control.signs.refinement.isNone && control.signs.entries.all (·.evidence.isSome) do
    throwError "full-query production performed useless window refinement"
  let some window := data.signs.refinement | throwError "missing test window"
  let badWindow := {window with count := {window.count with value := 0}}
  let badSigns := {data.signs with refinement := some badWindow}
  let corrupt := {data with signs := badSigns}
  for indexed in [false, true] do
    let before := (← Lean.getMCtx).mvarCounter
    let failure ← try
      let _ ← Lean.withOptions (fun options =>
          options.setBool `rcf.algebraic.indexSigns indexed) do
        FieldLiteral.replay (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
          (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .existsReal corrupt
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    -- Despite signRefinements=4, frozen replay reaches kernel rejection.
    -- It does not run the native refinement producer or repair the window.
    unless failure == some "rcf: fixed-field certificate replay did not prove a true verdict" do
      throwError "unexpected frozen-window failure: {failure}"
    unless (← Lean.getMCtx).mvarCounter == before do
      throwError "window replay failure leaked metavariables"

    -- A false preview cannot hide the same malformed inner-window evidence.
    let falseFailure ← try
      let _ ← Lean.withOptions (fun options =>
          options.setBool `rcf.algebraic.indexSigns indexed) do
        FieldLiteral.replay (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
          (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .forallReal corrupt
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    unless falseFailure == some "rcf: fixed-field certificate evidence failed replay" do
      throwError "invalid window became a false-goal diagnostic: {falseFailure}"
    unless (← Lean.getMCtx).mvarCounter == before do
      throwError "invalid false-preview window leaked metavariables"


elab "fixed_window" : tactic => Lean.Elab.Tactic.liftMetaTactic fun goal => do
  let (proof, _, _, _) ← FieldLiteral.proveRefiningWithCertificate
    (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
    (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .existsReal
  goal.assign proof
  return []

theorem fixed : ∃ x : ℝ, matrix.toProp
    (RealFormula.append (fun j => Field.value
      (Field.literalRep SquareTwo.polynomial SquareTwo.square hw hp) (values j)) x) := by
  fixed_window

set_option rcf.algebraic.signRefinements 16 in
theorem source_window : ∀ x : ℝ, x ^ 2 + Real.sqrt 3 -
    (31950697969885030203 / 18446744073709551616 : ℝ) > 0 := by rcf

run_meta do
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.GeneratorWindowTests.source_window
      (fun e => e.isConstOf ``Window.mk) do
    throwError "the complete tactic path emitted no generator window"
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.GeneratorWindowTests.source_window
      (fun e => e.isConstOf ``CommonPresentation.checkPolynomials_sound) do
    throwError "the checked window bypassed common-field source authentication"

theorem further : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf
theorem guarded : ∀ x : ℝ, x ^ 2 + 1 / Real.sqrt 2 > 0 := by rcf
theorem domain : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2 := by rcf

run_meta do
  for name in [`Hex.RCF.GeneratorWindowTests.further,
      `Hex.RCF.GeneratorWindowTests.guarded, `Hex.RCF.GeneratorWindowTests.domain] do
    unless ← Hex.RCF.ProofEvidence.contains name
        (fun e => e.isConstOf ``FieldBuild.Result.checkExistsIndex_eq ||
          e.isConstOf ``FieldBuild.Result.checkForallIndex_eq) do
      throwError "window proof did not use indexed checked sign retrieval"
    for producer in [``FieldBuild.refineSigns, ``RefinedIsolation.refineTo?,
        ``Table.refine, ``FieldBuild.produceWithin] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf producer) then
        throwError "window quotation embedded a native producer"

run_meta do
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.GeneratorWindowTests.fixed
      (fun e => e.isConstOf ``Window.mk) do
    throwError "fixed-field quoted proof omitted the checked window"

/-- info: 'Hex.RCF.GeneratorWindowTests.source_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_window
/-- info: 'Hex.RCF.GeneratorWindowTests.fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixed
/-- info: 'Hex.RCF.GeneratorWindowTests.further' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms further
/-- info: 'Hex.RCF.GeneratorWindowTests.guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guarded
/-- info: 'Hex.RCF.GeneratorWindowTests.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms domain
/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Window.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Window.bounds
/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Table.entry_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Table.entry_spec

end Hex.RCF.GeneratorWindowTests
