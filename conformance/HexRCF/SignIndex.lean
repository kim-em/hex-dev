/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexRCF.RealCoefficients.FieldIndex
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofEvidence
public section

namespace Hex.RCF.SignIndexTests
open Hex RealCoefficients LiteralSign

def entries : Array (Entry Nat) := #[⟨8, -1, none⟩, ⟨2, 1, none⟩,
  ⟨6, 0, none⟩, ⟨0, 1, none⟩, ⟨4, -1, none⟩]

def tree : Index := Index.build entries compare

#guard tree.lookup entries compare 8 == some (-1)
#guard tree.lookup entries compare 2 == some 1
#guard tree.lookup entries compare 6 == some 0
#guard tree.lookup entries compare 0 == some 1
#guard tree.lookup entries compare 4 == some (-1)
#guard (tree.lookup entries compare 3).isNone
#guard (tree.lookup entries compare 10).isNone
#guard (Index.build (#[] : Array (Entry Nat)) compare).lookup #[] compare 0 == none

-- Wrong positions cannot return a different key's sign. Unequal comparison
-- ties and out-of-range positions remain missing reads.
#guard (Index.node 0 .empty .empty).lookup entries compare 2 == none
#guard (Index.node 99 .empty .empty).lookup entries compare 8 == none
#guard (Index.node 0 (.node 1 .empty .empty) .empty).lookup entries
  (fun _ _ => .eq) 2 == none
#guard (Index.node 0 (.node 1 .empty .empty) .empty).lookup entries compare 2 == some 1

def polynomial : Hex.DensePoly Rat := Hex.DensePoly.ofList [-2, 0, 1]
def query (key : Nat) : Hex.DensePoly Rat :=
  Hex.DensePoly.C (if key = 0 then -1 else if key = 1 then 0 else 1)
def table? : Option (Table Nat) := Table.build polynomial 1 2 [0, 1, 2] query

#guard table?.isSome
#guard table?.map (fun table => table.check query) == some true
#guard table?.map (fun table => table.lookupIndex compare
  (Index.build table.entries.toArray compare) 0) == some (some (-1))
#guard table?.map (fun table => table.lookupIndex compare
  (Index.build table.entries.toArray compare) 1) == some (some 0)
#guard table?.map (fun table => table.lookupIndex compare
  (Index.build table.entries.toArray compare) 2) == some (some 1)
#guard table?.map (fun table => table.lookupIndex compare
  (Index.build table.entries.toArray compare) 3) == some none

-- Every original recorded hit survives malformed cache routing.
#guard table?.map (fun table => table.lookupIndex compare .empty 0) == some (some (-1))
#guard table?.map (fun table => table.lookupIndex (fun _ _ => .eq)
  (.node 99 .empty .empty) 1) == some (some 0)
#guard table?.map (fun table => table.lookupIndex compare .empty 3) == some none

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.indexSigns true

private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private abbrev hw : atomWitness SquareTwo.polynomial SquareTwo.square := by decide
private abbrev hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide
private abbrev root := SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square hw hp
private theorem real : SquareTwo.square.meetsRealAxis = true := by decide
private def values : Fin 1 → PolyQuot SquareTwo.polynomial root := fun _ =>
  SquareTwo.coordinate SquareTwo.square hw hp
private def matrix : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 1, .lt⟩) (.atom ⟨MvPoly.X 1 - 2, .lt⟩))

-- Audit the actual field comparator and every stored replay/cell operand.
-- Direct tree hits are required here, so linear fallback cannot mask a lost
-- optimization. The checker equivalences still permit arbitrary bad routing.
#guard match FieldBuild.produceWithin SquareTwo.polynomial SquareTwo.square hw hp real
    values matrix () 256 5 (monicCore := true) with
  | .error _ => false
  | .ok data =>
    let entries := data.signs.entries.toArray
    let index := Index.build entries Field.keyOrder
    Field.checkSignTable SquareTwo.polynomial SquareTwo.square hw hp data.signs &&
      (FieldBuild.signKeys values matrix data.radical.core data.isolation data.rootSigns).all
        (fun key => (index.lookup entries Field.keyOrder key).isSome &&
          index.lookup entries Field.keyOrder key == data.signs.lookup? key &&
          data.signs.lookupIndex Field.keyOrder .empty key == data.signs.lookup? key)

private meta partial def readIndex? (e : Lean.Expr) : Option Index := do
  if e.isConstOf ``Index.empty then return .empty
  if !e.isAppOfArity ``Index.node 3 then none
  let args := e.getAppArgs
  let numeral := args[0]!
  let raw := if numeral.isAppOfArity ``OfNat.ofNat 3 then numeral.getAppArgs[1]! else numeral
  let position ← raw.rawNatLit?
  return .node position (← readIndex? args[1]!) (← readIndex? args[2]!)

-- Audit the frozen tree actually passed by quotation, as well as the native
-- builder above. Quoting an empty tree cannot pass this optimization test.
run_meta do
  let (_, certificate, data, checked) ← FieldLiteral.proveRefiningWithCertificate
    (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
    (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .existsReal
  unless checked.getAppFn.isConstOf ``Eq.trans do
    throwError "indexed acceptance did not transport the original checker"
  let reverse := checked.getAppArgs[checked.getAppArgs.size - 2]!
  let same := reverse.getAppArgs.back!
  unless same.getAppFn.isConstOf ``FieldBuild.Result.checkExistsIndex_eq do
    throwError "indexed acceptance did not use its checker equivalence"
  let args := same.getAppArgs
  let some index := readIndex? args[args.size - 5]! |
    throwError "quoted sign tree was not found"
  let keys := FieldBuild.signKeys values matrix data.radical.core data.isolation data.rootSigns
  unless keys.all (fun key => (index.lookup data.signs.entries.toArray Field.keyOrder key).isSome) do
    throwError "quoted index lost a direct recorded hit"
  let quotedTable ← Lean.Meta.mkAppM ``FieldBuild.Result.signs #[certificate]
  let mut quotedEntries ← Lean.Meta.mkAppM ``Table.entries #[quotedTable]
  let mut position := 0
  while true do
    quotedEntries ← Lean.Meta.whnf quotedEntries
    if quotedEntries.isAppOfArity ``List.nil 1 then break
    unless quotedEntries.isAppOfArity ``List.cons 3 do
      throwError "quoted sign entries were not literal data"
    let row := quotedEntries.getAppArgs[1]!
    let key ← Lean.Meta.mkAppM ``Entry.key #[row]
    let coords ← Lean.Meta.mkAppM ``PolyQuot.coeffs #[key]
    let observed ← FieldRuntime.evalRatPoly coords
    let some original := data.signs.entries[position]? |
      throwError "quotation added a sign entry"
    unless observed == original.key.coeffs do
      throwError "quotation changed sign entry order"
    position := position + 1
    quotedEntries := quotedEntries.getAppArgs[2]!
  unless position == data.signs.entries.length do
    throwError "quotation omitted a sign entry"

-- A true preview with a corrupted scalar reaches kernel replay and fails there.
-- Both lookup and replay modes must retain the same terminal diagnostic and
-- restore caller state. These direct replay calls contain no solver dispatch.
run_meta do
  let .ok data := FieldBuild.produceWithin SquareTwo.polynomial SquareTwo.square hw hp real
    values matrix () 256 5 (monicCore := true) | throwError "replay failure fixture was not produced"
  for indexed in [false, true] do
    for combined in [false, true] do
      let proof ← Lean.withOptions (fun options => options
          |>.setBool `debug.skipKernelTC true
          |>.setBool `rcf.algebraic.indexSigns indexed
          |>.setBool `rcf.algebraic.singleReplay combined) do
        FieldLiteral.replay (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
          (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .existsReal data
      let constants := proof.getUsedConstants
      unless constants.contains ``FieldBuild.Result.checkExistsIndex_eq == indexed do
        throwError "successful frozen replay ignored its lookup mode"
      Hex.RCF.checkAxioms `Hex.RCF.SignIndexTests proof
  let corrupt := {data with radical.quotient := 0}
  for indexed in [false, true] do
    for combined in [false, true] do
      let before := (← Lean.getMCtx).mvarCounter
      let failure ← try
        let _ ← Lean.withOptions (fun options => options
            |>.setBool `rcf.algebraic.indexSigns indexed
            |>.setBool `rcf.algebraic.singleReplay combined) do
          FieldLiteral.replay (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
            (Lean.mkConst ``values) (Lean.mkConst ``matrix) values matrix .existsReal corrupt
        pure none
      catch error => pure (some (← error.toMessageData.toString))
      unless failure == some "rcf: fixed-field certificate replay did not prove a true verdict" do
        throwError "unexpected terminal replay diagnostic: {failure}"
      unless (← Lean.getMCtx).mvarCounter == before do
        throwError "terminal replay failure leaked metavariables"

theorem universal : ∀ x : ℝ, (x - Real.sqrt 2) ^ 2 ≥ 0 := by rcf
theorem further : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf
theorem reciprocal : ∀ x : ℝ, x ^ 2 + 1 / Real.sqrt 2 > 0 := by rcf
theorem domain : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2 := by rcf

set_option rcf.algebraic.singleReplay true in
theorem combined : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf

run_meta do
  for (name, route) in [(`Hex.RCF.SignIndexTests.universal,
      ``FieldBuild.Result.checkForallIndex_eq),
      (`Hex.RCF.SignIndexTests.further, ``FieldBuild.Result.checkExistsIndex_eq),
      (`Hex.RCF.SignIndexTests.combined, ``FieldBuild.Result.checkExistsIndex_eq),
      (`Hex.RCF.SignIndexTests.reciprocal, ``FieldBuild.Result.checkForallIndex_eq),
      (`Hex.RCF.SignIndexTests.domain, ``FieldBuild.Result.checkExistsIndex_eq)] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf route) do
      throwError "indexed proof regression did not use indexed replay"

/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Table.lookupIndex_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Table.lookupIndex_isSome

/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Index.lookup_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Index.lookup_entry
/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Table.lookupIndex_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Table.lookupIndex_spec
/-- info: 'Hex.RCF.RealCoefficients.LiteralSign.Table.signIndex_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Table.signIndex_spec

/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.Result.checkForallIndex_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FieldBuild.Result.checkForallIndex_eq
/-- info: 'Hex.RCF.RealCoefficients.FieldBuild.Result.checkExistsIndex_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FieldBuild.Result.checkExistsIndex_eq

/-- info: 'Hex.RCF.SignIndexTests.universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms universal
/-- info: 'Hex.RCF.SignIndexTests.further' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms further
/-- info: 'Hex.RCF.SignIndexTests.reciprocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocal
/-- info: 'Hex.RCF.SignIndexTests.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms domain
/-- info: 'Hex.RCF.SignIndexTests.combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combined

end Hex.RCF.SignIndexTests
