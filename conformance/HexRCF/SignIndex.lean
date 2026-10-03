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
open RealCoefficients LiteralSign

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
      (`Hex.RCF.SignIndexTests.combined, ``FieldBuild.Result.checkExistsIndex_eq)] do
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
