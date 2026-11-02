/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexGroebnerStateNative
import HexGroebner.Elimination
meta import Lean.Compiler.LCNF.ToImpureType
meta import Lean.Structure

/-! Check field names as well as constructor geometry: swapping two object
fields must fail before the native conformance executable can run. -/

open Lean Lean.Compiler.LCNF

private meta def checkLayout (name : Name) (objects scalars : Nat)
    (fields : Array (String × String)) : CoreM Unit := do
  let info ← getConstInfoInduct name
  let layout ← getCtorLayout info.ctors[0]!
  unless layout.ctorInfo.size == objects && layout.ctorInfo.usize == 0 &&
      layout.ctorInfo.ssize == scalars do
    throwError "native layout changed for {name}: expected {objects} objects, {scalars} scalar bytes"
  let fieldsInfo := getStructureInfo (← getEnv) name
  unless fieldsInfo.fieldNames.size == fields.size && layout.fieldInfo.size == fields.size do
    throwError "native field count changed for {name}"
  for i in [:fields.size] do
    let (field,expected) := fields[i]!
    let actualName := fieldsInfo.fieldNames[i]!.getString!
    let actual := match layout.fieldInfo[i]! with
      | .object slot _ => s!"o{slot}"
      | .scalar size offset _ => s!"s{size}@{offset}"
      | .usize slot => s!"u{slot}"
      | .erased => "erased"
      | .void => "void"
    unless actualName == field && actual == expected do
      throwError "native layout changed for {name}.{field}: expected {expected}, got {actualName}:{actual}"

private meta def checkTags (name : Name) (expected : Array String) : CoreM Unit := do
  let info ← getConstInfoInduct name
  let actual := (info.ctors.map Name.getString!).toArray
  unless actual == expected do
    throwError "native constructor tags changed for {name}: expected {expected}, got {actual}"
  for i in [:expected.size] do
    let layout ← getCtorLayout info.ctors[i]!
    unless layout.ctorInfo.cidx == i do
      throwError "native compiler tag changed for {name}.{expected[i]!}: {layout.ctorInfo.cidx}"

private meta def checkCtor (name : Name) (objects scalars : Nat)
    (fields : Array String) : CoreM Unit := do
  let layout ← getCtorLayout name
  unless layout.ctorInfo.size == objects && layout.ctorInfo.usize == 0 &&
      layout.ctorInfo.ssize == scalars && layout.fieldInfo.size == fields.size do
    throwError "native constructor shape changed for {name}"
  for i in [:fields.size] do
    let actual := match layout.fieldInfo[i]! with
      | .object slot _ => s!"o{slot}"
      | .scalar size offset _ => s!"s{size}@{offset}"
      | .usize slot => s!"u{slot}"
      | .erased => "erased"
      | .void => "void"
    unless actual == fields[i]! do
      throwError "native constructor field changed for {name} at {i}: {actual}"

run_meta do
  checkTags ``Hex.Groebner.MatrixState.Phase
    #["check","validate","workspace","input","scan","gather","order","done"]
  checkTags ``Hex.Groebner.Resource
    #["columns","rows","inputEntries","outputEntries","packedBytes","work","traceNodes"]
  checkTags ``Hex.Groebner.MatrixError
    #["dimensions","rowUpdate","rowLength","column","coefficient","exhausted"]
  checkCtor ``Hex.Groebner.MatrixError.dimensions 0 0 #[]
  checkCtor ``Hex.Groebner.MatrixError.rowUpdate 0 0 #[]
  checkCtor ``Hex.Groebner.MatrixError.rowLength 1 0 #["o0"]
  checkCtor ``Hex.Groebner.MatrixError.column 2 0 #["o0","o1"]
  checkCtor ``Hex.Groebner.MatrixError.coefficient 2 0 #["o0","o1"]
  checkCtor ``Hex.Groebner.MatrixError.exhausted 0 1 #["s1@0"]
  checkLayout ``Hex.Groebner.SparseRow 2 0 #[
    ("columns","o0"),("coefficients","o1")]
  checkLayout ``Hex.Groebner.RemainderRow 3 0 #[
    ("row","o0"),("derivation","o1"),("sugar","o2")]
  checkLayout ``Hex.Groebner.Echelon 3 0 #[
    ("rows","o0"),("reducerRank","o1"),("trace","o2")]
  checkLayout ``Hex.Groebner.Elimination.Result 2 0 #[
    ("result","o0"),("stats","o1")]
  checkLayout ``Hex.Groebner.Native.Scan.Result 5 1 #[
    ("state","o0"),("events","o1"),("work","o2"),("reductions","o3"),
    ("traceNodes","o4"),("status","s1@0")]
  checkLayout ``Hex.Groebner.Native.Gather.Result 4 1 #[
    ("state","o0"),("entries","o1"),("bytes","o2"),("work","o3"),("status","s1@0")]
  checkLayout ``Hex.Groebner.MatrixState.State 20 18 #[
    ("field","s8@0"),("limits","o0"),("columns","o1"),("reducers","o2"),
    ("targets","o3"),("sugars","o4"),("independent","s1@16"),("phase","s1@17"),
    ("validation","o5"),("input","o6"),("dense","o7"),("slots","o8"),
    ("pivots","o9"),("nativePivots","o10"),("remainders","o11"),("rank","o12"),
    ("scan","o13"),("gather","o14"),("leading","o15"),("sugar","o16"),
    ("inverse","s8@8"),("stats","o17"),("result","o18"),("quanta","o19")]
  checkLayout ``Hex.Groebner.Pivot 3 9 #[
    ("row","o0"),("fromTarget","s1@8"),("derivation","o1"),
    ("multiplier","s8@0"),("sugar","o2")]
  checkLayout ``Hex.Groebner.Native.Scan.State 8 8 #[
    ("dense","o0"),("column","o1"),("last","o2"),("chargedUntil","o3"),
    ("leading","o4"),("pending","o5"),("entry","o6"),("sugar","o7"),("factor","s8@0")]
  checkLayout ``Hex.Groebner.Native.Scan.Pivot 3 0 #[
    ("columns","o0"),("coefficients","o1"),("sugar","o2")]
  checkLayout ``Hex.Groebner.Native.Gather.State 4 0 #[
    ("dense","o0"),("columns","o1"),("coefficients","o2"),("cursor","o3")]
  checkLayout ``Hex.Groebner.MatrixStats 8 0 #[
    ("work","o0"),("inputEntries","o1"),("outputEntries","o2"),("packedBytes","o3"),
    ("traceNodes","o4"),("processedRows","o5"),("reductions","o6"),("zeroRows","o7")]
  checkLayout ``Hex.Groebner.MatrixLimits 7 0 #[
    ("columns","o0"),("rows","o1"),("inputEntries","o2"),("outputEntries","o3"),
    ("packedBytes","o4"),("work","o5"),("traceNodes","o6")]

-- A same-kind field permutation must be rejected by name, even when the
-- total object count and every scalar offset remain unchanged.
run_meta do
  let rejected ← try
    checkLayout ``Hex.Groebner.Pivot 3 9 #[
      ("derivation","o0"),("fromTarget","s1@8"),("row","o1"),
      ("multiplier","s8@0"),("sugar","o2")]
    pure false
  catch _ => pure true
  unless rejected do throwError "native layout checker accepted a same-kind field swap"
