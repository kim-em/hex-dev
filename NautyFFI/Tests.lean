/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Lean
import NautyFFI

/-!
# nauty-ffi fixture tests

Runs the FFI in process over the canonical labellings and forms committed by
the `hex-graph-iso` conformance corpus, then exercises the derived positive and
negative isomorphism paths on the named Petersen fixtures.
-/

namespace NautyFFI.Tests

open Lean

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def natField (json : Json) (name : String) : Except String Nat := do
  (← field json name).getNat?

private def stringField (json : Json) (name : String) : Except String String := do
  (← field json name).getStr?

private def natArray (json : Json) (name : String) : Except String (Array Nat) := do
  let values ← (← field json name).getArr?
  values.mapM Json.getNat?

private def graphOfJson (json : Json) : Except String NautyFFI.Graph := do
  let n ← natField json "n"
  let colorCount ← natField json "k"
  let colors ← natArray json "colors"
  if colors.size != n then
    throw s!"fixture has {colors.size} colours for n = {n}"
  let edgeValues ← (← field json "edges").getArr?
  let mut adjacency := Array.replicate n (Array.replicate n false)
  for edgeValue in edgeValues do
    let edge ← edgeValue.getArr?
    if edge.size != 2 then throw "fixture edge is not a pair"
    let left ← edge[0]!.getNat?
    let right ← edge[1]!.getNat?
    if left >= n || right >= n || left >= right then
      throw s!"fixture has invalid edge ({left}, {right})"
    adjacency := adjacency.set! left (adjacency[left]!.set! right true)
    adjacency := adjacency.set! right (adjacency[right]!.set! left true)
  return { colorCount, colors, adjacency }

private def boolArrayOfBits (bits : String) : Except String (Array Bool) := do
  let mut result := #[]
  for bit in bits.toList do
    match bit with
    | '0' => result := result.push false
    | '1' => result := result.push true
    | _ => throw s!"fixture canonical adjacency contains {repr bit}"
  return result

private def checkRecord (line : String) : Except String (String × NautyFFI.Graph) := do
  let json ← Json.parse line
  let caseName ← stringField json "case"
  let graph ← graphOfJson json
  let expectedLabelling ← natArray json "canonLab"
  let expectedCellSizes ← natArray json "cellSizes"
  let expectedAdjacency ← boolArrayOfBits (← stringField json "canonTri")
  let expected : NautyFFI.CanonResult :=
    { labelling := expectedLabelling
      form := { cellSizes := expectedCellSizes, adjacency := expectedAdjacency } }
  let actual ← NautyFFI.canonicalize graph
  if actual != expected then
    throw s!"{caseName}: expected {repr expected}, got {repr actual}"
  return (caseName, graph)

private def transports (left right : NautyFFI.Graph)
    (transporter : Array Nat) : Bool := Id.run do
  let n := left.colors.size
  if transporter.size != n then return false
  let mut seen := Array.replicate n false
  for vertex in [0:n] do
    let image := transporter[vertex]!
    if image >= n || seen[image]! || left.colors[vertex]! != right.colors[image]! then
      return false
    seen := seen.set! image true
  for i in [0:n] do
    for j in [0:n] do
      if left.adjacency[i]![j]! !=
          right.adjacency[transporter[i]!]![transporter[j]!]! then
        return false
  return true

private def checkIsomorphismCases (petersen kneser prism : NautyFFI.Graph) :
    Except String Unit := do
  let some transporter ← NautyFFI.findIso petersen kneser
    | throw "Petersen and Kneser presentations were reported non-isomorphic"
  if !transports petersen kneser transporter then
    throw "Petersen/Kneser transporter does not preserve colours and adjacency"
  if !(← NautyFFI.isIso petersen kneser) then
    throw "isIso rejected the Petersen/Kneser pair"
  if (← NautyFFI.findIso petersen prism).isSome then
    throw "Petersen graph and pentagonal prism were reported isomorphic"
  if ← NautyFFI.isIso petersen prism then
    throw "isIso accepted the Petersen graph/pentagonal prism pair"

/-- Run the vendored nauty binding over every committed graph-isomorphism
fixture and check the derived isomorphism API on named positive and negative
pairs. -/
def main : IO UInt32 := do
  let path := "conformance-fixtures/HexGraphIso/graphiso.jsonl"
  let contents ← IO.FS.readFile path
  let mut count := 0
  let mut petersen : Option NautyFFI.Graph := none
  let mut kneser : Option NautyFFI.Graph := none
  let mut prism : Option NautyFFI.Graph := none
  for line in contents.splitOn "\n" do
    if line.isEmpty then continue
    match checkRecord line with
    | .error error =>
        IO.eprintln s!"nauty-ffi tests: {error}"
        return 1
    | .ok (caseName, graph) =>
        count := count + 1
        if caseName == "named/petersen" then petersen := some graph
        if caseName == "named/kneser52" then kneser := some graph
        if caseName == "named/prism5" then prism := some graph
  match petersen, kneser, prism with
  | some petersenGraph, some kneserGraph, some prismGraph =>
      match checkIsomorphismCases petersenGraph kneserGraph prismGraph with
      | .error error =>
          IO.eprintln s!"nauty-ffi tests: {error}"
          return 1
      | .ok () => pure ()
  | _, _, _ =>
      IO.eprintln "nauty-ffi tests: named isomorphism fixtures are missing"
      return 1
  IO.println s!"nauty-ffi tests: {count} canonical forms and 2 isomorphism pairs passed"
  return 0

end NautyFFI.Tests

/-- Command-line entry point for the nauty-ffi fixture tests. -/
def main : IO UInt32 := NautyFFI.Tests.main
