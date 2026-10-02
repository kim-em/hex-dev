/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexGraph.Sparse.Relabel
import HexGraphIso.Perm
import HexGraphIso.Nauty.Sparse.Search
import Lean.Data.Json

/-! JSONL differential driver for the sparse dispatch. The search mode uses
the native checked edge constructor and independently checks the raw canonical
store against relabelling by the returned permutation. -/

open Lean Hex.GraphIso Hex.GraphIso.Nauty
namespace Hex.GraphIso.SparseProbe

private def graph (j : Json) : Except String (Σ n, Hex.SparseGraph n) := do
  let n ← j.getObjValAs? Nat "n"
  let edges ← j.getObjValAs? (List (Nat × Nat)) "edges"
  let some g := Hex.SparseGraph.ofEdges? n edges | throw "invalid sparse edges"
  return ⟨n, g⟩

def evaluate (j : Json) : Except String Json := do
  let mode := (j.getObjValAs? String "mode").toOption.getD "search"
  if mode == "sort" then
    return toJson (Sparse.Sort.indirect
      (← j.getObjValAs? (Array Nat) "x") (← j.getObjValAs? (Array Nat) "y")
      (← j.getObjValAs? Nat "start") (← j.getObjValAs? Nat "len"))
  let ⟨n, g⟩ ← graph j
  let raw := Sparse.Graph.ofGraph g
  if mode == "refine" then
    let lab ← j.getObjValAs? (Array Nat) "lab"
    let ptn ← j.getObjValAs? (Array Nat) "ptn"
    let level ← j.getObjValAs? Nat "level"
    let numcells ← j.getObjValAs? Nat "numcells"
    let active ← j.getObjValAs? (Array Nat) "active"
    let r := Sparse.refine raw level lab ptn
      (active.foldl (fun s v => s.insert v) (VSet.empty : VSet n)) numcells
    if r.numcells < n then
      let target := Sparse.maketargetcell raw r.lab r.ptn level 100 (-1)
      let (first, cell, size, _) := Sparse.maketargetCached raw r.lab r.ptn level 100 (-1) r.toScratch
      unless (first, cell, size) == target do
        throw "cached target differs from independent partition scan"
    return Json.mkObj [("lab", toJson r.lab), ("ptn", toJson r.ptn),
      ("active", toJson ((Array.range n).filter r.active.mem)),
      ("numcells", toJson r.numcells), ("code", toJson r.longcode),
      ("target", toJson (Sparse.targetcell raw r.lab r.ptn level 100 (-1)))]
  unless mode == "search" do throw s!"unknown mode: {mode}"
  let k ← j.getObjValAs? Nat "k"
  let colors ← j.getObjValAs? (Array Nat) "colors"
  unless colors.size == n && colors.all (· < k) &&
      (Array.range k).all colors.contains do throw "invalid ordered colouring"
  let (lab, ends) := Sparse.initialPartition n k colors
  let (exit, state) := Sparse.runState raw lab ends
  if let .fuel := exit then throw "sparse search exhausted its structural bound"
  let r := Sparse.finish raw state
  let some label := Label.ofArray? n r.canonlab | throw "invalid canonical label"
  let canonical := g.relabel label.perm
  let canonEdges := canonical.edges.map fun (a, b) => (a.val, b.val)
  let rawRows := (Array.range n).map fun i =>
    (r.canong.neighbors.extract r.canong.offsets[i]! r.canong.offsets[i + 1]!).toList
  let expected := (List.finRange n).toArray.map fun i =>
    (canonical.nbrs i).toList.map Fin.val
  unless rawRows.map (fun row => Hex.List.sort row (· ≤ ·)) == expected do
    throw "raw canonical store differs from relabelled graph"
  let sizes := colors.foldl (fun a c => a.set! c (a[c]! + 1)) (Array.replicate k 0)
  return Json.mkObj [
    ("kind", toJson "graphisosparseautos"), ("lib", toJson "HexGraphIso"),
    ("case", toJson ((j.getObjValAs? String "case").toOption.getD "probe")),
    ("n", toJson n), ("k", toJson k), ("colors", toJson colors),
    ("edges", toJson (g.edges.map fun (a, b) => (a.val, b.val))),
    ("canonLab", toJson r.canonlab),
    ("canonEdges", toJson canonEdges), ("cellSizes", toJson sizes),
    ("numnodes", toJson r.numnodes), ("gens", toJson r.genTrace),
    ("numGenerators", toJson r.numgenerators), ("orbits", toJson r.orbits),
    ("numOrbits", toJson r.numorbits), ("order", toJson r.order),
    ("stats", Json.mkObj [("numnodes", toJson r.numnodes),
      ("numorbits", toJson r.numorbits), ("numgenerators", toJson r.numgenerators),
      ("numbadleaves", toJson r.numbadleaves), ("maxlevel", toJson r.maxlevel),
      ("tctotal", toJson r.tctotal), ("canupdates", toJson r.canupdates)])]

end Hex.GraphIso.SparseProbe
