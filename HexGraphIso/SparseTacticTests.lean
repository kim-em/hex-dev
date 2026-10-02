/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso
public import HexGraphIso.SparseTestGraphs
public meta import HexGraphIso.Sparse.Tactic
public meta import HexGraphIso.SparseTestGraphs

open Hex Hex.GraphIso

-- Public dispatch must replay imported native sparse graphs in the kernel.

example : Sparse.Isomorphic SparseTestGraphs.empty SparseTestGraphs.empty := by
  graph_iso

set_option maxRecDepth 100000 in
example : Sparse.Isomorphic SparseTestGraphs.edgeMarkA SparseTestGraphs.edgeMarkB := by
  graph_iso

set_option maxRecDepth 100000 in
example : ¬ Sparse.Isomorphic SparseTestGraphs.edgeMarkA SparseTestGraphs.nonedgeMark := by
  graph_iso

set_option maxRecDepth 100000 in
example : Sparse.Isomorphic SparseTestGraphs.random12 SparseTestGraphs.random12relabeled := by
  graph_iso

set_option maxRecDepth 100000 in
example : ¬ Sparse.Isomorphic SparseTestGraphs.random12 SparseTestGraphs.random12b := by
  graph_iso

example : SparseGraph.Isomorphic SparseTestGraphs.empty.graph SparseTestGraphs.empty.graph := by
  graph_iso

example : SparseGraph.Isomorphic (SparseGraph.empty 1) (SparseGraph.empty 1) := by
  graph_iso

set_option maxRecDepth 100000 in
example : SparseGraph.Isomorphic SparseTestGraphs.random12.graph
    SparseTestGraphs.random12relabeled.graph := by
  fail_if_success graph_iso (maxSearchNodes := 0)
  graph_iso

set_option maxRecDepth 100000 in
example : ¬ SparseGraph.Isomorphic SparseTestGraphs.random12.graph
    SparseTestGraphs.random12b.graph := by
  fail_if_success graph_iso (maxSearchNodes := 0)
  fail_if_success graph_iso (maxCertRecords := 0)
  graph_iso

/-- error: graph_iso: both sparse graphs must be closed terms without metavariables -/
#guard_msgs in
example (G : Sparse.Colored 3 1) : Sparse.Isomorphic G G := by graph_iso
