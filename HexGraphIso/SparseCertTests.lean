/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Complete
public import HexGraphIso.Nauty.Sparse.Literal.Canon
public import HexGraphIso.Nauty.Sparse.Literal.Compact
public import HexGraphIso.Nauty.Sparse.Cert.Records
public import HexGraphIso.SparseKernelTests
public import HexGraphIso.SparseTestGraphs
public meta import HexGraphIso.SparseKernelTests
public meta import HexGraphIso.Nauty.Sparse.Cert.CompactCanon

open Hex Hex.GraphIso
open Nauty Nauty.Sparse

private def path : Sparse.Colored 3 1 :=
  ⟨SparseGraph.ofEdges [(0, 1), (1, 2)], Coloring.trivial 3⟩

private def pathKey : Nauty.Sparse.Key 3 :=
  ⟨[58, 27425, 32767], SparseGraph.ofEdges [(0, 2), (1, 2)]⟩

private def pathCert : Nauty.Sparse.CertNode := .node [.leaf, .leaf]

example : Literal.checkKey path pathCert pathKey = true := by sparse_kernel_decide

example : canonSpecKey path = pathKey := Literal.checkKey_sound (cert := pathCert) (by sparse_kernel_decide)

example : Literal.checkKey path (.node [.leaf]) pathKey = false := by sparse_kernel_decide

example : Literal.checkKey path (.node [.leaf, .leaf, .leaf]) pathKey = false := by sparse_kernel_decide

example : Literal.checkKey path .leaf pathKey = false := by sparse_kernel_decide

example : Literal.checkKey path pathCert { pathKey with codes := [58, 27425, 0] } = false := by
  sparse_kernel_decide

example : (Literal.checkCanon path ⟨pathCert, pathKey, #[0, 2, 1]⟩).isSome = true := by
  sparse_kernel_decide

example : (Literal.checkCanon path ⟨pathCert, pathKey, #[2, 0, 1]⟩).isSome = true := by
  sparse_kernel_decide

-- A bijection that does not attain the claimed graph, and malformed labels.
example : (Literal.checkCanon path ⟨pathCert, pathKey, #[0, 1, 2]⟩).isSome = false := by
  sparse_kernel_decide

example : (Literal.checkCanon path ⟨pathCert, pathKey, #[0, 2]⟩).isSome = false := by
  sparse_kernel_decide

example : (Literal.checkCanon path ⟨pathCert, pathKey, #[0, 2, 2]⟩).isSome = false := by
  sparse_kernel_decide

example : (Literal.checkCanon path ⟨pathCert, pathKey, #[0, 3, 1]⟩).isSome = false := by
  sparse_kernel_decide

-- The second endpoint branch is justified by the actual endpoint swap.
example : Literal.Compact.checkKey path (.node [.leaf, .autom 0 #[2, 1, 0]]) pathKey = true := by
  sparse_kernel_decide

-- References must be strictly earlier and transport the whole child partition.
example : Literal.Compact.checkKey path (.node [.leaf, .autom 1 #[2, 1, 0]]) pathKey = false := by
  sparse_kernel_decide

example : Literal.Compact.checkKey path (.node [.autom 1 #[2, 1, 0], .leaf]) pathKey = false := by
  sparse_kernel_decide

example : Literal.Compact.checkKey path (.node [.leaf, .autom 0 #[0, 1, 2]]) pathKey = false := by
  sparse_kernel_decide

example : Literal.Compact.checkKey path (.node [.leaf, .autom 0 #[1, 0, 2]]) pathKey = false := by
  sparse_kernel_decide

example : Literal.Compact.checkKey path (.node [.leaf, .autom 0 #[2, 1, 2]]) pathKey = false := by
  sparse_kernel_decide

example : Literal.Compact.checkKey path (.autom 0 #[2, 1, 0]) pathKey = false := by
  sparse_kernel_decide

example : (Literal.Compact.checkCanon path
    ⟨.node [.leaf, .autom 0 #[2, 1, 0]], pathKey, #[0, 2, 1]⟩).isSome = true := by
  sparse_kernel_decide

-- The compiled producer actually emits the compact branch and its complete
-- result passes replay. These guards exercise the producer's witness path.
#guard match Compact.produceCand path with
  | some ⟨.node [.leaf, .autom 0 _], _, _⟩ => true
  | _ => false

#guard (Compact.certifyCanon? path).isSome

example : Literal.Compact.checkRecords? 0 path pathCert pathKey = none := by sparse_kernel_decide

example : Literal.Compact.checkRecords? 2 path pathCert pathKey = none := by sparse_kernel_decide

example : Literal.Compact.checkRecords? 3 path pathCert pathKey = some true := by sparse_kernel_decide

example : Literal.Compact.checkRecords? 3 path
    (.node [.leaf, .autom 0 #[2, 1, 0]]) pathKey = some true := by sparse_kernel_decide

example : Literal.Compact.checkRecords? 3 path
    (.node [.leaf, .autom 1 #[2, 1, 0]]) pathKey = some false := by sparse_kernel_decide

private def randomKey : Nauty.Sparse.Key 12 :=
  ⟨[1819, 32767], SparseGraph.ofEdges [
    (0, 6), (0, 7), (0, 8), (1, 3), (1, 4), (1, 9), (1, 10),
    (2, 3), (2, 4), (2, 10), (2, 11), (3, 6), (3, 7), (3, 9),
    (4, 5), (4, 9), (4, 10), (5, 8), (5, 9), (5, 10), (5, 11),
    (6, 7), (6, 10), (6, 11), (7, 8), (7, 11), (8, 9), (8, 11),
    (9, 11), (10, 11)]⟩

private def randomKeyB : Nauty.Sparse.Key 12 :=
  ⟨[27524, 32767], SparseGraph.ofEdges [
    (0, 7), (0, 8), (0, 10), (0, 11), (1, 6), (1, 7), (1, 9),
    (1, 10), (2, 3), (2, 6), (2, 9), (2, 11), (3, 6), (3, 9),
    (3, 10), (3, 11), (4, 5), (4, 7), (4, 8), (4, 10), (4, 11),
    (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 7), (6, 8),
    (6, 10), (6, 11), (7, 8), (7, 9), (7, 11), (8, 9), (8, 10),
    (8, 11), (9, 10), (9, 11), (10, 11)]⟩

set_option maxRecDepth 100000 in
private theorem randomCheck : Literal.checkKey SparseTestGraphs.random12 .leaf randomKey = true := by
  sparse_kernel_decide

set_option maxRecDepth 100000 in
private theorem randomCheckB : Literal.checkKey SparseTestGraphs.random12b .leaf randomKeyB = true := by
  sparse_kernel_decide

example : ¬ Sparse.Isomorphic SparseTestGraphs.random12 SparseTestGraphs.random12b :=
  Literal.not_isomorphic_of_checkKeys randomCheck randomCheckB (by sparse_kernel_decide)
