/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Tactic
public import HexGraphIso.Sparse.Kernel
public import HexGraphIso.Nauty.Sparse.Cert.Records
public import HexGraphIso.Nauty.Sparse.Cert.LimitComplete
public import HexGraph.Sparse.Build
public meta import HexGraphIso.Tactic
public meta import HexGraphIso.Nauty.Sparse.Cert.CompactCanon
public meta import HexGraphIso.Nauty.Sparse.Literal.Compact
public meta import HexGraphIso.Nauty.Sparse.Limited
public meta import HexGraphIso.Nauty.Sparse.Cert.Limited
public meta import HexGraphIso.Sparse.Kernel
public meta import Lean

public section

namespace Hex.GraphIso.Sparse.Tactic

open Lean Meta
open GraphIso.Tactic (kernelDecideProof permExpr)

private meta unsafe def evalNatUnsafe (e : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatUnsafe]
meta opaque evalNat (e : Expr) : MetaM Nat

private meta unsafe def evalColoredUnsafe (n k : Nat) (e : Expr) : MetaM (Colored n k) :=
  evalExpr (Colored n k) (mkApp2 (mkConst ``Colored) (mkNatLit n) (mkNatLit k)) e

@[implemented_by evalColoredUnsafe]
private meta opaque evalColoredCore (n k : Nat) (e : Expr) : MetaM (Colored n k)

/-- Evaluate a closed native sparse graph without constructing dense rows.
All evaluated data are untrusted until the emitted kernel proof checks them. -/
meta def evalColored (n k : Nat) (e : Expr) : MetaM (Colored n k) := do
  try evalColoredCore n k e
  catch ex =>
    throwError "graph_iso: failed to evaluate the native sparse graph{indentExpr e}\n\
      {ex.toMessageData}\nThe graph must be a closed executable term; imported \
      definitions may need `public meta import`."

/-- Propose a transporter using two native searches sharing one node quota.
The outer `none` reports exhaustion; it supplies no isomorphism verdict.
The returned count is the actual combined number of admitted native visits. -/
meta def findWitness (maxNodes : Nat) (G H : Colored n k) : Option (Option (Perm n) × Nat) := do
  let (sa, sb) ← Nauty.Sparse.Limited.runPair? maxNodes G H
  let a := sa.value
  let b := sb.value
  let witness := do
    let la ← Label.ofArray? n a.canonlab
    let lb ← Label.ofArray? n b.canonlab
    let p := lb.toPerm.inv.comp la.toPerm
    if Sparse.checkIso G H p then some p else none
  return (witness, a.numnodes + b.numnodes)

/-- Propose two compact certificates with a shared search quota and a
record cap on each certificate. Exhaustion names the failed phase; only
subsequent kernel replay can turn the candidates into a negative proof. -/
meta def findCandidates (maxNodes maxRecords : Nat) (G H : Colored n k) :
    Except String (Nauty.Sparse.CertCandidate n × Nauty.Sparse.CertCandidate n) := do
  let some (sa, sb) := Nauty.Sparse.Limited.runPair? maxNodes G H
    | throw s!"search exhausted: maxSearchNodes := {maxNodes}"
  let some (a, _) := Nauty.Sparse.Compact.candidate? maxRecords G sa.value
    | throw s!"left certificate production failed or exhausted maxCertRecords := {maxRecords}"
  let some (b, _) := Nauty.Sparse.Compact.candidate? maxRecords H sb.value
    | throw s!"right certificate production failed or exhausted maxCertRecords := {maxRecords}"
  return (a, b)

/-- Prove equality with a literal through the kernel, without an elaborator
evaluation of the equality's decidable instance. -/
meta def tie (lhs rhs : Expr) : MetaM Expr := do
  kernelDecideProof (← mkAppM ``Eq #[lhs, rhs])

private meta def colorsSide (k : Nat) (e : Expr) : MetaM Expr := do
  let cells ← mkAppM ``Coloring.cells #[← mkAppM ``Colored.coloring #[e]]
  let vals ← mkAppM ``Vector.toList #[cells]
  let finVal ← mkAppOptM ``Fin.val #[some (mkNatLit k)]
  mkAppM ``List.map #[finVal, vals]

/-- Replay an explicit forward transporter on identified sparse row, colour
and permutation literals. The decisive theorem checks edges through sorted
neighbour images and never materializes a dense adjacency matrix. -/
meta def proveIsIso (GE HE : Expr) (G H : Colored n k)
    (p : Perm n) : MetaM (Expr × Expr) := do
  let rowsA := Kernel.rows G.graph
  let rowsB := Kernel.rows H.graph
  let cellsA := G.coloring.cells.toList.map Fin.val
  let cellsB := H.coloring.cells.toList.map Fin.val
  let images := p.vec.toList.map Fin.val
  unless Kernel.checkIso n rowsA rowsB cellsA cellsB images do
    throwError "graph_iso: the proposed sparse transporter failed checking"
  let pE ← permExpr n images.toArray
  let rowSide (e : Expr) := do mkAppM ``Kernel.rows #[← mkAppM ``Colored.graph #[e]]
  let hA ← tie (← rowSide GE) (toExpr rowsA)
  let hB ← tie (← rowSide HE) (toExpr rowsB)
  let hcA ← tie (← colorsSide k GE) (toExpr cellsA)
  let hcB ← tie (← colorsSide k HE) (toExpr cellsB)
  let permList ← mkAppM ``Vector.toList #[← mkAppM ``Perm.vec #[pE]]
  let finVal ← mkAppOptM ``Fin.val #[some (mkNatLit n)]
  let hp ← tie (← mkAppM ``List.map #[finVal, permList]) (toExpr images)
  let check ← mkAppM ``Kernel.checkIso #[mkNatLit n, toExpr rowsA, toExpr rowsB,
    toExpr cellsA, toExpr cellsB, toExpr images]
  let hc ← tie check (mkConst ``Bool.true)
  trace[graph_iso] "route=sparse-witness n={n}"
  return (pE, ← mkAppM ``Kernel.isIso_of_checkIso #[hA, hB, hcA, hcB, hp, hc])

/-- Wrap the checked explicit transporter as native sparse isomorphism. -/
meta def proveWitness (GE HE : Expr) (G H : Colored n k)
    (p : Perm n) : MetaM Expr := do
  let (pE, hp) ← proveIsIso GE HE G H p
  mkAppM ``Isomorphic.intro #[pE, hp]

/-- Reify a sparse graph as checked undirected edge literals. The default
empty graph only makes parsing total; kernel replay still checks the key. -/
meta def graphExpr (G : SparseGraph n) : MetaM Expr := do
  let edges := (List.finRange n).flatMap fun i =>
    (G.nbrs i).toList.filterMap fun j =>
      if i.val < j.val then some (i.val, j.val) else none
  let parsed ← mkAppM ``SparseGraph.ofEdges? #[mkNatLit n, toExpr edges]
  let finType := mkApp (mkConst ``Fin) (mkNatLit n)
  let pairType ← mkAppM ``Prod #[finType, finType]
  let empty ← mkAppOptM ``SparseGraph.ofEdges
    #[some (mkNatLit n), some (← mkListLit pairType [])]
  mkAppM ``Option.getD #[parsed, empty]

meta def keyExpr (B : Nauty.Sparse.Key n) : MetaM Expr := do
  mkAppM ``Nauty.Sparse.Key.mk #[toExpr B.codes, ← graphExpr B.graph]

/-- Preserve all sparse certificate records and their literal payloads. -/
meta partial def certExpr : Nauty.Sparse.CertNode → MetaM Expr
  | .leaf => return mkConst ``Nauty.Sparse.CertNode.leaf
  | .codePrune => return mkConst ``Nauty.Sparse.CertNode.codePrune
  | .autom earlier images =>
    return mkApp2 (mkConst ``Nauty.Sparse.CertNode.autom) (mkNatLit earlier) (toExpr images)
  | .node cs => do
    let children ← cs.mapM certExpr
    return mkApp (mkConst ``Nauty.Sparse.CertNode.node)
      (← mkListLit (mkConst ``Nauty.Sparse.CertNode) children)

private meta def keyProof (GE : Expr) (c : Nauty.Sparse.CertCandidate n) :
    MetaM (Expr × Expr) := do
  let B ← keyExpr c.key
  let check ← mkAppM ``Nauty.Sparse.Literal.Compact.checkKey #[GE, ← certExpr c.tree, B]
  return (B, ← tie check (mkConst ``Bool.true))

/-- Reify and replay an untrusted compact key certificate. A failed check
supplies no canonical-key proof. -/
meta def proveKey (GE : Expr) (G : Colored n k)
    (c : Nauty.Sparse.CertCandidate n) : MetaM (Expr × Expr) := do
  unless Nauty.Sparse.Literal.Compact.checkKey G c.tree c.key do
    throwError "graph_iso: the proposed sparse canonical certificate failed replay"
  keyProof GE c

/-- Two accepted different canonical keys give a native sparse negative
proof. All graph and certificate data in the proof term undergo kernel replay. -/
meta def proveDifferent (GE HE : Expr) (G H : Colored n k)
    (a b : Nauty.Sparse.CertCandidate n) : MetaM Expr := do
  unless Nauty.Sparse.checkDiff a.key b.key do
    throwError "graph_iso: the sparse canonical keys agree; this certificate pair does not separate the graphs"
  unless Nauty.Sparse.Literal.Compact.checkKey G a.tree a.key &&
      Nauty.Sparse.Literal.Compact.checkKey H b.tree b.key do
    throwError "graph_iso: the proposed sparse canonical certificate failed replay"
  let (aE, ha) ← keyProof GE a
  let (bE, hb) ← keyProof HE b
  let hd ← tie (← mkAppM ``Nauty.Sparse.checkDiff #[aE, bE]) (mkConst ``Bool.true)
  trace[graph_iso] "route=sparse-certs n={n} recordsG={a.tree.stats.records} \
    recordsH={b.tree.stats.records}"
  mkAppM ``Nauty.Sparse.Literal.Compact.not_isomorphic_of_checkKeys #[ha, hb, hd]

end Hex.GraphIso.Sparse.Tactic
