/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.TacticSupport
public import HexGraphIso.Sparse.UncoloredOps
public meta import HexGraphIso.Sparse.TacticSupport
public meta import HexGraphIso.Sparse.UncoloredOps
public meta import Lean

public section

namespace Hex.GraphIso.Sparse.Tactic

open Lean Meta
open GraphIso.Tactic (Extension)

/-- Prove a closed coloured sparse goal with the native bounded search and
literal kernel replay. Search exhaustion supplies no isomorphism verdict. -/
meta def proveColored (cfg : GraphIso.Tactic.Config) (negative : Bool) (GE HE : Expr) : MetaM Expr := do
  if GE.hasFVar || HE.hasFVar || GE.hasMVar || HE.hasMVar then
    throwError "graph_iso: both sparse graphs must be closed terms without metavariables"
  let ty ← whnfR (← inferType GE)
  unless ty.isAppOfArity ``Colored 2 do
    throwError "graph_iso: expected native sparse coloured graphs"
  let args := ty.getAppArgs
  let n ← evalNat args[0]!
  let k ← evalNat args[1]!
  let G ← evalColored n k GE
  let H ← evalColored n k HE
  if negative then
    let (a, b) ← match findCandidates cfg.maxSearchNodes cfg.maxCertRecords G H with
      | .ok pair => pure pair
      | .error message => throwError "graph_iso: {message}"
    proveDifferent GE HE G H a b
  else
    let some (witness, nodes) := findWitness cfg.maxSearchNodes G H
      | throwError "graph_iso: sparse search exhausted maxSearchNodes := {cfg.maxSearchNodes}"
    let some p := witness
      | throwError "graph_iso: the sparse graphs are not isomorphic; the positive goal is not provable"
    trace[graph_iso] "sparse search nodes={nodes}"
    proveWitness GE HE G H p

/-- Bare sparse graphs use the zero-or-one-colour view, which also covers
order zero. The correspondence theorem transports either proof direction. -/
meta def proveBare (cfg : GraphIso.Tactic.Config) (negative : Bool) (GE HE : Expr) : MetaM Expr := do
  let GC ← mkAppM ``Hex.SparseGraph.toColored #[GE]
  let HC ← mkAppM ``Hex.SparseGraph.toColored #[HE]
  let corr ← mkAppM ``Hex.SparseGraph.isomorphic_toColored_iff #[GE, HE]
  let proof ← proveColored cfg negative GC HC
  if negative then mkAppM ``mt #[← mkAppM ``Iff.mpr #[corr], proof]
  else mkAppM ``Iff.mp #[corr, proof]

/-- Extend the existing tactic on precisely the native sparse goal shapes.
The dense and Mathlib handlers retain their existing dispatch. -/
@[graph_iso_extension] meta def extension : Extension where
  prove? cfg target := do
    let target ← instantiateMVars target
    let t ← whnfR target
    let negative := t.isAppOf ``Not
    let iso ← whnfR (if negative then t.appArg! else t)
    let proof ← if iso.isAppOfArity ``Isomorphic 4 then
      let a := iso.getAppArgs
      proveColored cfg negative a[2]! a[3]!
    else if iso.isAppOfArity ``Hex.SparseGraph.Isomorphic 3 then
      let a := iso.getAppArgs
      proveBare cfg negative a[1]! a[2]!
    else return none
    unless ← isDefEq (← inferType proof) target do
      throwError "graph_iso: internal sparse proof mismatch"
    return some proof

end Hex.GraphIso.Sparse.Tactic
