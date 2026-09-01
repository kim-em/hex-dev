/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.TacticSupport
public import HexGraphIso.Tactic
public meta import HexGraphIsoMathlib.TacticSupport
public meta import HexGraphIso.Tactic
public meta import Lean

public section

/-!
# The `graph_iso` extension for `SimpleGraph` goals

Importing this library extends the existing `graph_iso` syntax — no
second tactic name — to closed ground `SimpleGraph` goals:

```
example : G ≃g H := by graph_iso
example : Nonempty (G ≃g H) := by graph_iso
example : IsEmpty (G ≃g H) := by graph_iso
example : ¬ Nonempty (G ≃g H) := by graph_iso
example : Colored.Iso CG CH := by graph_iso
example : Colored.Isomorphic CG CH := by graph_iso
example : IsEmpty (Colored.Iso CG CH) := by graph_iso
example : ¬ Colored.Isomorphic CG CH := by graph_iso
```

The reifier encodes both graphs along `Fintype.equivFin` and reuses the
Mathlib-free machinery: positive goals emit a literal transporter and
close through the kernel-replayed `checkIso?` and the decoding
theorems; negative goals kernel-replay the verified pairwise decision;
unequal cardinalities close immediately through `Fintype.card_congr`
obstructions, and empty vertex types through the explicit empty
isomorphism. The same three logical limits are accepted and are not
reinterpreted.
-/

namespace HexGraphIsoMathlib.Tactic

open Lean Elab Meta
open Hex.GraphIso Hex.GraphIso.Mathlib

private meta unsafe def evalNatUnsafe (e : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatUnsafe]
private meta opaque evalNatCore (e : Expr) : MetaM Nat

private meta unsafe def evalOptBoolUnsafe (e : Expr) : MetaM (Option Bool) :=
  evalExpr (Option Bool) (mkApp (mkConst ``Option [.zero]) (mkConst ``Bool)) e

@[implemented_by evalOptBoolUnsafe]
private meta opaque evalOptBoolCore (e : Expr) : MetaM (Option Bool)

/-- The supported goal shapes. Each carries the two graph expressions;
`colored` marks `Colored` goals, `negative` refuting shapes, `wrap`
whether a positive `Nonempty`/`Isomorphic` wrapper is required. -/
meta structure Shape where
  G : Expr
  H : Expr
  colored : Bool
  negative : Bool
  wrap : Bool
  /-- For negatives: build `¬ ·` (`true`) or `IsEmpty ·` (`false`). -/
  useNot : Bool := false

/-- Match a `SimpleGraph` isomorphism type `G ≃g H`. -/
meta def matchIsoType? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t ← whnfR t
  if t.isAppOfArity ``RelIso 4 then
    let args := t.getAppArgs
    let r := args[2]!
    let s := args[3]!
    if r.isAppOfArity ``SimpleGraph.Adj 2 ∧ s.isAppOfArity ``SimpleGraph.Adj 2 then
      return some (r.getAppArgs[1]!, s.getAppArgs[1]!)
    return none
  return none

/-- Match a `Colored.Iso` type. -/
meta def matchColoredIso? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t ← whnfR t
  if t.isAppOf ``Colored.Iso then
    let args := t.getAppArgs
    if h : args.size ≥ 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!)
  return none

/-- Match a `Colored.Isomorphic` proposition. -/
meta def matchColoredIsomorphic? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let t ← whnfR t
  if t.isAppOf ``Colored.Isomorphic then
    let args := t.getAppArgs
    if h : args.size ≥ 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!)
  return none

meta def parseGoal? (target : Expr) : MetaM (Option Shape) := do
  let t ← whnfR target
  match_expr t with
  | Nonempty inner =>
    match ← matchIsoType? inner with
    | some (G, H) =>
        return some { G := G, H := H, colored := false, negative := false, wrap := true }
    | none => return none
  | IsEmpty inner =>
    match ← matchIsoType? inner with
    | some (G, H) =>
        return some { G := G, H := H, colored := false, negative := true, wrap := false }
    | none =>
      match ← matchColoredIso? inner with
      | some (G, H) =>
          return some { G := G, H := H, colored := true, negative := true, wrap := false }
      | none => return none
  | Not p =>
    match_expr (← whnfR p) with
    | Nonempty inner =>
      match ← matchIsoType? inner with
      | some (G, H) =>
          return some
            { G := G, H := H, colored := false, negative := true
              wrap := false, useNot := true }
      | none => return none
    | _ =>
      match ← matchColoredIsomorphic? p with
      | some (G, H) =>
          return some
            { G := G, H := H, colored := true, negative := true
              wrap := false, useNot := true }
      | none => return none
  | _ =>
    match ← matchIsoType? target with
    | some (G, H) =>
        return some { G := G, H := H, colored := false, negative := false, wrap := false }
    | none =>
      match ← matchColoredIso? target with
      | some (G, H) =>
          return some { G := G, H := H, colored := true, negative := false, wrap := false }
      | none =>
        match ← matchColoredIsomorphic? target with
        | some (G, H) =>
            return some { G := G, H := H, colored := true, negative := false, wrap := true }
        | none => return none

/-- The vertex type of a graph expression (`SimpleGraph V` or
`Colored V k`). -/
meta def vertexType (colored : Bool) (g : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType g)
  if colored then
    return ty.getAppArgs[0]!
  else
    return ty.getAppArgs[0]!

/-- Elaboration data for one side of the goal. -/
meta structure Side where
  V : Expr
  instV : Expr
  cardTerm : Expr
  card : Nat
  equiv : Expr

meta def mkSide (colored : Bool) (g : Expr) : MetaM Side := do
  let V ← vertexType colored g
  let instV ← try
    synthInstance (← mkAppM ``Fintype #[V])
  catch _ =>
    throwError "graph_iso: failed to synthesize `Fintype {indentExpr V}`"
  let instEq ← try
    synthInstance (← mkAppM ``DecidableEq #[V])
  catch _ =>
    throwError "graph_iso: failed to synthesize `DecidableEq {indentExpr V}`"
  let cardTerm ← mkAppOptM ``Fintype.card #[V, instV]
  let card ← try
    evalNatCore cardTerm
  catch ex =>
    throwError "graph_iso: failed to evaluate the vertex cardinality of\
        {indentExpr V}\n{ex.toMessageData}"
  -- reduce the universal finset's multiset to a literal element list
  let univTerm ← mkAppOptM ``Finset.univ #[V, instV]
  let msTerm ← mkAppM ``Finset.val #[univTerm]
  let msVal ← withTransparency .default (Meta.reduce msTerm (skipProofs := true) (skipTypes := true))
  let lst ← do
    let fn := msVal.getAppFn
    let args := msVal.getAppArgs
    if fn.isConstOf ``Quot.mk ∧ args.size == 3 then
      pure args[2]!
    else
      throwError "graph_iso: could not reduce the vertex enumeration of\
          {indentExpr V}\nto a literal element list; the `Fintype` \
          instance may not reduce on this ground type (got \
          {indentExpr msVal})"
  let hlen ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``List.length #[lst], cardTerm])
  let hnodup ← mkDecideProof (← mkAppM ``List.Nodup #[lst])
  let complType ← withLocalDeclD `v V fun v => do
    mkForallFVars #[v] (← mkAppM ``Membership.mem #[lst, v])
  let hcompl ← mkDecideProof complType
  let equiv ← mkAppM ``listEquiv #[lst, hlen, hnodup, hcompl]
  return { V := V, instV := instV, cardTerm := cardTerm, card := card, equiv := equiv }

/-- Synthesize any trailing instance-implicit arguments left unapplied
by `mkAppM`. -/
meta def applyTrailingInstances (e : Expr) : MetaM Expr := do
  let mut e := e
  for _ in [0 : 4] do
    let ty ← whnfR (← inferType e)
    if ty.isForall ∧ ty.bindingInfo!.isInstImplicit then
      let inst ← synthInstance ty.bindingDomain!
      e := mkApp e inst
  return e

/-- The encoded executable graph term for one side, together with the
`0 < card` proof for uncoloured sides. -/
meta def encodeSide (colored : Bool) (g : Expr) (side : Side) :
    MetaM (Expr × Option Expr) := do
  if colored then
    let enc ← try
      applyTrailingInstances (← mkAppM ``encode #[side.equiv, g])
    catch ex =>
      throwError "graph_iso: failed to encode the coloured graph — the \
          adjacency relation may lack a `DecidableRel` \
          instance:{indentExpr g}\n{ex.toMessageData}"
    return (enc, none)
  else
    let posType ← mkAppM ``LT.lt #[mkNatLit 0, side.cardTerm]
    let hpos ← mkDecideProof posType
    let onecellG ← mkAppM ``onecell #[g, hpos]
    let enc ← try
      applyTrailingInstances (← mkAppM ``encode #[side.equiv, onecellG])
    catch ex =>
      throwError "graph_iso: failed to encode the graph — the adjacency \
          relation may lack a `DecidableRel` instance:{indentExpr g}\
          \n{ex.toMessageData}"
    return (enc, some hpos)

meta def proveShape (cfg : Hex.GraphIso.Tactic.Config) (target : Expr)
    (shape : Shape) : MetaM Expr := do
  let sG ← mkSide shape.colored shape.G
  let sH ← mkSide shape.colored shape.H
  let finish (proof : Expr) : MetaM Expr := do
    unless ← isDefEq (← inferType proof) target do
      throwError "graph_iso: internal final proof mismatch"
    instantiateMVars proof
  -- cardinality obstructions and the empty case
  if sG.card ≠ sH.card then
    if shape.negative then
      let neType ← mkAppM ``Ne #[sG.cardTerm, sH.cardTerm]
      let hne ← mkDecideProof neType
      let name :=
        if shape.colored then
          if shape.useNot then ``not_isomorphic_of_card_ne
          else ``isEmpty_coloredIso_of_card_ne
        else
          if shape.useNot then ``not_nonempty_iso_of_card_ne
          else ``isEmpty_iso_of_card_ne
      return ← finish (← mkAppM name #[shape.G, shape.H, hne])
    else
      throwError "graph_iso: the vertex types have cardinalities \
          {sG.card} and {sH.card}; the positive goal is not provable"
  if sG.card == 0 ∧ ¬ shape.negative then
    let z0 ← mkAppM ``Eq #[sG.cardTerm, mkNatLit 0]
    let z1 ← mkAppM ``Eq #[sH.cardTerm, mkNatLit 0]
    let h0 ← mkDecideProof z0
    let h1 ← mkDecideProof z1
    let core ← mkAppM
      (if shape.colored then ``coloredIsoOfCardZero else ``isoOfCardZero)
      #[shape.G, shape.H, h0, h1]
    let proof ← if shape.wrap then
        if shape.colored then
          mkAppM ``Colored.Isomorphic.intro #[core]
        else
          mkAppM ``Nonempty.intro #[core]
      else
        pure core
    return ← finish proof
  let (encG, hposG) ← encodeSide shape.colored shape.G sG
  let (encH, hposH) ← encodeSide shape.colored shape.H sH
  if shape.negative then
    let limitsE ← mkAppM ``SearchLimits.mk
      #[mkNatLit cfg.maxNodes, mkNatLit cfg.maxCertNodes]
    let decTerm ← mkAppM ``Pairwise.decideIso? #[limitsE, encG, encH]
    match ← evalOptBoolCore decTerm with
    | none =>
        throwError "graph_iso: search exhausted: the pairwise decision ran \
            out of nodes at maxNodes := {cfg.maxNodes}"
    | some true =>
        throwError "graph_iso: the graphs are isomorphic; the negative goal \
            is not provable"
    | some false =>
        let someFalse ← mkAppOptM ``Option.some
          #[mkConst ``Bool, mkConst ``Bool.false]
        let eqType ← mkAppM ``Eq #[decTerm, someFalse]
        let checked ← mkDecideProof eqType
        let proof ← if shape.colored then
            if shape.useNot then
              mkAppM ``not_isomorphic_of_decideIso?
                #[sG.equiv, sH.equiv, limitsE, checked]
            else
              mkAppM ``isEmpty_coloredIso_of_decideIso?
                #[sG.equiv, sH.equiv, limitsE, checked]
          else
            if shape.useNot then
              mkAppM ``not_nonempty_iso_of_decideIso?
                #[sG.equiv, sH.equiv, hposG.get!, hposH.get!, limitsE, checked]
            else
              mkAppM ``isEmpty_iso_of_decideIso?
                #[sG.equiv, sH.equiv, hposG.get!, hposH.get!, limitsE, checked]
        return ← finish proof
  else
    let a ← Hex.GraphIso.Tactic.evalColored encG
    let b ← Hex.GraphIso.Tactic.evalColored encH
    let (transporter?, nodes) := Hex.GraphIso.Tactic.rawFindIso a b
    if nodes > cfg.maxNodes then
      throwError "graph_iso: search exhausted: visited {nodes} nodes but \
          maxNodes := {cfg.maxNodes}"
    match transporter? with
    | none =>
        throwError "graph_iso: the graphs are not isomorphic; the positive \
            goal is not provable"
    | some p =>
        if Hex.GraphIso.checkCost sG.card > cfg.maxCheckerSteps then
          throwError "graph_iso: replay exhausted: checking the transporter \
              takes {Hex.GraphIso.checkCost sG.card} steps but \
              maxCheckerSteps := {cfg.maxCheckerSteps}"
        let pE ← Hex.GraphIso.Tactic.permExpr sG.card p
        let replayE ← mkAppM ``ReplayLimits.mk #[mkNatLit cfg.maxCheckerSteps]
        let checkTerm ← mkAppM ``checkIso? #[replayE, encG, encH, pE]
        let someTrue ← mkAppOptM ``Option.some
          #[mkConst ``Bool, mkConst ``Bool.true]
        let eqType ← mkAppM ``Eq #[checkTerm, someTrue]
        let checked ← mkDecideProof eqType
        let core ← if shape.colored then
            mkAppM ``coloredIsoOfCheckIso?
              #[sG.equiv, sH.equiv, replayE, pE, checked]
          else
            mkAppM ``isoOfCheckIso?
              #[sG.equiv, sH.equiv, hposG.get!, hposH.get!, replayE, pE, checked]
        let proof ← if shape.wrap then
            if shape.colored then
              mkAppM ``Colored.Isomorphic.intro #[core]
            else
              mkAppM ``Nonempty.intro #[core]
          else
            pure core
        return ← finish proof

/-- The `graph_iso` extension for `SimpleGraph` goals. -/
public meta def extension : Hex.GraphIso.Tactic.Extension where
  prove? cfg target := do
    match ← parseGoal? target with
    | none => return none
    | some shape => return some (← proveShape cfg target shape)

end HexGraphIsoMathlib.Tactic
