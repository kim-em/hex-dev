/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.AutCertificate
public import HexPermGroupMathlib.Tactic
public meta import HexGraphIsoMathlib.AutCertificate
public meta import HexGraphIsoMathlib.Tactic
public meta import HexPermGroupMathlib.Tactic
public meta import Lean

public section

/-!
# The `graph_aut` tactic

`graph_aut` certifies the full automorphism group of a closed explicit graph.
Compiled code searches for graph and permutation-group certificates; kernel
evaluation checks both before the cardinality sandwich is applied.
-/

namespace HexGraphIsoMathlib.AutTactic

open Lean Elab Meta Lean.Elab.Tactic
open Hex Hex.GraphIso Hex.GraphIso.Mathlib

meta initialize registerTraceClass `graph_aut

/-- Resource limits for one `graph_aut` call. -/
meta structure Config where
  /-- Search nodes allowed for each canonical-key certificate. -/
  maxSearchNodes : Nat := 100000
  /-- Total canonical-certificate records allowed in the graph certificate. -/
  maxCertRecords : Nat := 100000
  /-- Estimated kernel work in each permutation-group checker chunk. -/
  maxChunkWork : Nat := 600000

meta section

declare_config_elab elabGraphAutConfig Config

end

private meta unsafe def evalCertUnsafe (e : Expr) :
    MetaM (Option Aut.Kernel.Certificate) :=
  evalExpr (Option Aut.Kernel.Certificate)
    (mkApp (mkConst ``Option [0]) (mkConst ``Aut.Kernel.Certificate)) e

@[implemented_by evalCertUnsafe]
private meta opaque evalCertCore (e : Expr) :
    MetaM (Option Aut.Kernel.Certificate)

private meta unsafe def evalGensUnsafe (n : Nat) (e : Expr) : MetaM (List (Perm n)) :=
  evalExpr (List (Perm n))
    (mkApp (mkConst ``List [0]) (mkApp (mkConst ``Hex.Perm) (mkNatLit n))) e

@[implemented_by evalGensUnsafe]
private meta opaque evalGensCore (n : Nat) (e : Expr) : MetaM (List (Perm n))

private meta def keyCertExpr (c : Aut.Kernel.KeyCert) : MetaM Expr := do
  return mkApp2 (mkConst ``Aut.Kernel.KeyCert.mk)
    (← Hex.GraphIso.Tactic.certNodeExpr c.cert)
    (Hex.GraphIso.Tactic.keyExpr c.key)

private meta def separationExpr (s : Aut.Kernel.Separation) : MetaM Expr := do
  return mkApp2 (mkConst ``Aut.Kernel.Separation.mk) (mkNatLit s.vertex)
    (← keyCertExpr s.witness)

private meta def levelExpr (L : Aut.Kernel.Level) : MetaM Expr := do
  let orbit ← Hex.PermGroup.Kernel.Tactic.natListLit L.orbit
  let excluded ← L.excluded.mapM separationExpr
  let excluded ← mkListLit (mkConst ``Aut.Kernel.Separation) excluded
  return mkAppN (mkConst ``Aut.Kernel.Level.mk)
    #[mkNatLit L.base, orbit, ← keyCertExpr L.reference, excluded]

private meta def certificateRecords : Aut.Kernel.Certificate → Nat
  | .done => 0
  | .step L rest =>
      L.reference.cert.size +
        L.excluded.foldl (fun total e => total + e.witness.cert.size) 0 +
        certificateRecords rest

private meta def certificateLevels : Aut.Kernel.Certificate → Nat
  | .done => 0
  | .step _ rest => 1 + certificateLevels rest

private meta def certificateList : Aut.Kernel.Certificate → List Aut.Kernel.Level
  | .done => []
  | .step L rest => L :: certificateList rest

private meta def permExpr (n : Nat) (p : Perm n) : MetaM Expr := do
  let images := (List.finRange n).map fun i => (p.get i).val
  mkAppM ``Hex.PermGroup.Kernel.permOfImages
    #[mkNatLit n, ← Hex.PermGroup.Kernel.Tactic.natListLit images]

private meta def addDecideProof (suffix : String) (p : Expr) : TacticM Expr := do
  let inst ← synthInstance (← mkAppM ``Decidable #[p])
  let lhs := mkApp2 (mkConst ``Decidable.decide) p inst
  let h ← Hex.PermGroup.Kernel.Tactic.addKernelEq
    (← Hex.PermGroup.Kernel.Tactic.auxName suffix) lhs (mkConst ``Bool.true)
  return mkApp3 (mkConst ``of_decide_eq_true) p inst h

private meta def addProof (suffix : String) (type value : Expr) : TacticM Expr := do
  let name ← Hex.PermGroup.Kernel.Tactic.auxName suffix
  addDecl <| .thmDecl { name, levelParams := [], type, value }
  return mkConst name

private meta structure CheckedLevel where
  graph : Expr
  level : Expr
  hbase : Expr
  hindiv : Expr
  hlevel : Expr

private meta def coloredLiteral (suffix : String) (graph : Expr)
    (raw : Hex.GraphIso.Raw) : TacticM Expr := do
  if raw.k = 0 then
    throwError "graph_aut: internal zero-colour individualized graph"
  let finTy := mkApp (mkConst ``Fin) (mkNatLit raw.k)
  let mut cells : List Expr := []
  for c in raw.colors.toList do
    cells := cells ++ [← mkAppM ``Fin.ofNat #[mkNatLit raw.k, mkNatLit c]]
  let array ← mkAppM ``List.toArray #[← mkListLit finTy cells]
  let hsize ← Hex.PermGroup.Kernel.Tactic.addKernelEq
    (← Hex.PermGroup.Kernel.Tactic.auxName s!"{suffix}_size")
    (← mkAppM ``Array.size #[array]) (mkNatLit raw.n)
  let vector ← mkAppM ``Vector.mk #[array, hsize]
  let coloring? ← mkAppM ``Coloring.ofVector? #[vector]
  let hsome ← Hex.PermGroup.Kernel.Tactic.addKernelEq
    (← Hex.PermGroup.Kernel.Tactic.auxName s!"{suffix}_onto")
    (← mkAppM ``Option.isSome #[coloring?]) (mkConst ``Bool.true)
  let coloring ← mkAppM ``Option.get #[coloring?, hsome]
  mkAppM ``Hex.GraphIso.Colored.mk #[graph, coloring]

/-- Replay one stabilizer level per kernel declaration, then assemble the
full checker proof from the small results. -/
private meta def checkCertificate (n : Nat) (raw : Hex.GraphIso.Raw) (G rows : Expr)
    (c : Aut.Kernel.Certificate) : TacticM (Expr × Expr) := do
  let graphValue ← mkAppM ``Hex.GraphIso.Colored.graph #[G]
  let graph ← Hex.PermGroup.Kernel.Tactic.addDataDef
    (← Hex.PermGroup.Kernel.Tactic.auxName "graph_underlying")
    (← inferType graphValue) graphValue
  let mut current := G
  let mut currentRaw := raw
  let mut checked : List CheckedLevel := []
  for (L, i) in (certificateList c).zipIdx do
    let level ← Hex.PermGroup.Kernel.Tactic.addDataDef
      (← Hex.PermGroup.Kernel.Tactic.auxName s!"graph_level_{i}")
      (mkConst ``Aut.Kernel.Level) (← levelExpr L)
    let hbase ← addDecideProof s!"graph_level_{i}_base" (← mkAppM ``LT.lt
      #[mkNatLit L.base, mkNatLit n])
    let v ← mkAppM ``Fin.mk #[mkNatLit L.base, hbase]
    let opt ← mkAppM ``Aut.indiv? #[current, v]
    let rawNext : Hex.GraphIso.Raw :=
      { currentRaw with
        k := currentRaw.k + 1
        colors := currentRaw.colors.set! L.base currentRaw.k }
    let nextValue ← coloredLiteral s!"graph_level_{i}_colors" graph rawNext
    let next ← Hex.PermGroup.Kernel.Tactic.addDataDef
      (← Hex.PermGroup.Kernel.Tactic.auxName s!"graph_level_{i}_graph")
      (← inferType nextValue) nextValue
    let hindiv ← Hex.PermGroup.Kernel.Tactic.addKernelEq
      (← Hex.PermGroup.Kernel.Tactic.auxName s!"graph_level_{i}_value")
      opt (← mkAppM ``Option.some #[next])
    let hlevel ← Hex.PermGroup.Kernel.Tactic.addKernelEq
      (← Hex.PermGroup.Kernel.Tactic.auxName s!"graph_level_{i}_check")
      (← mkAppM ``Aut.Kernel.Level.check #[current, rows, v, next, level])
      (mkConst ``Bool.true)
    checked := checked ++ [⟨current, level, hbase, hindiv, hlevel⟩]
    current := next
    currentRaw := rawNext
  let mut cert := mkConst ``Aut.Kernel.Certificate.done
  let mut hcheck ← Hex.PermGroup.Kernel.Tactic.addKernelEq
    (← Hex.PermGroup.Kernel.Tactic.auxName "graph_done")
    (← mkAppM ``Aut.Kernel.check #[current, rows, cert]) (mkConst ``Bool.true)
  for item in checked.reverse do
    cert ← Hex.PermGroup.Kernel.Tactic.addDataDef
      (← Hex.PermGroup.Kernel.Tactic.auxName "graph_certificate")
      (mkConst ``Aut.Kernel.Certificate)
      (mkApp2 (mkConst ``Aut.Kernel.Certificate.step) item.level cert)
    let proof ← mkAppM ``Aut.Kernel.check_step
      #[item.level, item.hbase, item.hindiv, item.hlevel, hcheck]
    let type ← mkEq (← mkAppM ``Aut.Kernel.check #[item.graph, rows, cert])
      (mkConst ``Bool.true)
    hcheck ← addProof "graph_step" type proof
  return (cert, hcheck)

private meta def allIsIso (G : Expr) (gens : List Expr) : TacticM Expr := do
  let mut proof ← mkAppM ``Aut.isIso_nil #[G]
  for i in [0 : gens.length] do
    let j := gens.length - 1 - i
    let p ← mkAppM ``Perm.ofEquiv #[gens[j]!]
    let hcheck ← Hex.PermGroup.Kernel.Tactic.addKernelEq
      (← Hex.PermGroup.Kernel.Tactic.auxName s!"generator_{j}_isIso")
      (← mkAppM ``Hex.GraphIso.checkIso #[G, G, p]) (mkConst ``Bool.true)
    let hp ← mkAppM ``Iff.mp #[← mkAppM ``Hex.GraphIso.checkIso_iff #[G, G, p], hcheck]
    proof ← mkAppM ``Aut.isIso_cons #[hp, proof]
  return proof

private meta def setOfList (permTy gsList : Expr) : MetaM Expr :=
  withLocalDeclD `g permTy fun g => do
    let pred ← mkLambdaFVars #[g] (← mkAppM ``Membership.mem #[gsList, g])
    return mkApp2 (mkConst ``setOf [0]) permTy pred

private meta def closureCard (permTy set : Expr) : MetaM Expr := do
  let closure ← mkAppM ``Subgroup.closure #[set]
  let pred ← withLocalDeclD `g permTy fun g => do
    mkLambdaFVars #[g] (← mkAppM ``Membership.mem #[closure, g])
  let subtype := mkApp2 (mkConst ``Subtype [0]) permTy pred
  return mkApp (mkConst ``Nat.card [0]) subtype

private meta def cardClosureTarget (permTy set : Expr) (N : Nat) : MetaM Expr := do
  mkAppM ``Eq #[← closureCard permTy set, mkNatLit N]

private meta def provePermCard (cfg : Config) (permTy gsList : Expr)
    (N : Nat) : TacticM Expr := do
  let set ← setOfList permTy gsList
  let target ← cardClosureTarget permTy set N
  let aux ← mkFreshExprMVar target
  let saved ← getGoals
  try
    setGoals [aux.mvarId!]
    Hex.PermGroup.Kernel.Tactic.permGroupTac { maxChunkWork := cfg.maxChunkWork }
    let proof ← instantiateMVars aux
    setGoals saved
    return proof
  catch ex =>
    setGoals saved
    throw ex

private meta def executableSize (G : Expr) : MetaM Nat := do
  let ty ← whnfR (← inferType G)
  unless ty.isAppOfArity ``Hex.GraphIso.Colored 2 do
    throwError "graph_aut: expected an executable coloured graph, got{indentExpr ty}"
  let some n ← (evalNat ty.getAppArgs[0]!).run
    | throwError "graph_aut: the graph size must be a numeral"
  return n

private meta def equivGroupGraph? (H : Expr) : MetaM (Option Expr) := do
  let H ← instantiateMVars H
  if H.isAppOf ``Aut.equivGroup then
    return H.getAppArgs.back?
  return none

private meta inductive GoalInput where
  | closure (G set permTy : Expr) (gens : List Expr)
  | execCard (G : Expr)
  | coloredCard (G : Expr)
  | graphCard (G : Expr)

private meta structure Parsed where
  input : GoalInput
  N : Nat

private meta def parseGoal (target : Expr) : MetaM Parsed := do
  let target ← instantiateMVars target
  let unsupported {α} : MetaM α := throwError
    "graph_aut: unsupported goal; expected a closure equality with `Aut.equivGroup`, \
    or the cardinality of `Aut.equivGroup`, `G ≃g G`, or `Colored.Iso G G`"
  unless target.isAppOfArity ``Eq 3 do unsupported
  let lhs := target.getArg! 1
  let rhs := target.getArg! 2
  if let some G ← equivGroupGraph? rhs then
    let some set ← Hex.PermGroup.Kernel.Tactic.closureArg? lhs | unsupported
    let some gens ← Hex.PermGroup.Kernel.Tactic.setLitElems set
      | throwError "graph_aut: the generating set must be a set literal or a coerced Finset literal"
    let permTy ← match (← inferType set) with
      | .app _ ty => pure ty
      | ty => throwError "graph_aut: unexpected generating-set type{indentExpr ty}"
    return ⟨.closure G set permTy gens, 0⟩
  unless lhs.isAppOfArity ``Nat.card 1 do unsupported
  let some N ← (evalNat rhs).run
    | throwError "graph_aut: the claimed order must be a numeral"
  let cardTy := lhs.getArg! 0
  if let some H ← Hex.PermGroup.Kernel.Tactic.coeSortArg? cardTy then
    if let some G ← equivGroupGraph? H then
      return ⟨.execCard G, N⟩
  if let some (G, H) ← HexGraphIsoMathlib.Tactic.matchColoredIso? cardTy then
    unless ← isDefEq G H do unsupported
    return ⟨.coloredCard G, N⟩
  if let some (G, H) ← HexGraphIsoMathlib.Tactic.matchIsoType? cardTy then
    unless ← isDefEq G H do unsupported
    return ⟨.graphCard G, N⟩
  unsupported

private meta inductive Finish where
  | direct
  | colored (e G : Expr)
  | graph (e G hpos : Expr)

private meta structure Prepared where
  G : Expr
  n : Nat
  finish : Finish
  closure? : Option (Expr × Expr × List Expr) := none

private meta def prepare : GoalInput → MetaM Prepared
  | .closure G set permTy gens => do
      return ⟨G, ← executableSize G, .direct, some (set, permTy, gens)⟩
  | .execCard G => do
      return ⟨G, ← executableSize G, .direct, none⟩
  | .coloredCard G => do
      let side ← HexGraphIsoMathlib.Tactic.mkSide true G
      let (enc, _) ← HexGraphIsoMathlib.Tactic.encodeSide true G side
      return ⟨enc, side.card, .colored side.equiv G, none⟩
  | .graphCard G => do
      let side ← HexGraphIsoMathlib.Tactic.mkSide false G
      if side.card = 0 then
        throwError "graph_aut: automorphisms of an empty vertex type are not yet supported"
      let (enc, hpos) ← HexGraphIsoMathlib.Tactic.encodeSide false G side
      return ⟨enc, side.card, .graph side.equiv G hpos.get!, none⟩

private meta def run (cfg : Config) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  if (← instantiateMVars target).hasMVar then
    throwError "graph_aut: the goal contains metavariables; the graph must be a closed term"
  let parsed ← parseGoal target
  let prep ← prepare parsed.input
  let side ← Hex.GraphIso.Tactic.mkSide prep.G
  unless side.raw.n = prep.n do
    throwError "graph_aut: internal graph-size mismatch"
  let certTerm ← mkAppM ``Aut.Kernel.certify? #[mkNatLit cfg.maxSearchNodes, prep.G]
  let some cert ← evalCertCore certTerm
    | throwError "graph_aut: certificate production did not finish within \
        maxSearchNodes := {cfg.maxSearchNodes}"
  let records := certificateRecords cert
  trace[graph_aut] "produced graph certificate: levels {certificateLevels cert}, records {records}"
  if cfg.maxCertRecords < records then
    throwError "graph_aut: the graph certificate has {records} records, exceeding \
      maxCertRecords := {cfg.maxCertRecords}"
  let bound := cert.bound
  let N := match parsed.input with
    | .closure .. => bound
    | _ => parsed.N
  unless bound = N do
    throwError "graph_aut: the certified automorphism-group order is {bound}, not {N}"
  let (certConst, hcheck) ← checkCertificate prep.n side.raw prep.G side.lit cert
  trace[graph_aut] "checked graph certificate in the kernel"
  let hbound ← Hex.PermGroup.Kernel.Tactic.addKernelEq
    (← Hex.PermGroup.Kernel.Tactic.auxName "graph_bound")
    (← mkAppM ``Aut.Kernel.Certificate.bound #[certConst]) (mkNatLit N)
  trace[graph_aut] "checked graph bound"
  let (set?, permTy, gens) ← match prep.closure? with
    | some (set, permTy, gens) => pure (some set, permTy, gens)
    | none => do
        let ps ← evalGensCore prep.n (← mkAppM ``Aut.gens #[prep.G])
        let mut gens : List Expr := []
        for p in ps do
          gens := gens ++ [← permExpr prep.n p]
        let permTy ← mkAppM ``Equiv.Perm #[mkApp (mkConst ``Fin) (mkNatLit prep.n)]
        pure (none, permTy, gens)
  let gsList ← mkListLit permTy gens
  let hcard ← provePermCard cfg permTy gsList N
  trace[graph_aut] "checked generator subgroup"
  let hgens ← allIsIso prep.G gens
  trace[graph_aut] "checked generator actions"
  let core ← match parsed.input with
    | .closure .. =>
        mkAppM ``Aut.closure_eq_equivGroup
          #[side.tie, hcheck, hgens, hcard, hbound]
    | _ =>
        mkAppM ``Aut.card_equivGroup_eq
          #[side.tie, hcheck, hgens, hcard, hbound]
  let proof ← match prep.finish with
    | .direct => pure core
    | .colored e G => do
        let bridgeFn ← mkAppM ``card_coloredIso #[e, G]
        let .forallE _ instTy _ _ ← whnf (← inferType bridgeFn)
          | throwError "graph_aut: internal coloured-cardinality bridge mismatch"
        let bridge := mkApp bridgeFn (← synthInstance instTy)
        mkEqTrans bridge core
    | .graph e G hpos => do
        let bridge ← mkAppM ``card_graphIso #[e, G, hpos]
        mkEqTrans (← instantiateMVars bridge) core
  let goal ← match set? with
    | none => pure goal
    | some set =>
        Hex.PermGroup.Kernel.Tactic.rewriteSet goal set gsList gens permTy
  unless ← isDefEq (← inferType proof) (← goal.getType) do
    throwError "graph_aut: internal final proof mismatch"
  goal.assign (← instantiateMVars proof)
  replaceMainGoal []
  trace[graph_aut] "degree {prep.n}, order {N}, levels {certificateLevels cert}, records {records}"

/-- Prove the order or explicit generator description of the automorphism
group of a closed graph by kernel-checked certificates. -/
syntax (name := graphAut) "graph_aut" optConfig : tactic

@[tactic graphAut] meta def evalGraphAut : Tactic := fun stx => do
  let cfg ← elabGraphAutConfig stx[1]
  let env ← getEnv
  try run cfg
  catch ex =>
    setEnv env
    throw ex

end HexGraphIsoMathlib.AutTactic
