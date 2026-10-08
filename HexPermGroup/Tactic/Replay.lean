/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Kernel.Full
public import HexPermGroup.Kernel.Certify
public meta import HexPermGroup.Kernel.Certify
public meta import HexPermGroup.Kernel.Full
public meta import Lean

public section

/-!
# Kernel replay for generated Hex permutation groups

`perm_group` proves `Generated S p`, `¬ Generated S p` and `HasOrder S N`
for a closed array of Hex permutations. The producer runs in compiled code;
the kernel checks all packing ties and bounded certificate pieces. The
Mathlib companion registers an extension of the same syntax.
-/

namespace Hex.PermGroup.Kernel.Tactic

open Lean Elab Tactic Meta

/-- `set_option trace.perm_group true` reports the certificate shape and the
range of each chunk. -/
meta initialize registerTraceClass `perm_group

/-- The limits of one `perm_group` call. -/
meta structure Config where
  /-- Estimated kernel work per emitted declaration, in field operations. -/
  maxChunkWork : Nat := 600000

meta section

/-- Elaborate the `(maxChunkWork := k)` configuration of one call. -/
declare_config_elab elabPermGroupConfig Config

end

private meta unsafe def evalImagesUnsafe (e : Expr) : MetaM (List Nat) :=
  evalExpr (List Nat) (mkApp (mkConst ``List [0]) (mkConst ``Nat)) e

@[implemented_by evalImagesUnsafe]
private meta opaque evalImagesCore (e : Expr) : MetaM (List Nat)

/-- Evaluate a closed permutation to its image list. -/
meta def evalImages (_n : Nat) (g : Expr) : MetaM (List Nat) := do
  try
    evalImagesCore (← mkAppM ``Perm.images #[g])
  catch ex =>
    throwError "perm_group: failed to evaluate the permutation{indentExpr g}\n{ex.toMessageData}\
      \nThe generators and the query must be closed terms the compiler can evaluate."

private meta unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool :=
  evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolUnsafe]
private meta opaque evalBoolCore (e : Expr) : MetaM Bool

/-- Check whether an image-list constructor uses its valid-permutation branch. -/
meta def checkedImages (nE l : Expr) : MetaM Bool := do
  evalBoolCore (← mkAppM ``imagesOk #[nE, l])

/-- A runtime permutation from its image list. -/
meta def parsePerm (n : Nat) (l : List Nat) : MetaM (Perm n) := do
  let imgs : Array (Fin n) ← l.toArray.mapM fun x =>
    if h : x < n then pure ⟨x, h⟩ else throwError "perm_group: image {x} out of range"
  if h : imgs.size = n then
    let v : Vector (Fin n) n := ⟨imgs, h⟩
    if h1 : v.toList.Nodup then
      if h2 : ∀ i : Fin n, i ∈ v.toList then return ⟨v, h1, h2⟩
  throwError "perm_group: the images {l} do not form a permutation"

/-! # Literals -/

meta def natListLit (xs : List Nat) : MetaM Expr :=
  mkListLit (mkConst ``Nat) (xs.map mkNatLit)

meta def pairLit (p : Nat × Nat) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkNatLit p.1) (mkNatLit p.2)

meta partial def rarrayLit (ty : Expr) (f : α → Expr) : Lean.RArray α → Expr
  | .leaf x => mkApp2 (mkConst ``Lean.RArray.leaf [0]) ty (f x)
  | .branch p l r =>
    mkApp4 (mkConst ``Lean.RArray.branch [0]) ty (mkNatLit p) (rarrayLit ty f l) (rarrayLit ty f r)

meta def levelLit (L : Level) : MetaM Expr := do
  let natNat := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
  return mkAppN (mkConst ``Level.mk)
    #[mkNatLit L.base, mkNatLit L.size, ← natListLit L.gens,
      rarrayLit (mkConst ``Nat) mkNatLit L.orbit, rarrayLit (mkConst ``Nat) mkNatLit L.reps,
      rarrayLit (mkConst ``Nat) mkNatLit L.invs, rarrayLit natNat pairLit L.parents,
      mkNatLit L.lookup,
      ← mkListLit (← mkAppM ``List #[natNat]) (← L.next.mapM fun w => mkListLit natNat (w.map pairLit)),
      ← mkListLit (← mkAppM ``List #[mkConst ``Nat]) (← L.inputWords.mapM natListLit)]

/-! # Declarations -/

/-- A fresh auxiliary name below the current declaration. -/
meta def auxName (suffix : String) : TacticM Name := do
  let base := ((← Term.getDeclName?).getD `perm_group) ++ `_perm_group
  let env ← getEnv
  let mut i := 1
  while env.contains (base ++ Name.mkSimple s!"{suffix}_{i}") do
    i := i + 1
  return base ++ Name.mkSimple s!"{suffix}_{i}"

/-- Add an auxiliary declaration, kernel-checking it on a dedicated thread and
waiting for the result. When Lean checks theorems asynchronously, the kernel's
work is not charged to the heartbeats of the elaboration that produced them,
and each check has its own `maxHeartbeats` budget. `perm_group` waits instead,
so that a failed check is reported by the tactic and rolls back its
declarations; running the check on another thread keeps the same accounting.
The check shares the tactic's cancellation token, and its messages and traces,
such as a warning that a declaration uses `sorry`, are kept. -/
meta def addAuxDecl (decl : Declaration) : CoreM Unit := do
  Core.checkInterrupted
  let act ← Core.wrapAsync (cancelTk? := (← read).cancelTk?) fun (_ : Unit) => do
    -- Start from empty diagnostics, so that only this declaration's are returned.
    modify fun st => { st with messages := {}, traceState := { st.traceState with traces := {} } }
    addDecl decl
    let st ← get
    return (← getEnv, st.messages, st.traceState.traces)
  let task ← IO.asTask (prio := .dedicated) (act ()).toBaseIO
  match ← IO.wait task with
  | .ok (.ok (env, messages, traces)) =>
    Core.checkInterrupted
    setEnv env
    modify fun st => { st with
      messages := st.messages ++ messages
      traceState := { st.traceState with traces := st.traceState.traces ++ traces } }
  | .ok (.error ex) => throw ex
  | .error ex => throwError "perm_group: auxiliary declaration task failed: {ex}"

/-- Add a `noncomputable` definition holding kernel data. -/
meta def addDataDef (name : Name) (type value : Expr) : MetaM Expr := do
  addAuxDecl <| .defnDecl
    { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
  modifyEnv (addNoncomputable · name)
  return mkConst name

/-- Add a theorem `lhs = rhs`, proved by `Eq.refl` so that the kernel performs
the evaluation, in its own declaration. -/
meta def addKernelEq (name : Name) (lhs rhs : Expr) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  let value ← mkEqRefl rhs
  addAuxDecl <| .thmDecl { name, levelParams := [], type := ty, value }
  return mkConst name

/-! # The tactic -/

/-- The shape of a supported goal. -/
meta inductive GoalKind where
  | card (N : Nat)
  | mem (g : Expr)
  | notMem (g : Expr)
  | all


/-- A closed Hex permutation, optionally with a kernel-checkable equality to a
canonical Hex expression. Canonical expressions only optimize packing. -/
meta structure Input where
  term : Expr
  canonical? : Option (Expr × Expr) := none
  deriving Inhabited

/-- A requested computational conclusion. -/
meta inductive Goal where
  | card (N : Nat)
  | mem (g : Input)
  | notMem (g : Input)
  | all

/-- Prepared, untrusted certificate data shared by replay and source rendering.
Every proof-producing operation still checks the packing and certificate. -/
meta structure Prepared where
  config : Config
  degree : Nat
  inputs : List Input
  images : List (List Nat)
  certificate : Certificate
  /-- Whether `certificate` was checked earlier in this file, in which case
  replay emits none of its level checks and `parts` is empty. -/
  cached : Bool := false
  parts : List (List (Nat × Nat))

/-- The order proposed by the prepared certificate. -/
meta def Prepared.order (p : Prepared) : Nat := Kernel.order p.certificate

/-- A certificate already checked by the kernel earlier in the current file.
`checked` proves `check degree inputs (mkConst cert) = true`, and `levels`
are the data definitions listed by `cert`. -/
meta structure Checked where
  certificate : Certificate
  cert : Name
  levels : Array Name
  checked : Name

/-- Checked certificates of the current file, keyed by degree and packed
generators. Later `perm_group` calls on the same generators reuse them instead
of certifying and checking the chain again. The state is not exported: an
importing module cannot unfold the certificate definitions. -/
meta initialize checkedExt : EnvExtension (Std.HashMap (Nat × List Nat) Checked) ←
  registerEnvExtension (pure {}) (asyncMode := .sync)

/-- The checked certificate for these packed generators, if any. -/
meta def findChecked? (n : Nat) (inputs : List Nat) : MetaM (Option Checked) :=
  return (checkedExt.getState (← getEnv))[(n, inputs)]?

private meta def validateInput (n : Nat) (input : Input) : MetaM Input := do
  let term ← instantiateMVars input.term
  let ty := mkApp (mkConst ``Perm) (mkNatLit n)
  if term.hasFVar || term.hasMVar || term.hasLooseBVars then
    throwError "perm_group: the generators and query must be closed terms"
  unless ← isDefEq (← inferType term) ty do
    throwError "perm_group: expected a Hex permutation of degree {n}"
  let canonical? ← input.canonical?.mapM fun (canonical, proof) => do
    let canonical ← instantiateMVars canonical
    let proof ← instantiateMVars proof
    if canonical.hasFVar || canonical.hasMVar || canonical.hasLooseBVars ||
        proof.hasFVar || proof.hasMVar || proof.hasLooseBVars then
      throwError "perm_group: canonical input and equality must be closed terms"
    unless ← isDefEq (← inferType canonical) ty do
      throwError "perm_group: canonical input has the wrong degree"
    unless ← isDefEq (← inferType proof) (← mkEq term canonical) do
      throwError "perm_group: canonical input equality has the wrong type"
    return (canonical, proof)
  return { term, canonical? }

/-- Evaluate and prepare the generators once. This operation adds no declarations. -/
meta def prepare (cfg : Config) (n : Nat) (inputs : List Input) : MetaM Prepared := do
  let inputs ← inputs.mapM (validateInput n)
  let images ← inputs.mapM fun input => evalImages n input.term
  let perms : List (Perm n) ← images.mapM fun l => (parsePerm n l : MetaM (Perm n))
  if cfg.maxChunkWork == 0 then throwError "perm_group: the chunk budget must be positive"
  match ← findChecked? n (perms.map pack) with
  | some entry =>
    -- No level check will be emitted, so the chunk budget does not apply.
    return { config := cfg, degree := n, inputs, images, certificate := entry.certificate,
             cached := true, parts := [] }
  | none =>
    let certificate ← match certify perms.toArray with
      | .ok c => pure c
      | .error msg => throwError "perm_group: certificate construction failed: {msg}"
    unless check n (perms.map pack) certificate do
      throwError "perm_group: the certificate failed its compiled check"
    let parts ← match chunks n inputs.length certificate cfg.maxChunkWork with
      | .ok parts => pure parts
      | .error msg => throwError "perm_group: {msg}"
    return { config := cfg, degree := n, inputs, images, certificate, parts }


/-- A proof that `pack g = x`. A generator written `Perm.ofImages n l` is
checked in time linear in `n`. Any other closed permutation is evaluated by the kernel. -/
meta def packTie (nE g : Expr) (x : Nat) (suffix : String) : TacticM Expr := do
  if g.isAppOfArity ``Hex.Perm.ofImages 2 then
    let l := g.getArg! 1
    if ← checkedImages nE l then
      let hok ← addKernelEq (← auxName s!"{suffix}_images") (← mkAppM ``imagesOk #[nE, l])
        (mkConst ``Bool.true)
      let hpk ← addKernelEq (← auxName s!"{suffix}_pack") (← mkAppM ``packList #[nE, l])
        (mkNatLit x)
      return ← mkEqTrans (← mkAppM ``pack_ofImages #[hok]) hpk
  addKernelEq (← auxName suffix)
    (← mkAppOptM ``pack #[nE, g]) (mkNatLit x)

/-- Read an array literal, unfolding definitions without reducing its elements. -/
meta partial def arrayElems? (s : Expr) (fuel : Nat := 32) : MetaM (Option (List Expr)) := do
  let s ← instantiateMVars s
  if let some xs ← getArrayLit? s then return some xs.toList
  match fuel with
  | 0 => return none
  | k + 1 =>
    let some t ← unfoldDefinition? s | return none
    arrayElems? t k

/-- The degree must be a numeral. -/
meta def degree (S : Expr) : MetaM Nat := do
  let ty ← whnfR (← inferType S)
  unless ty.isAppOfArity ``Array 1 && (ty.getArg! 0).isAppOfArity ``Perm 1 do
    throwError "perm_group: expected an array of Hex permutations{indentExpr ty}"
  let nE := (ty.getArg! 0).getArg! 0
  let some n ← (evalNat nE).run
    | throwError "perm_group: the degree must be a numeral{indentExpr nE}"
  return n

/-- Match the computational generation and order goal forms. -/
meta def readGoal? (target : Expr) : MetaM (Option (Expr × GoalKind)) := do
  let t ← instantiateMVars target
  if t.isAppOfArity ``HasOrder 3 then
    let some N ← (evalNat (t.getArg! 2)).run
      | throwError "perm_group: the claimed order must be a numeral"
    return some (t.getArg! 1, .card N)
  if t.isAppOfArity ``Generated 3 then return some (t.getArg! 1, .mem (t.getArg! 2))
  if t.isAppOfArity ``Not 1 && (t.getArg! 0).isAppOfArity ``Generated 3 then
    let m := t.getArg! 0
    return some (m.getArg! 1, .notMem (m.getArg! 2))
  if t.isAppOfArity ``GeneratesAll 2 then return some (t.getArg! 1, .all)
  if t.isForall && t.bindingDomain!.isAppOfArity ``Perm 1 then
    let body := t.bindingBody!
    if body.isAppOfArity ``Generated 3 && body.getArg! 2 == .bvar 0 &&
        !(body.getArg! 1).hasLooseBVars then
      return some (body.getArg! 1, .all)
  return none

/-- Certify and replay a goal over a literal list of Hex permutations. Each
packing tie and bounded checker piece remains its own auxiliary declaration. -/
private meta def replayCore (prepared : Prepared) (kind : GoalKind)
    (tie : Expr → Expr → Nat → String → TacticM Expr := packTie) : TacticM Expr := do
  let n := prepared.degree
  let cfg := prepared.config
  let gens := prepared.inputs.map Input.term
  let c := prepared.certificate
  let parts := prepared.parts
  let inputs := prepared.images.map (fun l => packList n l)
  let W := width n
  let e := ident n W
  -- decide the goal in compiled code before adding any declaration
  let query ← match kind with
    | .mem g | .notMem g => do
      let p : Perm n ← (parsePerm n (← evalImages n g) : MetaM (Perm n))
      pure (some (g, pack p))
    | _ => pure none
  match kind with
  | .all =>
    let work := (c.map fun L => n * (2 * L.size + 2)).foldl max n
    if work > cfg.maxChunkWork then
      throwError "perm_group: full coverage check needs {work} estimated operations, \
        exceeding maxChunkWork := {cfg.maxChunkWork}"
    unless full n 0 c do
      throwError "perm_group: the certified group does not generate every permutation"
  | .card N =>
    unless order c == N do
      throwError "perm_group: the certified order is {order c}, not {N}"
  | .mem g =>
    unless sift n W e c (query.get!.2) do
      throwError "perm_group: the permutation{indentExpr g}\nis not in the subgroup"
  | .notMem g =>
    if sift n W e c (query.get!.2) then
      throwError "perm_group: the permutation{indentExpr g}\nis in the subgroup"
  trace[perm_group] "degree {n}, order {order c}, orbit sizes {c.map (·.size)}, \
    chunks per level {parts.map (·.length)}"
  -- declarations
  let natE := mkConst ``Nat
  let nE := mkNatLit n
  let WE ← mkAppM ``width #[nE]
  let eE ← mkAppM ``ident #[nE, WE]
  let levelTy := mkConst ``Level
  let inputsE ← natListLit inputs
  -- the inputs are the packings of the generators
  let mut hS ← mkAppOptM ``pack_nil #[nE]
  for k' in [0:gens.length] do
    let k := gens.length - 1 - k'
    let hk ← tie nE gens[k]! inputs[k]! s!"input_{k}"
    hS ← mkAppM ``pack_cons #[hk, hS]
  let entry ← match ← findChecked? n inputs with
    | some entry =>
      trace[perm_group] "reusing the checked certificate {entry.cert}"
      pure entry
    | none => do
      let mut levelConsts : Array Expr := #[]
      for h : i in [0:c.length] do
        let L := c[i]
        levelConsts := levelConsts.push
          (← addDataDef (← auxName s!"level_{i}") levelTy (← levelLit L))
      let suffix (k : Nat) : MetaM Expr :=
        mkListLit levelTy (levelConsts.toList.drop k)
      let certName ← auxName "cert"
      let certE ← addDataDef certName (← mkAppM ``List #[levelTy]) (← suffix 0)
      let hIn ← addKernelEq (← auxName "inputs_ok")
        (← mkAppM ``inputsOk #[nE, WE, eE, inputsE, certE]) (mkConst ``Bool.true)
      -- levels, from the last to the first
      let mut hLevels ← mkAppOptM ``levelsOk_nil #[nE]
      for k' in [0:c.length] do
        let k := c.length - 1 - k'
        let L := c[k]!
        let LE := levelConsts[k]!
        let restE ← suffix (k + 1)
        let hl ← addKernelEq (← auxName s!"level_{k}_ok")
          (← mkAppM ``levelOk #[nE, WE, eE, LE, restE]) (mkConst ``Bool.true)
        let total := L.gens.length * L.size
        let hN ← addKernelEq (← auxName s!"level_{k}_pairs")
          (← mkAppM ``Nat.mul #[← mkAppM ``List.length #[← mkAppM ``Level.gens #[LE]],
            ← mkAppM ``Level.size #[LE]]) (mkNatLit total)
        let ranges := parts[k]!
        let mut hp ← mkAppM ``pairsOk_nil #[nE, WE, eE, LE, restE, mkNatLit 0]
        for h : r in [0:ranges.length] do
          let (lo, hi') := ranges[r]
          trace[perm_group] "level {k}: pairs [{lo}, {hi'})"
          let hc ← addKernelEq (← auxName s!"level_{k}_chunk_{r}")
            (← mkAppM ``pairsOk #[nE, WE, eE, LE, restE, mkNatLit lo, mkNatLit hi'])
            (mkConst ``Bool.true)
          let h₁ ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit 0, mkNatLit lo])
          let h₂ ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit hi'])
          hp ← mkAppM ``pairsOk_append #[nE, WE, eE, LE, restE, h₁, h₂, hp, hc]
        hLevels ← mkAppM ``levelsOk_cons_of #[hl, hN, hp, hLevels]
      let checkedName ← auxName "checked"
      addAuxDecl <| .thmDecl
        { name := checkedName, levelParams := []
          type := ← mkEq (← mkAppM ``check #[nE, inputsE, certE]) (mkConst ``Bool.true)
          value := ← mkAppM ``check_of #[hIn, hLevels] }
      let entry : Checked :=
        { certificate := c, cert := certName,
          levels := levelConsts.filterMap Expr.constName?, checked := checkedName }
      modifyEnv fun env => checkedExt.modifyState env (·.insert (n, inputs) entry)
      pure entry
  let levelConsts := entry.levels.map mkConst
  let suffix (k : Nat) : MetaM Expr :=
    mkListLit levelTy (levelConsts.toList.drop k)
  let certE := mkConst entry.cert
  let hCheck := mkConst entry.checked
  let proof ← match kind with
    | .all =>
      let masks := c.scanl (fun fixed L => Nat.lor fixed (Nat.shiftLeft 1 L.base)) 0
      let mut hf ← addKernelEq (← auxName "full_end")
        (← mkAppM ``full #[nE, mkNatLit masks.getLast!, ← suffix c.length])
        (mkConst ``Bool.true)
      for k' in [0:c.length] do
        let k := c.length - 1 - k'
        let hL ← addKernelEq (← auxName s!"level_{k}_full")
          (← mkAppM ``fullLevel #[nE, mkNatLit masks[k]!, levelConsts[k]!])
          (mkConst ``Bool.true)
        hf ← mkAppM ``full_cons_of #[hL, hf]
      mkAppM ``all_of_check #[hS, hCheck, hf]
    | .card N =>
      let hO ← addKernelEq (← auxName "order") (← mkAppM ``order #[certE]) (mkNatLit N)
      mkAppM ``hasOrder_of_check #[hS, hCheck, hO]
    | .mem g =>
      let (_, x) := query.get!
      let hx ← tie nE g x "query"
      let hs ← addKernelEq (← auxName "sift")
        (← mkAppM ``Kernel.sift #[nE, WE, eE, certE, mkNatLit x]) (mkConst ``Bool.true)
      mkAppM ``generated_of_check #[hS, hCheck, hx, hs]
    | .notMem g =>
      let (_, x) := query.get!
      let hx ← tie nE g x "query"
      let hs ← addKernelEq (← auxName "sift")
        (← mkAppM ``Kernel.sift #[nE, WE, eE, certE, mkNatLit x]) (mkConst ``Bool.false)
      mkAppM ``not_generated_of_check #[hS, hCheck, hx, hs]
  return proof

private meta def expectedType (prepared : Prepared) (kind : GoalKind) : MetaM Expr := do
  let nE := mkNatLit prepared.degree
  let ty := mkApp (mkConst ``Perm) nE
  let gs ← mkListLit ty (prepared.inputs.map Input.term)
  let array ← mkAppM ``List.toArray #[gs]
  match kind with
  | .card N => mkAppM ``HasOrder #[array, mkNatLit N]
  | .mem g => mkAppM ``Generated #[array, g]
  | .notMem g => mkAppM ``Not #[← mkAppM ``Generated #[array, g]]
  | .all => mkAppM ``GeneratesAll #[array]

private meta def checkProof (proof target : Expr) : MetaM Unit := do
  unless ← withTransparency .all (isDefEq (← inferType proof) target) do
    throwError "perm_group: internal final proof mismatch\nProof:{indentExpr (← inferType proof)}\nGoal:{indentExpr target}"

private meta def transaction (action : TacticM α) : TacticM α := do
  let saved ← Tactic.saveState
  -- Auxiliary kernel errors must be caught before returning a proof or rolling
  -- back. Deferred checks could otherwise escape this transaction.
  let completed ← IO.mkRef false
  try
    let result ← withOptions (fun opts => opts.setBool `Elab.async false) action
    completed.set true
    return result
  finally
    unless ← completed.get do saved.restore true

private meta def packInput (nE : Expr) (input : Input) (x : Nat) (suffix : String) :
    TacticM Expr := do
  match input.canonical? with
  | none => packTie nE input.term x suffix
  | some (canonical, equality) =>
    -- The transport declaration performs the literal packing check itself,
    -- moving the evaluation here and removing one auxiliary declaration.
    let tie ← if canonical.isAppOfArity ``Hex.Perm.ofImages 2 &&
        (← checkedImages nE (canonical.getArg! 1)) then do
      let hok ← addKernelEq (← auxName s!"{suffix}_images")
        (← mkAppM ``imagesOk #[nE, canonical.getArg! 1]) (mkConst ``Bool.true)
      mkAppM ``pack_ofImages #[hok]
    else packTie nE canonical x suffix
    let packed ← mkCongrArg (← mkAppOptM ``pack #[nE]) equality
    let value ← mkEqTrans packed tie
    let type ← mkEq (← mkAppOptM ``pack #[nE, input.term]) (mkNatLit x)
    let name ← auxName s!"{suffix}_transport"
    addAuxDecl <| .thmDecl { name, levelParams := [], type, value }
    return mkConst name

/-- Replay a requested conclusion. Packing transport, bounded declarations and
final proof checking are owned by Hex, and failures restore all tactic state. -/
meta def replay (prepared : Prepared) (goal : Goal) : TacticM Expr := transaction do
  let query ← match goal with
    | .mem input | .notMem input => pure (some (← validateInput prepared.degree input))
    | _ => pure none
  let kind := match goal with
    | .card N => GoalKind.card N
    | .all => .all
    | .mem _ => .mem query.get!.term
    | .notMem _ => .notMem query.get!.term
  let inputs := prepared.inputs ++ query.toList
  let proof ← replayCore prepared kind fun nE g x suffix => do
    let some input := inputs.find? (fun input => input.term == g)
      | throwError "perm_group: unknown replay input"
    packInput nE input x suffix
  checkProof proof (← expectedType prepared kind)
  return proof

/-- Compatibility entry point for consumers of the original replay API. -/
meta def prove (cfg : Config) (n : Nat) (gens : List Expr) (kind : GoalKind)
    (tie : Expr → Expr → Nat → String → TacticM Expr := packTie) : TacticM Expr :=
  transaction do
    let prepared ← prepare cfg n (gens.map fun term => { term })
    let proof ← replayCore prepared kind tie
    checkProof proof (← expectedType prepared kind)
    return proof

/-- A `perm_group` goal handler contributed by a downstream library.
A `public meta def` of this type tagged `@[perm_group_extension]`
extends the same `perm_group` syntax to that library's goal shapes. -/
meta structure Extension where
  /-- Handle a goal, returning its proof term, or `none` when the goal
  shape is not this extension's. -/
  prove? : Config → Expr → TacticM (Option Expr)
  /-- Print a certificate for this extension's generator representation. -/
  certificate? : String → Expr → Syntax → TermElabM (Option String) := fun _ _ _ => pure none

meta section

open Lean

/-- The registered `perm_group` extensions, in declaration order. -/
initialize extensionExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss => nss.flatten
    addEntryFn := fun s n => s.push n
  }

initialize registerBuiltinAttribute {
  name := `perm_group_extension
  descr := "register a `perm_group` goal handler for extra goal shapes"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    ensureAttrDeclIsMeta `perm_group_extension decl kind
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `perm_group_extension kind
    let declType := (← getConstInfo decl).type
    unless declType.isConstOf ``Extension do
      throwAttrDeclNotOfExpectedType `perm_group_extension decl declType
        (mkConst ``Extension)
    modifyEnv fun env => extensionExt.addEntry env decl
}

end

private meta unsafe def evalExtensionUnsafe (n : Name) : MetaM Extension :=
  evalConst Extension n

@[implemented_by evalExtensionUnsafe]
private meta opaque evalExtensionCore (n : Name) : MetaM Extension

/-- All extensions present in the current environment, in lookup order. -/
meta def extensions : MetaM (List Extension) := do
  let names := extensionExt.getState (← getEnv)
  names.toList.mapM evalExtensionCore

/-- Prove generation, non-generation or exact order from a packed certificate.
Correspondence libraries extend this syntax to goals about subgroup closures. -/
syntax (name := permGroup) "perm_group" optConfig : tactic

/-- The shared tactic entry point, also callable by computational consumers. -/
meta def permGroupTac (cfg : Config) : TacticM Unit := transaction do
    withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let proof ← match ← readGoal? target with
        | some (S, kind) => do
          let some gens ← arrayElems? S
            | throwError "perm_group: expected an array literal or a definition unfolding to one"
          let prepared ← prepare cfg (← degree S) (gens.map fun term => { term })
          let request := match kind with
            | .card N => Goal.card N
            | .mem term => .mem { term }
            | .notMem term => .notMem { term }
            | .all => .all
          replay prepared request
        | none => do
          let mut result := none
          for ext in ← extensions do
            if result.isNone then result ← ext.prove? cfg target
          let some proof := result
            | throwError "perm_group: unsupported goal{indentExpr target}\n\
              Expected `Generated S p`, `¬ Generated S p`, `HasOrder S N` or `GeneratesAll S`.\n\
              Import a correspondence library for goals about subgroup closures."
          pure proof
      unless ← withTransparency .all (isDefEq (← inferType proof) target) do
        throwError "perm_group: internal final proof mismatch\nProof:{indentExpr (← inferType proof)}\nGoal:{indentExpr target}"
      goal.assign proof
      replaceMainGoal []

@[tactic permGroup] meta def evalPermGroup : Tactic := fun stx => do
  permGroupTac (← elabPermGroupConfig stx[1])

meta partial def rarraySrc (f : α → String) : Lean.RArray α → String
  | .leaf x => s!"(.leaf {f x})"
  | .branch p l r => s!"(.branch {p} {rarraySrc f l} {rarraySrc f r})"

meta def listSrc (f : α → String) (xs : List α) : String :=
  "[" ++ ", ".intercalate (xs.map f) ++ "]"

meta def pairSrc (p : Nat × Nat) : String := s!"({p.1}, {p.2})"

meta def levelSrc (L : Level) : String :=
  s!"\{ base := {L.base}, size := {L.size},\n    gens := {listSrc toString L.gens},\n" ++
  s!"    orbit := {rarraySrc toString L.orbit},\n    reps := {rarraySrc toString L.reps},\n" ++
  s!"    invs := {rarraySrc toString L.invs},\n    parents := {rarraySrc pairSrc L.parents},\n" ++
  s!"    lookup := {L.lookup},\n    next := {listSrc (listSrc pairSrc) L.next},\n" ++
  s!"    inputWords := {listSrc (listSrc toString) L.inputWords} }"

/-- Print kernel packing ties and bounded checks for the prepared certificate.
Canonical image constructors use their optimized ties; other inputs use
kernel evaluation of the original term. -/
meta def render (name : String) (prepared : Prepared)
    (elemSrc : List String) (sSrc : String)
    (imagesTie : Expr → MetaM (Option String) := fun g => do
      if g.isAppOfArity ``Hex.Perm.ofImages 2 then
        if ← checkedImages (mkNatLit prepared.degree) (g.getArg! 1) then
          return some "_root_.Hex.PermGroup.Kernel.pack_ofImages"
      return none) : TermElabM String := do
  let n := prepared.degree
  let gens := prepared.inputs.map Input.term
  unless elemSrc.length == gens.length do
    throwError "#perm_group_certificate: wrong number of generator sources"
  let gsSrc := "[" ++ ", ".intercalate elemSrc ++ "]"
  let images := prepared.images
  let c := prepared.certificate
  -- A certificate reused from this file has no chunk ranges; the printed
  -- source checks every level, so compute them here.
  let parts ← if prepared.cached then
      match chunks n gens.length c prepared.config.maxChunkWork with
      | .ok parts => pure parts
      | .error msg => throwError "#perm_group_certificate: {msg}"
    else pure prepared.parts
  let inputs := images.map (packList n)
  let ctx := s!"{n} (_root_.Hex.PermGroup.Kernel.width {n}) (_root_.Hex.PermGroup.Kernel.ident {n} (_root_.Hex.PermGroup.Kernel.width {n}))"
  let lv (k : Nat) : String :=
    listSrc (fun j => s!"{name}_level_{j}") (List.range' k (c.length - k))
  let mut out := "section\n\nset_option maxRecDepth 8192\n\n" ++
    "open Hex Hex.PermGroup Hex.PermGroup.Kernel\n\n"
  for h : i in [0:c.length] do
    out := out ++ s!"noncomputable def {name}_level_{i} : _root_.Hex.PermGroup.Kernel.Level :=\n  {levelSrc c[i]}\n\n"
  -- Explicit packing theorems make the rendered source easy to inspect.
  let mut hS := "_root_.Hex.PermGroup.Kernel.pack_nil"
  for k' in [0:gens.length] do
    let k := gens.length - 1 - k'
    let g := gens[k]!
    let x := inputs[k]!
    let input := prepared.inputs[k]!
    let canonical := input.canonical?.map Prod.fst |>.getD g
    let tie ← if let some lemmaName ← imagesTie canonical then do
        let l := listSrc toString images[k]!
        out := out ++ s!"theorem {name}_input_{k}_images : _root_.Hex.PermGroup.Kernel.imagesOk {n} {l} = true := by\n" ++
          "  decide +kernel\n\n"
        out := out ++ s!"theorem {name}_input_{k}_pack : _root_.Hex.PermGroup.Kernel.packList {n} {l} = {x} := by\n" ++
          "  decide +kernel\n\n"
        let tie := s!"(({lemmaName} {name}_input_{k}_images).trans {name}_input_{k}_pack)"
        if let some (_, equality) := input.canonical? then
          let equalitySrc ← withOptions (fun opts =>
              ((opts.setBool `pp.fullNames true).setBool `pp.proofs true)
                |>.setBool `pp.deepTerms true |>.set `pp.maxSteps (100000000 : Nat)) do
            return (← ppExpr equality).pretty
          pure s!"((congrArg (_root_.Hex.PermGroup.Kernel.pack (n := {n})) ({equalitySrc})).trans {tie})"
        else pure tie
      else do
        out := out ++ s!"theorem {name}_input_{k} :\n" ++
          s!"    _root_.Hex.PermGroup.Kernel.pack ({elemSrc[k]!} : _root_.Hex.Perm {n}) = {x} := by\n" ++
          "  decide +kernel\n\n"
        pure s!"{name}_input_{k}"
    hS := s!"(_root_.Hex.PermGroup.Kernel.pack_cons {tie}\n      {hS})"
  out := out ++ s!"theorem {name}_inputs :\n" ++
    s!"    ({gsSrc} : List (_root_.Hex.Perm {n})).map _root_.Hex.PermGroup.Kernel.pack =\n" ++
    s!"      {listSrc toString inputs} :=\n  {hS}\n\n"
  out := out ++ s!"theorem {name}_inputs_ok :\n    _root_.Hex.PermGroup.Kernel.inputsOk {ctx} {listSrc toString inputs}\n" ++
    s!"      {lv 0} = true := by\n  decide +kernel\n\n"
  let mut levels := "_root_.Hex.PermGroup.Kernel.levelsOk_nil"
  for k' in [0:c.length] do
    let k := c.length - 1 - k'
    let L := c[k]!
    out := out ++ s!"theorem {name}_level_{k}_ok :\n" ++
      s!"    _root_.Hex.PermGroup.Kernel.levelOk {ctx} {name}_level_{k} {lv (k+1)} = true := by\n" ++
      "  decide +kernel\n\n"
    out := out ++ s!"theorem {name}_level_{k}_pairs :\n" ++
      s!"    Nat.mul {name}_level_{k}.gens.length " ++
      s!"{name}_level_{k}.size = {L.gens.length * L.size} := by\n  decide +kernel\n\n"
    let mut acc := "(_root_.Hex.PermGroup.Kernel.pairsOk_nil _ _ _ _ _ 0)"
    for h : r in [0:parts[k]!.length] do
      let (lo, hi) := parts[k]![r]
      out := out ++ s!"theorem {name}_level_{k}_chunk_{r} :\n" ++
        s!"    _root_.Hex.PermGroup.Kernel.pairsOk {ctx} {name}_level_{k} {lv (k+1)} " ++
        s!"{lo} {hi} = true := by\n  decide +kernel\n\n"
      acc := s!"(_root_.Hex.PermGroup.Kernel.pairsOk_append _ _ _ _ _ (by decide) (by decide) {acc} " ++
        s!"{name}_level_{k}_chunk_{r})"
    levels := s!"(_root_.Hex.PermGroup.Kernel.levelsOk_cons_of {name}_level_{k}_ok {name}_level_{k}_pairs\n" ++
      s!"      {acc}\n      {levels})"
  out := out ++ s!"theorem {name}_order : _root_.Hex.PermGroup.Kernel.order {lv 0} = {order c} := by\n  decide +kernel\n\n"
  out := out ++ s!"theorem {name}_hasOrder :\n" ++
    s!"    _root_.Hex.PermGroup.HasOrder {sSrc} {order c} := by\n" ++
    s!"  exact _root_.Hex.PermGroup.Kernel.hasOrder_of_check {name}_inputs (_root_.Hex.PermGroup.Kernel.check_of {name}_inputs_ok\n" ++
    s!"      {levels})\n    {name}_order\n\n" ++
    "end\n"
  return out
/-- Compatibility printer for the original generator-expression API. -/
meta def certificateSource (name : String) (n : Nat) (gens : List Expr)
    (elemSrc : List String) (sSrc : String)
    (imagesTie : Expr → MetaM (Option String) := fun g => do
      if g.isAppOfArity ``Hex.Perm.ofImages 2 then
        if ← checkedImages (mkNatLit n) (g.getArg! 1) then
          return some "_root_.Hex.PermGroup.Kernel.pack_ofImages"
      return none) : TermElabM String := do
  let prepared ← prepare {} n (gens.map fun term => { term })
  render name prepared elemSrc sSrc imagesTie

/-- Recover authored elements without pretty-printing their proof fields. -/
meta partial def arraySources? (stx : Syntax) : Option (Array Syntax) :=
  if stx.getKind == ``Lean.Parser.Term.typeAscription then arraySources? stx[1]
  else if stx.getKind == ``Lean.Parser.Term.paren then arraySources? stx[1]
  else if stx.getNumArgs == 3 && stx[0].isToken "#[" && stx[2].isToken "]" then
    some stx[1].getSepArgs
  else none

/-- Print a reusable kernel certificate and its exact-order proof. -/
syntax (name := permGroupCertificate) "#perm_group_certificate " ident " for " term : command

@[command_elab permGroupCertificate]
meta def elabPermGroupCertificate : Command.CommandElab := fun stx => do
  Command.liftTermElabM do
    let name := stx[1].getId.toString
    let sStx := stx[3]
    let s ← Term.elabTerm sStx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let s ← instantiateMVars s
    let out ← match ← arrayElems? s with
      | some gens =>
        let sSrc := ((sStx.updateTrailing "".toRawSubstring).reprint.getD "").trimAscii.toString
        let elemSrc := match arraySources? sStx with
          | some xs => xs.toList.map fun e =>
              ((e.updateTrailing "".toRawSubstring).reprint.getD "").trimAscii.toString
          | none => (List.range gens.length).map fun k => s!"({sSrc})[{k}]'(by decide)"
        certificateSource name (← degree s) gens elemSrc sSrc
      | none => do
        let mut result := none
        for ext in ← extensions do
          if result.isNone then result ← ext.certificate? name s sStx
        let some out := result
          | throwError "#perm_group_certificate: expected an array of Hex permutations"
        pure out
    logInfo out

end Hex.PermGroup.Kernel.Tactic
