/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Ops
public import HexGraphIso.Uncolored
public import HexGraphIso.Kernel.IsoLit
public import HexGraphIso.Kernel.CheckKey
public import HexGraphIso.Kernel.RootCode
public import HexGraphIso.Nauty.Search
public meta import HexGraphIso.Nauty.Search
public meta import HexGraphIso.Nauty.CanonForm
public meta import HexGraphIso.Kernel.CheckKey
public meta import Lean

public section

/-!
# The Mathlib-free `graph_iso` tactic

`graph_iso` closes closed `Isomorphic G H` and `¬ Isomorphic G H` goals
over executable `Colored n k` values, and the uncoloured
`Graph.Isomorphic G H` and `¬ Graph.Isomorphic G H` goals over
`Graph n`. An uncoloured goal is coloured with the single colour zero
and transported back through `Graph.isomorphic_singleColor_iff`, so
both shapes run the same machinery. Three logical limits are optional
and may appear in any order:

```
graph_iso (maxSearchNodes := 200000) (maxCertRecords := 200000)
  (maxKernelSteps := 10000000)
```

A positive goal closes by the relabel shortcut when the right-hand
graph is syntactically a relabelling of the left-hand one, and
otherwise by the witness route: the compiled nauty-compatible search
runs at elaboration time as untrusted code and produces a literal
forward permutation, and the goal closes through `Kernel.checkIso` and
`Kernel.isIso_of_checkIso`, which check the permutation against
list-literal adjacency data, so the kernel performs the decisive replay
without unfolding the executable representation.

A negative goal closes by the root separator when the two root
refinement codes already differ, and otherwise by certificate replay:
the compiled search produces one canonical-key certificate per graph
and the kernel replays them with `Kernel.checkKey`. Search exhaustion
never closes a negative goal, and every failure leaves the goal
unchanged and names the limit that ran out. No path uses
`native_decide` and no axiom is introduced.
-/

namespace Hex.GraphIso

/-- The non-dependent runtime image of a coloured graph, so elaboration-time
meta code can evaluate closed `Colored n k` terms without knowing `n` and
`k` at compile time. -/
structure Raw where
  /-- The number of vertices. -/
  n : Nat
  /-- The number of colours. -/
  k : Nat
  /-- The packed adjacency rows. -/
  rows : Array (Nauty.VSet n)
  /-- The colour of each vertex. -/
  colors : Array Nat

instance : Inhabited Raw := ⟨{ n := 0, k := 0, rows := #[], colors := #[] }⟩

/-- The runtime image of a coloured graph. -/
def Colored.toRaw {n k : Nat} (G : Colored n k) : Raw where
  n := n
  k := k
  rows := Nauty.rowsOf G
  colors := .ofFn fun i : Fin n => (G.coloring.cells[i]).val

namespace Tactic

open Lean Elab Lean.Elab.Tactic Meta

/-- `set_option trace.graph_iso true` reports the route each call closes
through — `relabel`, `witness`, `root` or `certs` — and, for the
certificate route, the record counts the kernel replays; the
kernel-cost harness (`scripts/bench/graphiso_kernel_cost.py`) reads
these lines. -/
meta initialize registerTraceClass `graph_iso

/-- The logical limits of one `graph_iso` call. -/
meta structure Config where
  /-- Nodes the compiled search may visit per graph, both for the
  witness search and for the certificate producer. -/
  maxSearchNodes : Nat := 100000
  /-- Certificate records per graph the kernel replays. Exceeding it
  abandons the certificate route, not the tactic. -/
  maxCertRecords : Nat := 100000
  /-- Estimated kernel work: `checkCost n` for a witness, and
  `(records + autom + 2) * checkCost n` for a certificate pair. This is
  the limit that bounds the work the kernel itself does, so it is the
  one to raise for a goal the elaborator solves but the kernel cannot
  finish. -/
  maxKernelSteps : Nat := 5000000

meta section

/-- Elaborate the `(field := value)` limits of one `graph_iso` call. -/
declare_config_elab elabGraphIsoConfig Config

end

private meta unsafe def evalRawUnsafe (e : Expr) : MetaM Raw :=
  evalExpr Raw (mkConst ``Raw) e

@[implemented_by evalRawUnsafe]
private meta opaque evalRawCore (e : Expr) : MetaM Raw

/-- Evaluate a closed `Colored n k` expression to its runtime image. -/
meta def evalColored (e : Expr) : MetaM Raw := do
  let raw ← mkAppM ``Colored.toRaw #[e]
  try
    evalRawCore raw
  catch ex =>
    throwError "graph_iso: failed to evaluate the coloured graph\
        {indentExpr e}\n{ex.toMessageData}\
        \nThe tactic requires closed executable terms; definitions from \
        other modules may need `public meta import`."

/-- Run the nauty-compatible canonical search on a runtime graph. -/
meta def rawCanon (r : Raw) : Nauty.RunResult r.n := Id.run do
  let mut lab0 : Array Nat := #[]
  let mut ends : List Nat := []
  for c in [0 : r.k] do
    let mut found := false
    for v in [0 : r.n] do
      if r.colors[v]! == c then
        lab0 := lab0.push v
        found := true
    if found then
      ends := (lab0.size - 1) :: ends
  Nauty.run r.n r.rows lab0 ends.reverse

/-- Check a raw transporter: colour preservation and adjacency
transport. -/
meta def rawCheckIso (a b : Raw) (p : Array Nat) : Bool := Id.run do
  if p.size != a.n ∨ a.n != b.n ∨ a.k != b.k then
    return false
  for v in [0 : a.n] do
    if p[v]! ≥ a.n ∨ b.colors[p[v]!]! != a.colors[v]! then
      return false
  for u in [0 : a.n] do
    for v in [0 : a.n] do
      if b.rows[p[u]!]!.mem p[v]! != a.rows[u]!.mem v then
        return false
  return true

/-- The untrusted elaboration-time search: compare canonical forms and
compose the two canonical labels into a forward transporter. Returns the
transporter, or `none` for non-isomorphic inputs, together with the total
node count. -/
meta def rawFindIso (a b : Raw) : Option (Array Nat) × Nat := Id.run do
  if a.n != b.n ∨ a.k != b.k then
    return (none, 0)
  let ra := rawCanon a
  let rb := rawCanon b
  let nodes := ra.numnodes + rb.numnodes
  -- ordered colour-cell sizes must agree
  let mut sizesA : Array Nat := .replicate a.k 0
  let mut sizesB : Array Nat := .replicate a.k 0
  for v in [0 : a.n] do
    sizesA := sizesA.set! a.colors[v]! (sizesA[a.colors[v]!]! + 1)
    sizesB := sizesB.set! b.colors[v]! (sizesB[b.colors[v]!]! + 1)
  if sizesA != sizesB then
    return (none, nodes)
  if ra.canong.map Nauty.VSet.toNat != rb.canong.map Nauty.VSet.toNat then
    return (none, nodes)
  let mut p : Array Nat := .replicate a.n 0
  for i in [0 : a.n] do
    p := p.set! ra.canonlab[i]! rb.canonlab[i]!
  if rawCheckIso a b p then
    return (some p, nodes)
  return (none, nodes)

/-- Build the literal `Perm n` expression
`(Perm.ofNatArray? n #[...]).getD (Perm.id n)`. -/
meta def permExpr (n : Nat) (p : Array Nat) : MetaM Expr := do
  let listExpr ← mkListLit (mkConst ``Nat) (p.toList.map mkNatLit)
  let arrExpr ← mkAppM ``List.toArray #[listExpr]
  let opt ← mkAppM ``Perm.ofNatArray? #[mkNatLit n, arrExpr]
  let dflt ← mkAppM ``Perm.id #[mkNatLit n]
  mkAppM ``Option.getD #[opt, dflt]

/-- Build `of_decide_eq_true (Eq.refl true) : p` without reducing
`decide p` in the elaborator: the kernel performs the one decisive
evaluation when it checks the ascribed `Eq.refl`. `mkDecideProof`
would evaluate twice — once at elaboration, once at kernel check —
which doubles the cost of every replay obligation. -/
meta def kernelDecideProof (p : Expr) : MetaM Expr := do
  let inst ← synthInstance (← mkAppM ``Decidable #[p])
  let decideApp := mkApp2 (mkConst ``Decidable.decide) p inst
  let refl := mkApp2 (mkConst ``Eq.refl [1])
    (mkConst ``Bool) (mkConst ``Bool.true)
  let eqType ← mkAppM ``Eq #[decideApp, mkConst ``Bool.true]
  let h ← mkExpectedTypeHint refl eqType
  return mkApp3 (mkConst ``of_decide_eq_true) p inst h

/-- The flat Bool literal of a raw graph's adjacency matrix, in
row-major order. -/
meta def rawFlat (r : Raw) : List Bool :=
  (List.range r.n).flatMap fun i =>
    (List.range r.n).map fun j => r.rows[i]!.mem j

/-- A `List Bool` literal expression. -/
meta def boolListLit (bs : List Bool) : MetaM Expr :=
  mkListLit (mkConst ``Bool) (bs.map fun bb =>
    mkConst (if bb then ``Bool.true else ``Bool.false))

/-- The expression `e.graph.adjMatrix.data.toList` for a coloured
graph expression `e`: the tying side of a flat-literal equality. -/
meta def matrixListSide (e : Expr) : MetaM Expr := do
  mkAppM ``Vector.toList #[← mkAppM ``Matrix.data
    #[← mkAppM ``Graph.adjMatrix #[← mkAppM ``Colored.graph #[e]]]]

/-- The expression `Kernel.packRows n e.graph.adjMatrix.data.toList`:
the tying side of the packed-rows equality the negative routes
replay. -/
meta def matrixPackedSide (n : Nat) (e : Expr) : MetaM Expr := do
  mkAppM ``Kernel.packRows #[mkNatLit n, ← matrixListSide e]

/-- The packed rows of a runtime graph, row `v` at bits
`[n * v, n * (v + 1))`: the literal side of the packed-rows equality. -/
meta def rawPackedRows (r : Raw) : Nat :=
  (List.range r.n).foldr (fun v acc => r.rows[v]!.toNat + (acc <<< r.n)) 0

/-- One side of a negative goal: the graph expression, its runtime
image, the packed-rows literal, and the tie of the graph's adjacency to
that literal. Both negative routes replay against these, so each side
is evaluated and tied once per call. -/
meta structure Side where
  /-- The coloured graph expression. -/
  expr : Expr
  /-- Its runtime image. -/
  raw : Raw
  /-- The proof of `Kernel.packRows n expr.graph.adjMatrix.data.toList = lit`. -/
  tie : Expr
  /-- The packed-rows literal. -/
  lit : Expr

/-- Evaluate a coloured graph expression and tie it to its packed-rows
literal, one sequential kernel evaluation of the graph's adjacency. -/
meta def mkSide (e : Expr) : MetaM Side := do
  let r ← evalColored e
  let lit := mkNatLit (rawPackedRows r)
  let h ← kernelDecideProof (← mkAppM ``Eq #[← matrixPackedSide r.n e, lit])
  return { expr := e, raw := r, tie := h, lit := lit }

/-- Reify a certificate tree as a literal expression. -/
meta partial def certNodeExpr : Nauty.CertNode → MetaM Expr
  | .leaf => return mkConst ``Nauty.CertNode.leaf
  | .codePrune => return mkConst ``Nauty.CertNode.codePrune
  | .autom o γ =>
    return mkApp2 (mkConst ``Nauty.CertNode.autom) (mkNatLit o) (toExpr γ)
  | .node children => do
    let elems ← children.mapM certNodeExpr
    return mkApp (mkConst ``Nauty.CertNode.node)
      (← mkListLit (mkConst ``Nauty.CertNode) elems)

/-- Reify a literal canonical key as an expression. -/
meta def keyExpr (K : Kernel.Key) : Expr :=
  mkApp2 (mkConst ``Kernel.Key.mk) (toExpr K.codes) (toExpr K.rows)

/-- Match `Isomorphic G H` (returning `(false, n, k, G, H)`) or
`¬ Isomorphic G H` (returning `true` first); `none` for other goals. -/
meta def matchGoal? (target : Expr) : MetaM (Option (Bool × Expr × Expr × Expr × Expr)) := do
  let t ← whnfR target
  match_expr t with
  | Isomorphic n k G H => return some (false, n, k, G, H)
  | Not p =>
    let p ← whnfR p
    match_expr p with
    | Isomorphic n k G H => return some (true, n, k, G, H)
    | _ => return none
  | _ => return none

/-- Match the uncoloured `Graph.Isomorphic G H` (returning
`(false, n, G, H)`) or its negation (returning `true` first); `none`
for other goals. -/
meta def matchUncoloredGoal? (target : Expr) :
    MetaM (Option (Bool × Expr × Expr × Expr)) := do
  let t ← whnfR target
  match_expr t with
  | _root_.Hex.Graph.Isomorphic n G H => return some (false, n, G, H)
  | Not p =>
    let p ← whnfR p
    match_expr p with
    | _root_.Hex.Graph.Isomorphic n G H => return some (true, n, G, H)
    | _ => return none
  | _ => return none

private meta unsafe def evalNatUnsafe (e : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatUnsafe]
private meta opaque evalNatCore (e : Expr) : MetaM Nat

private meta unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool :=
  evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolUnsafe]
private meta opaque evalBoolCore (e : Expr) : MetaM Bool

private meta unsafe def evalCertUnsafe (e : Expr) :
    MetaM (Option (Nauty.CertNode × Kernel.Key)) := do
  evalExpr (Option (Nauty.CertNode × Kernel.Key))
    (← mkAppM ``Option
      #[← mkAppM ``Prod
        #[mkConst ``Nauty.CertNode, mkConst ``Kernel.Key]]) e

@[implemented_by evalCertUnsafe]
private meta opaque evalCertCore (e : Expr) :
    MetaM (Option (Nauty.CertNode × Kernel.Key))

private meta def countAutom : Nauty.CertNode → Nat
  | .leaf | .codePrune => 0
  | .autom _ _ => 1
  | .node cs => cs.foldl (fun a c => a + countAutom c) 0

/-- The root-separator leg of the negative path: when the root
refinement codes already differ — the typical case for irregular pairs
— the kernel obligation is a single refinement per graph, so the leg
always runs. -/
meta def proveNotIsoRoot? (G H : Side) : MetaM (Option Expr) := do
  unless (← evalBoolCore (← mkAppM ``Kernel.rootSeparates #[G.expr, H.expr])) do
    return none
  let sepTerm ← mkAppM ``Kernel.rootDiff #[G.expr, H.expr, G.lit, H.lit]
  let hs ← kernelDecideProof
    (← mkAppM ``Eq #[sepTerm, mkConst ``Bool.true])
  trace[graph_iso] "route=root n={G.raw.n}"
  return some (← mkAppM ``Kernel.not_isomorphic_of_rootCode #[G.tie, H.tie, hs])

/-- The certificate leg of the negative path: budgeted certificate
production on both sides compiled, the key comparison compiled, and the
kernel replaying only two Boolean `Kernel.checkKey` certificates plus
`checkDiffL`. Returns the limit that ran out when the route is
unavailable; throws when the keys agree, because the goal is then
unprovable. -/
meta def proveNotIsoCerts (cfg : Config) (G H : Side) :
    MetaM (Except MessageData Expr) := do
  -- deliberately the VALIDATED bounded producer: the ~10ms compiled
  -- validation guarantees every emitted kernel obligation replays
  -- successfully — a bad candidate must fall back here, not surface as
  -- a kernel rejection at module finalization
  let bounded (e : Expr) :
      MetaM (Option (Nauty.CertNode × Kernel.Key)) := do
    evalCertCore (← mkAppM ``Kernel.certifyKey?
      #[mkNatLit cfg.maxSearchNodes, e])
  let exhausted : MessageData :=
    m!"certificate production did not finish within maxSearchNodes := \
      {cfg.maxSearchNodes}"
  let some (certG, BG) ← bounded G.expr | return .error exhausted
  let some (certH, BH) ← bounded H.expr | return .error exhausted
  unless Nauty.checkDiffL BG BH do
    throwError "graph_iso: the graphs are isomorphic; the negative goal \
        is not provable"
  -- one `checkCost` per record plus one per `.autom` payload, both sides
  let nv := BG.rows.length
  let steps := (certG.size + certH.size + countAutom certG +
    countAutom certH + 2) * checkCost nv
  unless certG.size ≤ cfg.maxCertRecords && certH.size ≤ cfg.maxCertRecords do
    return .error m!"the certificates hold {certG.size} and {certH.size} \
      records but maxCertRecords := {cfg.maxCertRecords}"
  unless steps ≤ cfg.maxKernelSteps do
    return .error m!"replaying them costs about {steps} kernel steps but \
      maxKernelSteps := {cfg.maxKernelSteps}"
  let mkCheck (side : Side) (cert : Nauty.CertNode) (B : Kernel.Key) :
      MetaM Expr := do
    let checkTerm ← mkAppM ``Kernel.checkKey
      #[side.expr, side.lit, ← certNodeExpr cert, keyExpr B]
    kernelDecideProof (← mkAppM ``Eq #[checkTerm, mkConst ``Bool.true])
  let hG ← mkCheck G certG BG
  let hH ← mkCheck H certH BH
  let diffTerm ← mkAppM ``Nauty.checkDiffL #[keyExpr BG, keyExpr BH]
  let hd ← kernelDecideProof
    (← mkAppM ``Eq #[diffTerm, mkConst ``Bool.true])
  let proof ← mkAppM ``Kernel.not_isomorphic_of_checkKeys
    #[G.tie, H.tie, hG, hH, hd]
  trace[graph_iso] "route=certs n={nv} records={certG.size + certH.size} \
      recordsG={certG.size} recordsH={certH.size} \
      autom={countAutom certG + countAutom certH} steps={steps}"
  return .ok proof

/-- Produce a proof of `¬ Isomorphic G H` for closed executable coloured
graphs: the root separator first, then certificate replay. The
certificate obligations replay only because their whole closure is
exposed to the module-finalization kernel; the regression ladder in
`HexGraphIso.ModuleBoundaryTests` pins that closure. Shared by the core
negative branch and downstream extensions (the Mathlib layer calls it
on the encodings). -/
meta def proveNotIso (cfg : Config) (GE HE : Expr) : MetaM Expr := do
  let G ← mkSide GE
  let H ← mkSide HE
  match ← proveNotIsoRoot? G H with
  | some proof => return proof
  | none =>
    match ← proveNotIsoCerts cfg G H with
    | .ok proof => return proof
    | .error reason =>
      throwError "graph_iso: every negative route is exhausted: the root \
          refinement codes agree, and {reason}"

/-- The witness leg of the positive path: tie each side's adjacency,
colouring and the transporter to literals, and check the transporter on
those literals. Returns the permutation expression and the proof of
`IsIso G H p`, which the core branch wraps as `Isomorphic` and
downstream extensions decode. -/
meta def proveIsIso (cfg : Config) (n : Nat) (GE HE : Expr) (a b : Raw)
    (p : Array Nat) (nodes : Nat) : MetaM (Expr × Expr) := do
  if checkCost n > cfg.maxKernelSteps then
    throwError "graph_iso: replay exhausted: checking the transporter \
        takes {checkCost n} steps but maxKernelSteps := \
        {cfg.maxKernelSteps}"
  let pE ← permExpr n p
  let natLit (xs : List Nat) : MetaM Expr :=
    mkListLit (mkConst ``Nat) (xs.map mkNatLit)
  let kE := (← whnfD (← inferType GE)).getAppArgs[1]!
  let finVal (bound : Expr) : MetaM Expr :=
    mkAppOptM ``Fin.val #[some bound]
  let cellSide (e : Expr) : MetaM Expr := do
    mkAppM ``List.map #[← finVal kE, ← mkAppM ``Vector.toList
      #[← mkAppM ``Coloring.cells #[← mkAppM ``Colored.coloring #[e]]]]
  let permSide : MetaM Expr := do
    mkAppM ``List.map #[← finVal (mkNatLit n),
      ← mkAppM ``Vector.toList #[← mkAppM ``Perm.vec #[pE]]]
  let tie (lhs rhs : Expr) : MetaM Expr := do
    kernelDecideProof (← mkAppM ``Eq #[lhs, rhs])
  let hA ← tie (← matrixListSide GE) (← boolListLit (rawFlat a))
  let hB ← tie (← matrixListSide HE) (← boolListLit (rawFlat b))
  let hcA ← tie (← cellSide GE) (← natLit a.colors.toList)
  let hcB ← tie (← cellSide HE) (← natLit b.colors.toList)
  let hp ← tie (← permSide) (← natLit p.toList)
  let chkTerm ← mkAppM ``Kernel.checkIso
    #[mkNatLit n, ← boolListLit (rawFlat a), ← boolListLit (rawFlat b),
      ← natLit a.colors.toList, ← natLit b.colors.toList,
      ← natLit p.toList]
  let hchk ← kernelDecideProof
    (← mkAppM ``Eq #[chkTerm, mkConst ``Bool.true])
  let proof ← mkAppM ``Kernel.isIso_of_checkIso
    #[hA, hB, hcA, hcB, hp, hchk]
  trace[graph_iso] "route=witness n={n} nodes={nodes}"
  return (pE, proof)

/-- A `graph_iso` goal handler contributed by a downstream library.
A `public meta def` of this type tagged `@[graph_iso_extension]`
extends the same `graph_iso` syntax to that library's goal shapes. -/
meta structure Extension where
  /-- Handle a goal, returning its proof term, or `none` when the goal
  shape is not this extension's. -/
  prove? : Config → Expr → MetaM (Option Expr)

meta section

open Lean

/-- The registered `graph_iso` extensions, in declaration order. -/
initialize extensionExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss => nss.flatten
    addEntryFn := fun s n => s.push n
  }

initialize registerBuiltinAttribute {
  name := `graph_iso_extension
  descr := "register a `graph_iso` goal handler for extra goal shapes"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    ensureAttrDeclIsMeta `graph_iso_extension decl kind
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `graph_iso_extension kind
    let declType := (← getConstInfo decl).type
    unless declType.isConstOf ``Extension do
      throwAttrDeclNotOfExpectedType `graph_iso_extension decl declType
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

/-- Prove a `graph_iso` goal over executable coloured graphs. -/
meta def proveGraphIso (cfg : Config) (target : Expr)
    (parsed : Bool × Expr × Expr × Expr × Expr) : MetaM Expr := do
  let (negative, nE, _kE, GE, HE) := parsed
  if (← instantiateMVars target).hasMVar then
    throwError "graph_iso: the goal contains metavariables; both graphs \
        must be closed terms"
  let n ← evalNatCore nE
  if negative then
    let proof ← proveNotIso cfg GE HE
    unless ← isDefEq (← inferType proof) target do
      throwError "graph_iso: internal final proof mismatch"
    return proof
  else
    -- relabel-shaped positives close by `isomorphic_relabel` with no
    -- kernel evaluation and no search: peel definitions off `H` and match
    let rec peel (e : Expr) : Nat → MetaM Expr
      | 0 => return e
      | fuel + 1 => do
        if e.isAppOf ``Colored.relabel then return e
        match ← unfoldDefinition? e with
        | some e' => peel e' fuel
        | none => return e
    let HEr ← peel HE 8
    if HEr.isAppOf ``Colored.relabel then
      let args := HEr.getAppArgs
      if args.size ≥ 2 then
        let Gsub := args[args.size - 2]!
        let lE := args[args.size - 1]!
        if ← isDefEq Gsub GE then
          let proof ← mkAppM ``isomorphic_relabel #[GE, lE]
          if ← isDefEq (← inferType proof) target then
            trace[graph_iso] "route=relabel n={n}"
            return proof
    let a ← evalColored GE
    let b ← evalColored HE
    let (transporter?, nodes) := rawFindIso a b
    if nodes > cfg.maxSearchNodes then
      throwError "graph_iso: search exhausted: visited {nodes} nodes but \
          maxSearchNodes := {cfg.maxSearchNodes}"
    match transporter? with
    | none =>
        throwError "graph_iso: the graphs are not isomorphic; the positive \
            goal is not provable"
    | some p =>
        let (pE, isIso) ← proveIsIso cfg n GE HE a b p nodes
        let proof ← mkAppM ``Isomorphic.intro #[pE, isIso]
        unless ← isDefEq (← inferType proof) target do
          throwError "graph_iso: internal final proof mismatch"
        return proof

/-- Prove a `graph_iso` goal over executable uncoloured graphs: colour
every vertex alike, hand the pair to `proveGraphIso`, and transport the
conclusion back through `Graph.isomorphic_singleColor_iff`. Both
directions of that equivalence are proof terms, so the uncoloured route
costs the kernel nothing beyond the coloured obligation and the one
`0 < n` decision. -/
meta def proveGraphIsoUncolored (cfg : Config) (target : Expr)
    (parsed : Bool × Expr × Expr × Expr) : MetaM Expr := do
  let (negative, nE, GE, HE) := parsed
  if (← instantiateMVars target).hasMVar then
    throwError "graph_iso: the goal contains metavariables; both graphs \
        must be closed terms"
  let hpos ← kernelDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, nE])
  let GC ← mkAppM ``Hex.Graph.singleColor #[GE, hpos]
  let HC ← mkAppM ``Hex.Graph.singleColor #[HE, hpos]
  let corr ← mkAppM ``Hex.Graph.isomorphic_singleColor_iff #[GE, HE, hpos]
  let coloured ← mkAppM ``Isomorphic #[GC, HC]
  let proof ← if negative then do
    let inner ← proveGraphIso cfg (← mkAppM ``Not #[coloured])
      (true, nE, mkNatLit 1, GC, HC)
    mkAppM ``mt #[← mkAppM ``Iff.mpr #[corr], inner]
  else do
    let inner ← proveGraphIso cfg coloured (false, nE, mkNatLit 1, GC, HC)
    mkAppM ``Iff.mp #[corr, inner]
  unless ← isDefEq (← inferType proof) target do
    throwError "graph_iso: internal final proof mismatch"
  return proof

end Tactic

open Lean Elab Lean.Elab.Tactic Meta Lean.Parser.Tactic in
/-- Close a closed `Isomorphic` or `¬ Isomorphic` goal over executable
graphs, coloured (`Colored n k`) or uncoloured (`Graph n`).

Three logical limits are optional and may appear in any order:

```
graph_iso (maxSearchNodes := 200000) (maxCertRecords := 200000)
  (maxKernelSteps := 10000000)
```

They default to 100000, 100000, and 5000000. Importing `HexGraphIsoMathlib`
extends this same tactic to Mathlib `SimpleGraph` goals. See the module
docstring for the proof routes. -/
syntax (name := graphIsoTac) "graph_iso" optConfig : tactic

open Lean Elab Lean.Elab.Tactic Meta in
/-- Elaborator for `graph_iso`: parse the optional limits, then dispatch to
`proveGraphIso` on the core `Colored` goal shapes, `proveGraphIsoUncolored`
on the `Graph` shapes, and then each registered `Extension` in turn. -/
@[tactic graphIsoTac] meta def evalGraphIsoTac : Tactic := fun stx => do
  let cfg ← Tactic.elabGraphIsoConfig stx[1]
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let proof ← do
      match ← Tactic.matchGoal? target with
      | some parsed => Tactic.proveGraphIso cfg target parsed
      | none =>
      match ← Tactic.matchUncoloredGoal? target with
      | some parsed => Tactic.proveGraphIsoUncolored cfg target parsed
      | none =>
        let exts ← Tactic.extensions
        let mut result : Option Expr := none
        for ext in exts do
          if result.isNone then
            result ← ext.prove? cfg target
        match result with
        | some prf => pure prf
        | none =>
          if exts.isEmpty then
            throwError "graph_iso: the goal is not an `Isomorphic` or \
                `¬ Isomorphic` proposition over executable graphs, \
                coloured or not:{indentExpr target}\
                \nFor `SimpleGraph` goals, import `HexGraphIsoMathlib`."
          else
            throwError "graph_iso: the goal is not a supported isomorphism \
                proposition:{indentExpr target}"
    goal.assign proof
  replaceMainGoal []

end Hex.GraphIso
