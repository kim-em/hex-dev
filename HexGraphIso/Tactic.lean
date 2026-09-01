/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Canon
public import HexGraphIso.Nauty.Search
public meta import HexGraphIso.Nauty.Search
public meta import Lean

public section

/-!
# The Mathlib-free `graph_iso` tactic

`graph_iso` closes closed `Isomorphic G H` and `¬ Isomorphic G H` goals
over executable `Colored n k` values. The three logical limits are
optional, may appear in any order, and may appear at most once each:

```
graph_iso (maxNodes := 200000) (maxCertNodes := 200000) (maxCheckerSteps := 10000000)
```

For a positive goal, the compiled nauty-compatible search runs at
elaboration time as untrusted code and produces a literal forward
permutation; the goal closes through the replay-bounded `checkIso?` and
its soundness theorem, so the kernel performs the decisive replay. For a
negative goal, the kernel currently replays the bounded reference
decision `isIso G H = false` through `isIso_eq_false_iff`; the
certificate-based negative path replaces this replay before release, per
SPEC/Libraries/hex-graph-iso.md § Canonical certificates, extending the
feasible size without changing the trust story. Search exhaustion never
closes a negative goal, and every failure leaves the goal unchanged and
reports the phase and logical limit that failed. No path uses
`native_decide` and no axiom is introduced.
-/

namespace Hex.GraphIso

/-- Checked permutation construction from raw entries, for literal data
emitted by tactics: entries must be in range, duplicate-free, and
complete. -/
@[expose] def permOfNatArray? (n : Nat) (a : Array Nat) : Option (Perm n) :=
  if h : a.size = n ∧ ∀ i, (hi : i < a.size) → a[i] < n then
    Perm.ofVector? (Hex.Vector.ofFn' fun i : Fin n =>
      ⟨a[i.val]'(h.1.symm ▸ i.isLt), h.2 i.val (h.1.symm ▸ i.isLt)⟩)
  else
    none

theorem isomorphic_of_checkIso? {n k : Nat} {G H : Colored n k}
    {replay : ReplayLimits} {p : Perm n}
    (h : checkIso? replay G H p = some true) : Isomorphic G H :=
  Isomorphic.intro p ((checkIso?_some h).mp rfl)

theorem not_isomorphic_of_isIso_eq_false {n k : Nat} {G H : Colored n k}
    (h : isIso G H = false) : ¬ Isomorphic G H :=
  (isIso_eq_false_iff G H).mp h

/-- The non-dependent runtime image of a coloured graph, so elaboration-time
meta code can evaluate closed `Colored n k` terms without knowing `n` and
`k` at compile time. -/
structure Raw where
  /-- The number of vertices. -/
  n : Nat
  /-- The number of colours. -/
  k : Nat
  /-- Adjacency bitset rows. -/
  rows : Array Nat
  /-- The colour of each vertex. -/
  colors : Array Nat
deriving Inhabited, Repr

/-- The runtime image of a coloured graph. -/
def Colored.toRaw {n k : Nat} (G : Colored n k) : Raw where
  n := n
  k := k
  rows := Nauty.rowsOf G
  colors := .ofFn fun i : Fin n => (G.coloring.cells[i]).val

namespace Tactic

open Lean Elab Lean.Elab.Tactic Meta

/-- The parsed logical limits of one `graph_iso` call. -/
meta structure Config where
  maxNodes : Nat := 100000
  maxCertNodes : Nat := 100000
  maxCheckerSteps : Nat := 5000000

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
meta def rawCanon (r : Raw) : Nauty.RunResult := Id.run do
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
      if (b.rows[p[u]!]! >>> p[v]!) &&& 1 != (a.rows[u]! >>> v) &&& 1 then
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
  if ra.canong != rb.canong then
    return (none, nodes)
  let mut p : Array Nat := .replicate a.n 0
  for i in [0 : a.n] do
    p := p.set! ra.canonlab[i]! rb.canonlab[i]!
  if rawCheckIso a b p then
    return (some p, nodes)
  return (none, nodes)

/-- Build the literal `Perm n` expression
`(permOfNatArray? n #[...]).getD (Perm.id n)`. -/
meta def permExpr (n : Nat) (p : Array Nat) : MetaM Expr := do
  let listExpr ← mkListLit (mkConst ``Nat) (p.toList.map mkNatLit)
  let arrExpr ← mkAppM ``List.toArray #[listExpr]
  let opt ← mkAppM ``permOfNatArray? #[mkNatLit n, arrExpr]
  let dflt ← mkAppM ``Perm.id #[mkNatLit n]
  mkAppM ``Option.getD #[opt, dflt]

/-- Match `Isomorphic G H` (returning `(false, n, k, G, H)`) or
`¬ Isomorphic G H` / `Isomorphic G H → False` (returning `true` first). -/
meta def matchGoal (target : Expr) : MetaM (Bool × Expr × Expr × Expr × Expr) := do
  let t ← whnfR target
  match_expr t with
  | Isomorphic n k G H => return (false, n, k, G, H)
  | Not p =>
    let p ← whnfR p
    match_expr p with
    | Isomorphic n k G H => return (true, n, k, G, H)
    | _ => throwError "graph_iso: the goal is not an `Isomorphic` or \
        `¬ Isomorphic` proposition over executable coloured graphs:{indentExpr target}"
  | _ => throwError "graph_iso: the goal is not an `Isomorphic` or \
      `¬ Isomorphic` proposition over executable coloured graphs:{indentExpr target}"

private meta unsafe def evalNatUnsafe (e : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatUnsafe]
private meta opaque evalNatCore (e : Expr) : MetaM Nat

/-- Prove a `graph_iso` goal. -/
meta def proveGraphIso (cfg : Config) (target : Expr) : MetaM Expr := do
  let (negative, nE, _kE, GE, HE) ← matchGoal target
  if (← instantiateMVars target).hasMVar then
    throwError "graph_iso: the goal contains metavariables; both graphs \
        must be closed terms"
  let n ← evalNatCore nE
  let a ← evalColored GE
  let b ← evalColored HE
  let (transporter?, nodes) := rawFindIso a b
  if nodes > cfg.maxNodes then
    throwError "graph_iso: search exhausted: visited {nodes} nodes but \
        maxNodes := {cfg.maxNodes}"
  if negative then
    match transporter? with
    | some _ =>
        throwError "graph_iso: the graphs are isomorphic; the negative goal \
            is not provable"
    | none =>
        -- Kernel replay of the bounded reference decision; the certificate
        -- path will replace this replay (see the module docstring).
        if searchCost n > cfg.maxNodes then
          throwError "graph_iso: negative replay exhausted: the kernel \
              replay enumerates {searchCost n} candidate labellings but \
              maxNodes := {cfg.maxNodes}"
        let isIsoTerm ← mkAppM ``isIso #[GE, HE]
        let eqType ← mkAppM ``Eq #[isIsoTerm, mkConst ``Bool.false]
        let checked ← mkDecideProof eqType
        let proof ← mkAppM ``not_isomorphic_of_isIso_eq_false #[checked]
        unless ← isDefEq (← inferType proof) target do
          throwError "graph_iso: internal final proof mismatch"
        return proof
  else
    match transporter? with
    | none =>
        throwError "graph_iso: the graphs are not isomorphic; the positive \
            goal is not provable"
    | some p =>
        if checkCost n > cfg.maxCheckerSteps then
          throwError "graph_iso: replay exhausted: checking the transporter \
              takes {checkCost n} steps but maxCheckerSteps := \
              {cfg.maxCheckerSteps}"
        let pE ← permExpr n p
        let replayE ← mkAppM ``ReplayLimits.mk #[mkNatLit cfg.maxCheckerSteps]
        let checkTerm ← mkAppM ``checkIso? #[replayE, GE, HE, pE]
        let someTrue ← mkAppOptM ``Option.some #[mkConst ``Bool, mkConst ``Bool.true]
        let eqType ← mkAppM ``Eq #[checkTerm, someTrue]
        let checked ← mkDecideProof eqType
        let proof ← mkAppM ``isomorphic_of_checkIso? #[checked]
        unless ← isDefEq (← inferType proof) target do
          throwError "graph_iso: internal final proof mismatch"
        return proof

end Tactic

open Lean Elab Lean.Elab.Tactic Meta in
/-- Close a closed `Isomorphic` or `¬ Isomorphic` goal over executable
coloured graphs. See the module docstring for the limit syntax. -/
syntax (name := graphIsoTac) "graph_iso" (" (" ident " := " num ")")* : tactic

open Lean Elab Lean.Elab.Tactic Meta in
@[tactic graphIsoTac] meta def evalGraphIsoTac : Tactic := fun stx => do
  let args := stx[1].getArgs
  let mut cfg : Tactic.Config := {}
  let mut seen : List String := []
  for arg in args do
    let name := arg[1].getId.toString
    let value := arg[3].isNatLit?.getD 0
    if seen.contains name then
      throwError "graph_iso: duplicate limit `{name}`"
    seen := name :: seen
    match name with
    | "maxNodes" => cfg := { cfg with maxNodes := value }
    | "maxCertNodes" => cfg := { cfg with maxCertNodes := value }
    | "maxCheckerSteps" => cfg := { cfg with maxCheckerSteps := value }
    | _ => throwError "graph_iso: unknown limit `{name}`"
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let proof ← Tactic.proveGraphIso cfg target
    goal.assign proof
  replaceMainGoal []

end Hex.GraphIso
