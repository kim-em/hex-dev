/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert

public section

/-!
The automorphism-pruning certificate producer. Everything here is
untrusted: candidates are validated by `validateKey?` (the trusted
`checkKey` replay), and every automorphism prune is self-checked with
the checker's own predicates (`childAutomOk`, the literal conjunction
replayed by `checkChildren`) before use, so a producer bug can only
cost performance, never soundness. The honest code-prune producer
`certifyNode` stays in `Cert` untouched; the completeness theorems and
the exhaustive fallback (`Complete`) are stated about it and carry
totality.

Automorphisms are harvested nauty-style from pairs of aligned leaves:
`γ[ref[i]] = lab[i]` (the `workperm` shape) against the pass's first
leaf and the current best-achieving leaf, kept only when the checker's
`checkAutom` accepts. A generator discovered at a divergence node
respects that node's ordered partition and every coarser ancestor
partition, so a single global store plus a per-node cell-respect
filter (`respectsMasks`) makes deep discoveries reusable higher up. The
per-node orbit walk (`witness?`) composes filtered generators by
breadth-first search inside the target cell; this under-approximates
the true partition stabilizer (products of individually non-respecting
generators may respect the partition) and is a heuristic, not a group
computation.

Skipping invariant: a child offset is pruned only against a strictly
earlier offset, so every pruned subtree's key equals the key of an
earlier offset that was either explored or pruned against a yet
earlier one; the chain strictly decreases and terminates at an
explored representative already folded into the running maximum.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The generator-store cap. Beyond it, admission overwrites the last
slot (bounded replacement) rather than stopping. -/
def genCap : Nat := 500

/-- Untrusted automorphism state threaded through the pruning
producers. -/
structure AutState where
  /-- Verified generators paired with their inverses. -/
  gens : Array (Array Nat × Array Nat) := #[]
  /-- Bumped on every successful admission (including cap-slot
  replacement), so per-node filter caches know when to refresh. -/
  gen : Nat := 0
  /-- Union-find orbit array over vertices, for admission control. -/
  orbits : Array Nat := #[]
  /-- Number of orbit classes of `orbits`. -/
  numorbits : Nat := 0
  /-- The first leaf labelling seen by the current pass. -/
  firstLeaf : Option (Array Nat) := none
  /-- The previous leaf labelling seen by the current pass. -/
  prevLeaf : Option (Array Nat) := none
  /-- A fixed reference leaf from an earlier pass (the achiever). -/
  refLeaf : Option (Array Nat) := none
  /-- Remaining node budget; `none` is unbounded. -/
  budget : Option Nat := none
  /-- The budget ran out; the caller must discard the result. -/
  exhausted : Bool := false

/-- Fresh state over `nn` vertices. -/
def AutState.init (nn : Nat) (budget : Option Nat := none) : AutState :=
  { orbits := Array.range nn, numorbits := nn, budget }

/-- Charge one node against the budget. -/
def AutState.charge (st : AutState) : AutState :=
  match st.budget with
  | none => st
  | some 0 => { st with exhausted := true }
  | some (b + 1) => { st with budget := some b }

/-- The permutation carrying labelling `ref` onto labelling `lab`:
`γ[ref[i]] = lab[i]` (nauty's `workperm` composition). -/
def composeOnto (ref lab : Array Nat) : Array Nat := Id.run do
  let mut γ : Array Nat := .replicate ref.size 0
  for i in [0 : ref.size] do
    γ := γ.set! ref[i]! lab[i]!
  return γ

/-- The composition `f ∘ π` as arrays over `[0, nn)`. -/
def composePerm (f π : Array Nat) (nn : Nat) : Array Nat :=
  (Array.range nn).map fun x => f[π[x]!]!

private def isIdentity (γ : Array Nat) (nn : Nat) : Bool :=
  (List.range nn).all fun v => γ[v]! == v

/-- Admit one candidate automorphism: reject the identity and
duplicates, verify with the checker's own `checkAutom`, and store the
inverse alongside. Admission past the cap overwrites the last slot,
preferring generators that merge orbits. -/
def AutState.admit (ctx : Ctx) (st : AutState) (γ : Array Nat) :
    AutState := Id.run do
  if isIdentity γ ctx.n then
    return st
  if st.gens.any (fun p => p.1 == γ) then
    return st
  -- untrusted fast filter (nauty's edge-wise test); the trusted
  -- checkAutom runs only when a record is emitted
  unless γ.size == ctx.n &&
      ((List.range ctx.n).all fun v => γ[v]! < ctx.n) &&
      isautom ctx γ do
    return st
  let (orbits, numorbits) := orbjoin st.orbits γ ctx.n
  let grew := numorbits < st.numorbits
  if st.gens.size < genCap then
    return { st with
             gens := st.gens.push (γ, invPerm γ)
             gen := st.gen + 1
             orbits := orbits
             numorbits := numorbits }
  if grew then
    return { st with
             gens := st.gens.set! (genCap - 1) (γ, invPerm γ)
             gen := st.gen + 1
             orbits := orbits
             numorbits := numorbits }
  return st

/-- Harvest generators at a leaf: compose the leaf labelling against
the pass's first leaf, the previous leaf, and the fixed reference
leaf. -/
def AutState.harvest (ctx : Ctx) (st : AutState) (lab : Array Nat) :
    AutState := Id.run do
  let mut st := st
  match st.firstLeaf with
  | none => st := { st with firstLeaf := some lab }
  | some ref => st := st.admit ctx (composeOnto ref lab)
  if let some ref := st.prevLeaf then
    st := st.admit ctx (composeOnto ref lab)
  if let some ref := st.refLeaf then
    st := st.admit ctx (composeOnto ref lab)
  return { st with prevLeaf := some lab }

/-- The vertex bitset of every cell of the node's ordered partition. -/
def cellMasks (ctx : Ctx) (rsLab rsPtn : Array Nat) (level : Nat) :
    List Nat :=
  (cells rsPtn level ctx.n).map fun p =>
    (List.range (p.2 + 1 - p.1)).foldl
      (fun m o => insert m rsLab[p.1 + o]!) 0

/-- Does `γ` map every cell bitset onto itself? Since the cells
partition the vertices and `γ` is a bijection, per-cell image equality
is exactly setwise cell preservation. Untrusted fast filter. -/
def respectsMasks (ctx : Ctx) (masks : List Nat) (γ : Array Nat) :
    Bool :=
  masks.all fun m => image (fun w => γ[w]!) ctx.n m == m

/-- The literal `.autom` acceptance predicate of `checkChildren`,
including the earlier-offset requirement: emitted records satisfy
exactly what the trusted replay re-checks. -/
def childAutomOk (ctx : Ctx) (rsLab rsPtn : Array Nat) (level tc : Nat)
    (o o' : Nat) (γ : Array Nat) : Bool :=
  decide (o' < o) &&
  checkAutom ctx.g γ ctx.n &&
  checkCellsPerm
    (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
    (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1
    ((breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1.map
      fun w => γ[w]!)
    (level + 1) ctx.n

/-- Search for a witness pruning target-cell offset `o` onto an
earlier offset: breadth-first search from `v = rsLab[tc + o]` over the
filtered generators and their inverses, composing the witness along
the path. The caller decides how to validate the returned witness:
the key search may rely on the untrusted filters alone (a wrong skip
is caught by the trusted replay), while certificate emission runs the
literal checker predicate. -/
def witness? (ctx : Ctx) (rsLab : Array Nat) (tc : Nat)
    (usable : Array (Array Nat × Array Nat)) (o : Nat) :
    Option (Nat × Array Nat) := Id.run do
  if o == 0 || usable.isEmpty then
    return none
  let v := rsLab[tc + o]!
  let mut queue : Array (Nat × Array Nat) := #[(v, Array.range ctx.n)]
  let mut seen : Nat := insert 0 v
  let mut head := 0
  for _ in [0 : ctx.n] do
    if head < queue.size then
      let (u, π) := queue[head]!
      head := head + 1
      -- is `u` the branch vertex of an earlier offset?
      let mut hit : Option Nat := none
      for j in [0 : o] do
        if rsLab[tc + j]! == u then
          hit := some j
      match hit with
      | some o' => return some (o', π)
      | none => pure ()
      for (γ, γi) in usable do
        for f in [γ, γi] do
          let w := f[u]!
          unless elem seen w do
            seen := insert seen w
            queue := queue.push (w, composePerm f π ctx.n)
  return none

/-- The per-node generator filter, cached against the admission
generation: recompute only when generators were admitted since the
cache was built (freezing at node entry would lose prunes from
generators discovered under earlier children). -/
def usableGens (ctx : Ctx) (masks : List Nat) (st : AutState)
    (cache : Option (Nat × Array (Array Nat × Array Nat))) :
    Nat × Array (Array Nat × Array Nat) :=
  match cache with
  | some (cachedGen, u) =>
    if cachedGen == st.gen then (cachedGen, u)
    else (st.gen, st.gens.filter fun p => respectsMasks ctx masks p.1)
  | none => (st.gen, st.gens.filter fun p => respectsMasks ctx masks p.1)

/-- Build the certificate tree for the final best key, emitting
`.autom` records for target-cell offsets reachable from an earlier
offset through verified automorphisms. Untrusted; `checkKey`
revalidates everything. -/
def certifyNodeAutom (ctx : Ctx) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → List Nat →
      AutState → CertNode × AutState
  | 0, _, _, _, _, _, _, st => (.codePrune, st)
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st0 =>
    let st := st0.charge
    if st.exhausted then
      (.codePrune, st)
    else
      match bcodes with
      | [] => (.codePrune, st)
      | bc :: brest =>
        let rs := refine ctx level lab ptn active numcells
        match compare rs.longcode bc with
        | .lt => (.codePrune, st)
        | .gt => (.codePrune, st)
        | .eq =>
          if discreteAt rs.ptn level ctx.n then
            (.leaf, st.harvest ctx rs.lab)
          else
            let tcr := specMaketargetcell ctx rs.lab rs.ptn level
              tcLevel
            let masks := cellMasks ctx rs.lab rs.ptn level
            let (children, st', _) := (List.range tcr.2.2).foldl
              (fun (acc : List CertNode × AutState ×
                  Option (Nat × Array (Array Nat × Array Nat))) o =>
                let (kids, st, cache) := acc
                let cache' := usableGens ctx masks st cache
                let descend : Unit → List CertNode × AutState ×
                    Option (Nat × Array (Array Nat × Array Nat)) :=
                  fun _ =>
                  let br := breakout rs.lab rs.ptn (level + 1) tcr.1
                    rs.lab[tcr.1 + o]!
                  let (child, st') := certifyNodeAutom ctx tcLevel
                    fuel (level + 1) br.1 br.2.1 br.2.2
                    (numcells + 1) brest st
                  (child :: kids, st', some cache')
                match witness? ctx rs.lab tcr.1 cache'.2 o with
                | some (o', γ) =>
                  -- emission runs the literal checker predicate once
                  if childAutomOk ctx rs.lab rs.ptn level tcr.1 o o'
                      γ then
                    (.autom o' γ :: kids, st, some cache')
                  else
                    descend ()
                | none => descend ())
              ([], st, none)
            (.node children.reverse, st')

/-- The checker-coordinate refinement codes along the achieving
labelling's path: at each node the achieving child is the vertex the
leaf keeps at the target-cell start (breakout pins it there and later
refinement never moves a singleton). The walk mirrors `checkNode`'s
refine arguments, because the search's internal code chain uses the
transcription's own numcells convention and cannot be reused.
Untrusted; the replay recomputes everything. -/
def achieverCodes (ctx : Ctx) (tcLevel : Nat) (canonlab : Array Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → List Nat
  | 0, _, _, _, _, _ => []
  | fuel + 1, level, lab, ptn, active, numcells =>
    let rs := refine ctx level lab ptn active numcells
    if discreteAt rs.ptn level ctx.n then
      [rs.longcode]
    else
      let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
      let br := breakout rs.lab rs.ptn (level + 1) tcr.1
        canonlab[tcr.1]!
      rs.longcode :: achieverCodes ctx tcLevel canonlab fuel
        (level + 1) br.1 br.2.1 br.2.2 (numcells + 1)

/-- Trace-driven candidate production, per the SPEC: the transcribed
search runs once with tracing on, and the certificate pass translates
its trace — the harvested generators and the achieving labelling,
whose key is derived by `achieverCodes` and `leafRows` — into a
certificate against that key. No second search runs; the node budget
bounds the traced walk. Purely a candidate producer — nothing here is
trusted. -/
def produceCand (G : Colored n k) (budget : Option Nat) :
    Option (CertNode × Key) :=
  let ctx : Ctx := { n := n, g := rowsOf G }
  let tr := runColoredTraced G
  if budget.any fun b => decide (tr.result.numnodes > b) then
    none
  else
    let st1 := tr.autos.foldl (fun st γ => st.admit ctx γ)
      (AutState.init n budget)
    let st2 := { st1 with refLeaf := some tr.result.canonlab }
    let B : Key := ⟨achieverCodes ctx 100 tr.result.canonlab (n + 2) 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length ++ [codeSentinel],
      leafRows ctx tr.result.canonlab⟩
    let (cert, st3) := certifyNodeAutom ctx 100 n 1
      (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length B.codes st2
    if st3.exhausted then
      none
    else
      some (cert, B)

/-- The candidate pipeline plus trusted validation. -/
def certifyKeyCore (G : Colored n k) (budget : Option Nat) :
    Option (CertNode × Key) :=
  if n == 0 then
    validateKey? G .leaf ⟨[], []⟩
  else
    (produceCand G budget).bind fun cb => validateKey? G cb.1 cb.2

/-- Produce a checked canonical-key certificate: the pruned
branch-and-bound search finds the best key, the pruning certificate
pass rebuilds the tree against it, and the trusted `checkKey` replay
validates the pair. -/
def certifyKey? (G : Colored n k) : Option (CertNode × Key) :=
  certifyKeyCore G none

/-- The node-budgeted variant for tactic use: `none` on budget
exhaustion as well as on validation failure. -/
def certifyKeyBounded? (budget : Nat) (G : Colored n k) :
    Option (CertNode × Key) :=
  certifyKeyCore G (some budget)

/-- Every key a successful `certifyKeyCore` returns is the spec
key. -/
theorem certifyKeyCore_sound {G : Colored n k} {budget : Option Nat}
    {cert : CertNode} {B : Key}
    (h : certifyKeyCore G budget = some (cert, B)) :
    canonSpecKey G = B := by
  rw [certifyKeyCore] at h
  split at h
  · exact validateKey?_sound h
  · rcases hp : produceCand G budget with _ | cb
    · rw [hp] at h
      cases h
    · rw [hp] at h
      exact validateKey?_sound h

/-- Every key a successful `certifyKey?` returns is the spec key. -/
theorem certifyKey?_sound {G : Colored n k} {cert : CertNode}
    {B : Key} (h : certifyKey? G = some (cert, B)) :
    canonSpecKey G = B :=
  certifyKeyCore_sound h

end Hex.GraphIso.Nauty
