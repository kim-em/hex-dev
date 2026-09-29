/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Bisection

public section

namespace Hex.RealClosure.Bisection

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
variable [NatCast E] [Neg E] [Inv E]

/-- A finite interval checked against the exact current head and sign operation.
Its root count is computed once for this actual domain and retained. -/
structure Cell (sign : E → Int) (p : DensePoly E) where
  private mk ::
  lower : E
  upper : E
  domain : Sturm.PreparedDomain E
  bound : domain.sign = sign ∧ domain.head = p ∧
    domain.lower = .finite lower ∧ domain.upper = .finite upper
  count : Int
  count_eq : count = Sturm.queryPrepared domain 1

/-- Prepare a finite cell using the shared domain producer. -/
def Cell.prepare? (sign : E → Int) (p : DensePoly E) (lower upper : E) :
    Option (Cell sign p) :=
  match h : Sturm.prepare sign p (.finite lower) (.finite upper) with
  | none => none
  | some domain => some ⟨lower, upper, domain, Sturm.prepare_eq_some _ _ _ _ _ h,
      Sturm.queryPrepared domain 1, rfl⟩

/-- A successful cell retains the supplied finite endpoints literally. -/
theorem Cell.prepare?_endpoints {sign : E → Int} {p : DensePoly E} {lower upper : E}
    {cell : Cell sign p} (accepted : Cell.prepare? sign p lower upper = some cell) :
    cell.lower = lower ∧ cell.upper = upper := by
  unfold Cell.prepare? at accepted
  split at accepted
  · cases accepted
  · cases Option.some.inj accepted
    exact ⟨rfl, rfl⟩

/-- Cell construction has exactly the domain of the shared preparation. -/
theorem Cell.prepare?_isSome (sign : E → Int) (p : DensePoly E) (lower upper : E) :
    (Cell.prepare? sign p lower upper).isSome =
      (Sturm.prepare sign p (.finite lower) (.finite upper)).isSome := by
  unfold Cell.prepare?
  split <;> simp_all

/-- Bisect the actual stored domain, reusing its unchanged derivative chain. -/
def Cell.bisect? {sign : E → Int} {p : DensePoly E} (cell : Cell sign p) :
    Option (Split sign p (.finite cell.lower) (.finite cell.upper)
      (midpoint cell.lower cell.upper)) := by
  let output := splitPrepared? cell.domain (midpoint cell.lower cell.upper)
  simpa only [cell.bound.1, cell.bound.2.1, cell.bound.2.2.1, cell.bound.2.2.2] using output

/-- Stored-domain bisection returns exactly the fresh split, including its data. -/
@[simp] theorem Cell.bisect_eq {sign : E → Int} {p : DensePoly E} (cell : Cell sign p) :
    cell.bisect? = Bisection.bisect? sign p cell.lower cell.upper := by
  unfold Cell.bisect?
  rw [splitPrepared?_eq]
  rcases cell with ⟨lower, upper, domain, bound, count, count_eq⟩
  rcases bound with ⟨hs, hp, hl, hu⟩
  cases domain
  cases hs
  cases hp
  cases hl
  cases hu
  rfl

/-- Replace the head by preparing the same endpoints again. In particular,
no count or endpoint certificate for an old head is retained after deflation. -/
@[expose] def Cell.reprepare? {sign : E → Int} {p : DensePoly E}
    (cell : Cell sign p) (head : DensePoly E) : Option (Cell sign head) :=
  Cell.prepare? sign head cell.lower cell.upper

/-- Rebind a collection only when the classified cut changes its head. -/
@[expose] def Mode.reprepare? {sign : E → Int} {p : DensePoly E} {point : E}
    (mode : Mode sign p point) (cells : List (Cell sign p)) :
    Option (List (Cell sign mode.head)) :=
  match mode with
  | .regular _ => some cells
  | .root d => cells.mapM fun cell => cell.reprepare? d.quotient

/-- Recomputing pending domains changes no interval coordinates. -/
theorem Cell.reprepare?_endpoints {sign : E → Int} {p head : DensePoly E}
    (cells : List (Cell sign p)) {pending : List (Cell sign head)}
    (accepted : cells.mapM (fun cell => cell.reprepare? head) = some pending) :
    pending.map (fun cell => (cell.lower, cell.upper)) =
      cells.map (fun cell => (cell.lower, cell.upper)) := by
  induction cells generalizing pending with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at accepted
    subst pending
    rfl
  | cons cell cells ih =>
    simp only [List.mapM_cons] at accepted
    cases hc : cell.reprepare? head with
    | none => simp [hc] at accepted
    | some output =>
      cases hr : cells.mapM (fun cell => cell.reprepare? head) with
      | none => simp [hc, hr] at accepted
      | some rest =>
        simp [hc, hr] at accepted
        subst pending
        have ends := Cell.prepare?_endpoints hc
        simp only [List.map_cons, ends.1, ends.2, ih hr]

/-- Both cut modes retain all pending interval coordinates. -/
theorem Mode.reprepare?_endpoints {sign : E → Int} {p : DensePoly E} {point : E}
    (mode : Mode sign p point) (cells : List (Cell sign p))
    {pending : List (Cell sign mode.head)} (accepted : mode.reprepare? cells = some pending) :
    pending.map (fun cell => (cell.lower, cell.upper)) =
      cells.map (fun cell => (cell.lower, cell.upper)) := by
  cases mode with
  | regular _ =>
    have he : cells = pending := Option.some.inj accepted
    rw [← he]
    rfl
  | root d => exact Cell.reprepare?_endpoints cells accepted

/-- Choose the first cell containing multiple roots. Other cells retain their
order; count-one cells remain available for descriptor construction. New
halves precede pending cells, so refinement follows a depth-first policy. -/
@[expose] def select {sign : E → Int} {p : DensePoly E} :
    List (Cell sign p) → Option (Cell sign p × List (Cell sign p))
  | [] => none
  | cell :: cells =>
    if cell.count > 1 then some (cell, cells)
    else (select cells).map fun (selected, rest) => (selected, cell :: rest)

/-- Exhaustion means every retained cell has at most one root according to
its actual shared prepared query. -/
theorem select_none {sign : E → Int} {p : DensePoly E} (cells : List (Cell sign p)) :
    select cells = none ↔ ∀ cell ∈ cells, cell.count ≤ 1 := by
  induction cells with
  | nil => simp [select]
  | cons cell cells ih =>
    simp only [select]
    split
    · rename_i h
      simp only [Option.some_ne_none, false_iff]
      intro all
      have hc := all cell (by simp)
      omega
    · rename_i h
      cases hc : select cells with
      | none =>
        simp only [Option.map_none, true_iff]
        have ht := ih.mp hc
        intro c hm
        rcases List.mem_cons.mp hm with rfl | hm
        · omega
        · exact ht c hm
      | some result =>
        rcases result with ⟨selected, rest⟩
        simp only [Option.map_some, Option.some_ne_none, false_iff]
        intro all
        have ht := ih.mpr (fun c hm => all c (by simp [hm]))
        simp [hc] at ht

/-- Selecting a cell neither drops nor duplicates the other intervals. -/
theorem select_perm {sign : E → Int} {p : DensePoly E}
    {cells : List (Cell sign p)} {selected : Cell sign p} {rest : List (Cell sign p)}
    (chosen : select cells = some (selected, rest)) : cells.Perm (selected :: rest) := by
  induction cells generalizing selected rest with
  | nil => simp [select] at chosen
  | cons cell cells ih =>
    simp only [select] at chosen
    split at chosen
    · cases Option.some.inj chosen
      exact List.Perm.refl _
    · cases hc : select cells with
      | none => simp [hc] at chosen
      | some result =>
        rcases result with ⟨next, remaining⟩
        simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at chosen
        rcases chosen with ⟨rfl, rfl⟩
        exact (List.Perm.cons cell (ih hc)).trans (List.Perm.swap _ _ _)

/-- The selection policy never spends a node on a count-zero or count-one cell. -/
theorem select_count {sign : E → Int} {p : DensePoly E}
    {cells : List (Cell sign p)} {selected : Cell sign p} {rest : List (Cell sign p)}
    (chosen : select cells = some (selected, rest)) : selected.count > 1 := by
  induction cells generalizing selected rest with
  | nil => simp [select] at chosen
  | cons cell cells ih =>
    simp only [select] at chosen
    split at chosen
    · rename_i hc
      cases Option.some.inj chosen
      exact hc
    · cases hc : select cells with
      | none => simp [hc] at chosen
      | some result =>
        rcases result with ⟨next, remaining⟩
        simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at chosen
        rcases chosen with ⟨rfl, rfl⟩
        exact ih hc

/-- A frontier owns one current head and cells bound to that head. Removed
coefficient roots are separate from the remaining open intervals. -/
structure Frontier (sign : E → Int) where
  private mk ::
  head : DensePoly E
  cells : List (Cell sign head)
  removed : List E
  nodes : Nat
  nonempty : cells ≠ []

/-- The initial finite frontier has no emitted roots and has used no nodes. -/
def Frontier.prepare? (sign : E → Int) (p : DensePoly E) (lower upper : E) :
    Option (Frontier sign) := do
  let cell ← Cell.prepare? sign p lower upper
  return ⟨p, [cell], [], 0, by simp⟩

/-- Frontier preparation has exactly the domain of its initial cell. -/
theorem Frontier.prepare?_isSome (sign : E → Int) (p : DensePoly E) (lower upper : E) :
    (Frontier.prepare? sign p lower upper).isSome =
      (Cell.prepare? sign p lower upper).isSome := by
  cases h : Cell.prepare? sign p lower upper <;> simp [Frontier.prepare?, h]

/-- Initial construction retains exactly the supplied head and interval. -/
theorem Frontier.prepare?_result {sign : E → Int} {p : DensePoly E} {lower upper : E}
    {frontier : Frontier sign} (accepted : Frontier.prepare? sign p lower upper = some frontier) :
    frontier.head = p ∧ frontier.removed = [] ∧ frontier.nodes = 0 ∧
      frontier.cells.map (fun cell => (cell.lower, cell.upper)) = [(lower, upper)] := by
  cases hc : Cell.prepare? sign p lower upper with
  | none => simp [Frontier.prepare?, hc] at accepted
  | some cell =>
    simp [Frontier.prepare?, hc] at accepted
    cases accepted
    have ends := Cell.prepare?_endpoints hc
    exact ⟨rfl, rfl, rfl, by simp [ends.1, ends.2]⟩

/-- Perform one selected bisection. A root cut re-prepares every pending cell
against the quotient, including the cells whose previous count was one.
Failure remains explicit if any shared preparation rejects the new head. -/
def Frontier.advance? {sign : E → Int} (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (_chosen : select frontier.cells = some (selected, rest)) :
    Option (Frontier sign) := do
  let split ← selected.bisect?
  let point := midpoint selected.lower selected.upper
  let left : Cell sign split.mode.head :=
    ⟨selected.lower, point, split.left, split.left_bound, Sturm.queryPrepared split.left 1, rfl⟩
  let right : Cell sign split.mode.head :=
    ⟨point, selected.upper, split.right, split.right_bound, Sturm.queryPrepared split.right 1, rfl⟩
  let pending ← split.mode.reprepare? rest
  return ⟨split.mode.head, left :: right :: pending,
    frontier.removed ++ split.mode.removed.toList, frontier.nodes + 1, by simp⟩

/-- Advancement succeeds exactly when the actual split and pending-domain
recomputation both succeed. -/
theorem Frontier.advance?_isSome {sign : E → Int} (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) :
    (frontier.advance? selected rest chosen).isSome = true ↔
      ∃ split, bisect? sign frontier.head selected.lower selected.upper = some split ∧
        (split.mode.reprepare? rest).isSome = true := by
  cases hs : bisect? sign frontier.head selected.lower selected.upper with
  | none => simp [Frontier.advance?, hs]
  | some split =>
    cases hp : split.mode.reprepare? rest with
    | none => simp [Frontier.advance?, hs, hp]
    | some pending => simp [Frontier.advance?, hs, hp]

/-- Every successful advancement spends exactly one node. -/
theorem Frontier.advance?_nodes {sign : E → Int} (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) {next : Frontier sign}
    (accepted : frontier.advance? selected rest chosen = some next) :
    next.nodes = frontier.nodes + 1 := by
  cases hs : bisect? sign frontier.head selected.lower selected.upper with
  | none => simp [Frontier.advance?, hs] at accepted
  | some split =>
    cases hp : split.mode.reprepare? rest with
    | none => simp [Frontier.advance?, hs, hp] at accepted
    | some pending =>
      simp [Frontier.advance?, hs, hp] at accepted
      cases accepted
      rfl

/-- The returned frontier records the actual split, recomputed pending cells,
and emitted point. Its interval coordinates are bound to those actual cells. -/
theorem Frontier.advance?_result {sign : E → Int} (frontier : Frontier sign)
    (selected : Cell sign frontier.head) (rest : List (Cell sign frontier.head))
    (chosen : select frontier.cells = some (selected, rest)) {next : Frontier sign}
    (accepted : frontier.advance? selected rest chosen = some next) :
    ∃ split, bisect? sign frontier.head selected.lower selected.upper = some split ∧
      ∃ pending, split.mode.reprepare? rest = some pending ∧
        next.head = split.mode.head ∧
        next.removed = frontier.removed ++ split.mode.removed.toList ∧
        next.cells.map (fun cell => (cell.lower, cell.upper)) =
          [(selected.lower, midpoint selected.lower selected.upper),
            (midpoint selected.lower selected.upper, selected.upper)] ++
              pending.map (fun cell => (cell.lower, cell.upper)) := by
  cases hs : bisect? sign frontier.head selected.lower selected.upper with
  | none => simp [Frontier.advance?, hs] at accepted
  | some split =>
    cases hp : split.mode.reprepare? rest with
    | none => simp [Frontier.advance?, hs, hp] at accepted
    | some pending =>
      simp [Frontier.advance?, hs, hp] at accepted
      cases accepted
      exact ⟨split, rfl, pending, hp, rfl, rfl, rfl⟩

/-- Internally bounded traversal. Each recursive call spends exactly one
bisection node; exhaustion preserves all remaining cells for BKR completion. -/
@[expose] def traverse? {sign : E → Int} : Nat → Frontier sign → Option (Frontier sign)
  | 0, frontier => some frontier
  | budget + 1, frontier =>
    match chosen : select frontier.cells with
    | none => some frontier
    | some (selected, rest) => do
      let next ← frontier.advance? selected rest chosen
      traverse? budget next

/-- A successful traversal cannot exceed its internal node allowance. -/
theorem traverse?_nodes {sign : E → Int} (budget : Nat) (frontier : Frontier sign)
    {result : Frontier sign} (accepted : traverse? budget frontier = some result) :
    result.nodes ≤ frontier.nodes + budget := by
  induction budget generalizing frontier with
  | zero =>
    simp only [traverse?, Option.some.injEq] at accepted
    subst result
    omega
  | succ budget ih =>
    simp only [traverse?] at accepted
    split at accepted
    · simp only [Option.some.injEq] at accepted
      subst result
      omega
    · rename_i cell rest hc
      cases hn : frontier.advance? cell rest hc with
      | none => simp [hn] at accepted
      | some next =>
        simp [hn] at accepted
        have bound := ih next accepted
        have spent := frontier.advance?_nodes cell rest hc hn
        omega

/-- Traversal stops only when selection is exhausted or its node budget is spent. -/
theorem traverse?_stopped {sign : E → Int} (budget : Nat) (frontier : Frontier sign)
    {result : Frontier sign} (accepted : traverse? budget frontier = some result) :
    select result.cells = none ∨ result.nodes = frontier.nodes + budget := by
  induction budget generalizing frontier with
  | zero =>
    simp only [traverse?, Option.some.injEq] at accepted
    subst result
    exact Or.inr (by omega)
  | succ budget ih =>
    simp only [traverse?] at accepted
    split at accepted
    · rename_i hc
      simp only [Option.some.injEq] at accepted
      subst result
      exact Or.inl hc
    · rename_i cell rest hc
      cases hnext : frontier.advance? cell rest hc with
      | none => simp [hnext] at accepted
      | some next =>
        simp [hnext] at accepted
        rcases ih next accepted with done | spent
        · exact Or.inl done
        · have nodes := frontier.advance?_nodes cell rest hc hnext
          exact Or.inr (by omega)

/-- The finite policy is fixed by the input degree, not a requested accuracy.
Call this once after `prepare?`; each call grants a new allowance based on
the supplied current head. The node bound is for one prepare-then-refine run.
This returns a frontier for completion, never a purported partial root set. -/
@[expose] def Frontier.refine? {sign : E → Int} (frontier : Frontier sign) :
    Option (Frontier sign) :=
  traverse? (2 * (frontier.head.natDegree + 1)) frontier

end Hex.RealClosure.Bisection

/-- info: 'Hex.RealClosure.Bisection.select_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.select_none
/-- info: 'Hex.RealClosure.Bisection.select_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.select_perm
/-- info: 'Hex.RealClosure.Bisection.traverse?_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_nodes

/-- info: 'Hex.RealClosure.Bisection.select_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.select_count
/-- info: 'Hex.RealClosure.Bisection.traverse?_stopped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.traverse?_stopped

/-- info: 'Hex.RealClosure.Bisection.Cell.bisect_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.Cell.bisect_eq
