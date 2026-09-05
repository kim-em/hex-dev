/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Domination
public import HexGraphIso.Nauty.CertStore
import all HexGraphIso.Nauty.Search

public section

/-!
The quartet's return type (SPEC § Verified search refinement).

This file states, and does not yet prove, what one call of each of
`firstPathNode`, `firstChildLoop`, `otherNode` and `otherChildLoop`
establishes. It exists to fix the shape of the mutual induction's
conclusion before the induction is written, and in particular to
record how a generator return carries its justification.

The design point. A node that returns below `level - 1` abandoned
part of its subtree, so it cannot claim the full absorption equation.
The leaf and the abandoned suffix are discharged separately.  At a
code-one leaf, the sentinel immediately above the current path proves
that its codes equal the first path's codes, and the checked carrier
proves that their rows agree; `auto_keyMax` therefore absorbs the leaf
itself without a path-geometry invariant.  The remaining abandonment is
absorbed *wholesale at the greatest common ancestor*: `processnode`
returns `gcaFirst`, and the recorded generator carries the first path's
child of that ancestor onto the current one, so `childKey_of_carried`
equates the two child subtree keys and the abandoned one is dominated by
a sibling the search already explored.

The carrier fact is direct. `processnode` builds its generator as
`workperm[firstlab[i]] := lab[i]`, so `γ` maps `firstlab` to `lab`
pointwise by construction; the ancestor's target position is frozen
from that level down, so the two entries at that position are exactly
the two individualized vertices. Store validity is local as well: code
one validates its scatter with `isautom` before admission.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The subtree key of a node, under its path codes. -/
@[expose] def nodeKey (ctx : Ctx n) (tcLevel fuel level : Nat)
    (cs : List Nat) (st : SearchSt n) (numcells : Nat) : Key n :=
  prefixKey cs
    (specNode ctx tcLevel fuel level st.lab st.ptn st.active numcells)

/-! # The incumbent, read off the state

The incumbent has to be an `Option`, because before the first leaf is
installed there is no incumbent and the state's degenerate contents do
not stand in for one. That is not a stylistic choice: at the root
`canonlevel` is `0`, so the code list is empty and `incKey` would read
`⟨[codeSentinel], _⟩`. Every real refinement code is strictly below
`codeSentinel` (`refine_longcode_lt`), so `listCmp` compares
`codeSentinel` against a real first code and answers `.gt`. The
degenerate reading therefore *outranks every reachable leaf key*, and
`keyMax` keeps it. An absorption equation stated with it would assert
that the final incumbent is the degenerate one, which is false as soon
as the search installs anything.

`SearchModel` already carries the fix: `incMax : Option (Key n) → Key n →
Key n` with `none` as the bottom, which is what `searchNode_eq` folds
with.  The semantic induction threads that option explicitly.  It can
be read back from the imperative state only outside the temporary
upward-comparison window, where `canoncode` contains path codes rather
than the installed incumbent's codes. -/

/-- The incumbent's code list, as `runTraced` reports it. -/
@[expose] def bestCodesOf (st : SearchSt n) : List Nat :=
  (List.range' 1 st.canonlevel).map fun i => st.canoncode[i]!

/-- The incumbent a state carries, or `none` before the first
install. -/
@[expose] def stInc (ctx : Ctx n) (st : SearchSt n) : Option (Key n) :=
  if st.canonlevel = 0 then none
  else some ⟨bestCodesOf st ++ [codeSentinel], leafRows ctx st.canonlab⟩

/-- The semantic incumbent represented by the comparison machine's ghost
code list. -/
@[expose] def ghostInc (ctx : Ctx n) (bs : List Nat)
    (canonlab : Array Nat) : Option (Key n) :=
  if bs = [] then none else some (incKey ctx bs canonlab)

/-- Outside the upward overwrite window, `canoncode` contains exactly the
ghost incumbent codes. -/
theorem bestCodesOf_eq {nn : Nat} {cs bs : List Nat} {st : SearchSt n}
    {compCanon : Int}
    (hinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon compCanon)
    (hne : compCanon ≠ 1) :
    bestCodesOf st = bs := by
  unfold bestCodesOf
  refine List.ext_getElem (by simp [hinv.blen]) fun i hi hb => ?_
  rw [List.getElem_map]
  have hcontent := hinv.content (i + 1) (by omega) (by omega)
    (fun h => (hne h).elim)
  have hir : i < (List.range' 1 st.canonlevel).length := by
    simpa using hi
  rw [List.getElem_range' hir]
  have hbcode : bcode bs (i + 1) = bs[i]! :=
    bcode_of_le (by omega) (by omega)
  rw [hbcode, getElem!_pos bs i hb] at hcontent
  simpa [Nat.add_comm] using hcontent

/-- At a stable comparison state, reading the mutable incumbent agrees
with the semantic ghost incumbent. -/
theorem stInc_eq_ghost {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {st : SearchSt n} {compCanon : Int}
    (hinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon compCanon)
    (hne : compCanon ≠ 1) :
    stInc ctx st = ghostInc ctx bs st.canonlab := by
  rw [stInc, ghostInc, bestCodesOf_eq hinv hne, hinv.blen]
  cases bs <;> simp [incKey]

/-- The payload a generator return carries to its target level.

`γ` is the generator `processnode` recorded, it is a checked
automorphism, and it maps the first path's labelling onto the
current one pointwise. The last clause is the whole content: at any
position frozen at or above the return level, the two labellings hold
the two paths' individualized vertices, so `γ` carries one child of
the return level's node onto another. -/
@[expose] def CarrierOut (ctx : Ctx n) (out : SearchSt n) : Prop :=
  ∃ γ ∈ out.genTrace,
    checkAutom ctx.g γ = true ∧
      ∀ i, i < n → γ[out.firstlab[i]!]! = out.lab[i]!

/-- What one node call establishes.

`full` is the absorption equation, available exactly when the node ran
to completion, and `carried` is the generator payload, available
exactly when it did not. The two are stated as implications on the
returned level rather than as a disjunction so that a caller which
knows which case it is in can use the corresponding clause without a
case split. `installed` records that a completed node leaves an
incumbent, which is what makes the `full` equation's left side a
`some`. -/
structure NodeConcl (ctx : Ctx n) (tcLevel fuel level : Nat)
    (cs : List Nat) (st out : SearchSt n) (numcells : Nat)
    (r : Int) : Prop where
  /-- Something is installed on the way out of a completed node. -/
  installed : r = Int.ofNat level - 1 → out.canonlevel ≠ 0
  /-- Ran to completion: the whole subtree is absorbed. -/
  full : r = Int.ofNat level - 1 →
    stInc ctx out =
      some (incMax (stInc ctx st)
        (nodeKey ctx tcLevel fuel level cs st numcells))
  /-- Returned early: the return goes to the recorded ancestor and
  carries a generator that identifies this subtree with a sibling the
  search already explored. -/
  carried : r < Int.ofNat level - 1 →
    r = Int.ofNat out.gcaFirst ∧ CarrierOut ctx out

/-- What one child-loop call establishes.

The loop folds the children from `tv1` onward into the incumbent.
`explored` names the offsets it got through; on a `none` return that
is all of them, and on a `some` return the loop stopped early and the
payload travels on. -/
structure LoopConcl (ctx : Ctx n) (tcLevel fuel level : Nat)
    (cs : List Nat) (st out : SearchSt n)
    (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (explored : List Nat) (r : Option Int) : Prop where
  /-- Completed with a nonempty sweep: something is installed. -/
  installed : r = none → explored ≠ [] → out.canonlevel ≠ 0
  /-- Completed: the incumbent absorbed exactly the children the loop
  visited, under the node's own code prefix. -/
  full : r = none →
    stInc ctx out =
      (explored.map fun o =>
          prefixKey cs
            (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o)).foldl
        (fun acc kk => some (incMax acc kk)) (stInc ctx st)
  /-- Stopped early: the payload identifies the remainder. -/
  carried : ∀ rr, r = some rr → rr < Int.ofNat level →
    rr = Int.ofNat out.gcaFirst ∧ CarrierOut ctx out

/-! # The carrier fact is free

The payload's third clause is not an assumption about the search's
history: it follows from how `processnode` builds its generator. This
is the feasibility check for the whole architecture, so it is proved
here rather than asserted.

`StoreValid` already has this fact as a private lemma
(`foldl_scatter_getElem`) and already consumes exactly this shape in
`scatter_isPerm`'s `hsc` hypothesis. At integration the private
lemma should be exposed and these two re-proofs deleted, rather than
kept in parallel. -/

private theorem foldl_size {lab₁ lab₂ : Array Nat} :
    ∀ (l : List Nat) (base : Array Nat),
      (l.foldl (fun r i => r.set! lab₁[i]! lab₂[i]!) base).size
        = base.size
  | [], _ => rfl
  | _ :: l, base => by
    rw [List.foldl_cons, foldl_size l, Array.size_set!]

private theorem foldl_get {lab₁ lab₂ : Array Nat} {nn : Nat}
    (hinj : ∀ a b, a < nn → b < nn → lab₁[a]! = lab₁[b]! → a = b)
    {base : Array Nat}
    (hbb : ∀ i, i < nn → lab₁[i]! < base.size) :
    ∀ {m : Nat}, m ≤ nn → ∀ {j : Nat}, j < m →
      ((List.range m).foldl
        (fun r i => r.set! lab₁[i]! lab₂[i]!) base)[lab₁[j]!]! =
        lab₂[j]! := by
  intro m
  induction m with
  | zero => intro _ j hj; omega
  | succ p ih =>
    intro hm j hj
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rcases Decidable.em (j = p) with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _
        (by rw [foldl_size]; exact hbb j (by omega))]
    · have hlne : lab₁[p]! ≠ lab₁[j]! := fun h =>
        hne (hinj j p (by omega) (by omega) h.symm)
      rw [Array.getElem!_set!_ne _ _ _ _ hlne, ih (by omega) (by omega)]

/-- The generator `processnode` records maps the first-path labelling
onto the current one pointwise, given only that the first-path
labelling is injective and bounded. Nothing about codes, code
lengths, or where the first path went discrete is used. -/
theorem firstScatter_get {flab lab : Array Nat} {nn : Nat}
    (hinj : ∀ a b, a < nn → b < nn → flab[a]! = flab[b]! → a = b)
    (hlt : ∀ i, i < nn → flab[i]! < nn) :
    ∀ {j : Nat}, j < nn →
      (firstScatter nn flab lab)[flab[j]!]! = lab[j]! := by
  intro j hj
  rw [firstScatter]
  exact foldl_get hinj (base := Array.replicate nn 0)
    (fun i hi => by rw [Array.size_replicate]; exact hlt i hi)
    (Nat.le_refl nn) hj

/-- The gca step, which is where a payload is discharged.

At the ancestor the payload's generator carries the abandoned child
onto an already-explored one, so `childKey_of_carried` equates their
keys and the abandoned child contributes nothing new. This is stated
as the shape the loop needs, not proved here. -/
@[expose] def PayloadAbsorbs (ctx : Ctx n) (tcLevel fuel level : Nat)
    (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (oFirst oCur : Nat) (out : SearchSt n) : Prop :=
  CarrierOut ctx out →
    childKey ctx tcLevel fuel level rsLab rsPtn tc numcells oCur =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells oFirst

/-- The payload discharges, given the two position facts.

The carrier clause holds at every position, so it holds at the
ancestor's target position `tc`; the two hypotheses say what the two
labellings hold there, namely the two paths' individualized vertices.
`childKey_of_carried` then equates the two children's subtree keys.

The position facts are the induction's to supply: they are the
descent's own bookkeeping, not a property of this node. Everything
else here is the node's well-formedness. -/
theorem payloadAbsorbs_of_positions {ctx : Ctx n}
    (hgsz : ctx.g.size = n) (tcLevel fuel level : Nat)
    {rsLab rsPtn : Array Nat} {tc lenT numcells oFirst oCur : Nat}
    {out : SearchSt n}
    (hstab : ∀ γ, checkAutom ctx.g γ = true →
      (∀ i, i < n → γ[out.firstlab[i]!]! = out.lab[i]!) →
      CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (hoC : oCur < lenT) (hoF : oFirst < lenT)
    (hlf : level + 1 + fuel ≤ n + 1) (htc : tc < n)
    (hfirst : out.firstlab[tc]! = rsLab[tc + oFirst]!)
    (hcur : out.lab[tc]! = rsLab[tc + oCur]!) :
    PayloadAbsorbs ctx tcLevel fuel level rsLab rsPtn tc numcells
      oFirst oCur out := by
  rintro ⟨γ, _, hAut, hmap⟩
  refine childKey_of_carried hn hgsz hAut tcLevel fuel level
    (hstab γ hAut hmap) hs hok hsp hend hvals hic hrange hoC hoF hlf ?_
  have h := hmap tc htc
  rwa [hfirst, hcur] at h

/-! # The position facts: the step

`payloadAbsorbs_of_positions` takes the two position facts as
hypotheses because they are the descent's bookkeeping. Their base case
is local and is proved here: individualizing offset `o` puts that
offset's vertex at the target position.

The transport of this from the child down to the leaf rests on the
target position being a *singleton cell* from the individualization
onwards. Both steps of that transport are proved below, over one
operation each: `refine` fixes a singleton cell's position, and a
`breakout` elsewhere misses it, because two maximal runs are equal or
disjoint. What is not proved here is the run-level statement that
chains them, since the descent is the mutual recursion itself; see the
note after `breakout_misses_singleton`. -/

/-- Individualizing offset `o` puts that offset's vertex at the target
position. -/
theorem breakout_at_target {lab ptn : Array Nat} {level tc o : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size) :
    (breakout n lab ptn (level + 1) tc lab[tc + o]!).1[tc]! =
      lab[tc + o]! := by
  rw [breakout_lab_at hinj hto tc, ite_eq_right (Nat.lt_irrefl tc),
    ite_eq_left rfl]

/-- Individualizing closes the target position, so it becomes a
singleton cell one level down. This is what makes the transport below
apply from the child onwards. -/
theorem isCell_breakout_target {lab ptn : Array Nat}
    {level tc tv : Nat} (hlt : tc < ptn.size)
    (hstart : tc = 0 ∨ ptn[tc - 1]! ≤ level) :
    IsCell (breakout n lab ptn (level + 1) tc tv).2.1 (level + 1) tc 1 := by
  refine ⟨Nat.one_pos, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos tc with rfl | hpos
    · exact Or.inl rfl
    · refine Or.inr ?_
      show (ptn.set! tc (level + 1))[tc - 1]! ≤ level + 1
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      rcases hstart with rfl | hs
      · omega
      · exact Nat.le_succ_of_le hs
  · intro i h1 h2; omega
  · show (ptn.set! tc (level + 1))[tc]! ≤ level + 1
    rw [Array.getElem!_set!_self _ _ _ hlt]
    exact Nat.le_refl _

/-- `refine` leaves a singleton cell's position exactly where it was:
it permutes cell contents, and a singleton cell has only one. -/
theorem refine_fixes_singleton {ctx : Ctx n} {level : Nat}
    {lab ptn : Array Nat} {active numcells a : Nat}
    (hnn : n ≤ ptn.size) (hs : lab.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) (hc : IsCell ptn level a 1) :
    (refine ctx level lab ptn active numcells).lab[a]! = lab[a]! :=
  (cellsPerm_singleton (refine_refInv hnn hs hend).perm hc).symm

/-- A singleton cell lies outside any other cell, so outside the window
a `breakout` at that other cell rotates. -/
theorem singleton_outside_cell {ptn : Array Nat}
    {level a tc len o : Nat} (hca : IsCell ptn level a 1)
    (hct : IsCell ptn level tc len) (hne : a ≠ tc) (ho : o < len) :
    a < tc ∨ tc + o < a := by
  rcases isCell_disj_or_eq hca hct with ⟨h1, _⟩ | h | h
  · exact absurd h1 hne
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- A `breakout` at a different cell leaves a singleton cell's position
alone. Together with `refine_fixes_singleton` this is the whole content
of the descent's position bookkeeping, one operation at a time. -/
theorem breakout_misses_singleton {lab ptn : Array Nat}
    {level a tc o : Nat} (hinj : LabInj lab lab.size)
    (hto : tc + o < lab.size) (hout : a < tc ∨ tc + o < a) :
    (breakout n lab ptn (level + 1) tc lab[tc + o]!).1[a]! = lab[a]! := by
  rw [breakout_lab_at hinj hto a]
  rcases hout with h | h
  · rw [ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-! What remains for the position facts is a run-level frame: that one
call of a quartet function preserves `lab[q]` at every position that is
a singleton cell on entry. Its proof is an induction over the same
mutual recursion as the absorption equation, discharging `refine` by
`refine_fixes_singleton`, each deeper `breakout` by
`singleton_outside_cell` and `breakout_misses_singleton`, and the
persistence of the singleton itself by `refine_frozen` on both `ptn[q]`
and `ptn[q - 1]`, whose values a deeper `set!` at a different position
does not touch. It is stated as part of that induction rather than
before it because a node's effect on `lab` is only defined through the
recursion. -/

/-! # From the loop's fold to the node's maximum

`LoopConcl.full` is a left fold of `incMax` over the offsets the loop
actually visited, and `specNode_internal` presents the node's key as a
`keysMax` over *all* of them. Two facts bridge the two, and neither
mentions the search: the fold is the maximum, and offsets dominated by
a survivor can be dropped from a maximum.

The second is what the orbit prune and the two sibling filters are
for. `firstChildLoop` skips a child outright when its orbit
representative is not itself (`Search.lean`, the `orbits` test), so the
fold's list is a sublist of the node's children; `childKey_of_orbPruned`
and `longprune_carried`/`shortprune_carried` say each skipped child's
key repeats one that survived, which is exactly the hypothesis of
`keysMax_eq_of_dominated`. -/

/-- A fold of `incMax` from a present incumbent is the seeded
maximum. -/
theorem foldl_incMax_some : ∀ (l : List (Key n)) (k : Key n),
    l.foldl (fun acc kk => some (incMax acc kk)) (some k) =
      some (keysMax k l)
  | [], _ => rfl
  | k' :: rest, k => by
    rw [List.foldl_cons, keysMax]
    exact foldl_incMax_some rest (keyMax k k')

/-- A fold of `incMax` from no incumbent is the maximum seeded by the
first key folded in. -/
theorem foldl_incMax_none (k : Key n) (l : List (Key n)) :
    (k :: l).foldl (fun acc kk => some (incMax acc kk)) none =
      some (keysMax k l) := by
  rw [List.foldl_cons]
  exact foldl_incMax_some l k

/-- Keys dominated by what survives can be dropped from a maximum.

This is the shape the skipped children need: `l` is every child of the
node, `l'` the ones the loop visited, and the hypothesis is that each
child's key is bounded by the maximum over the visited ones, which the
prune dischargers supply by exhibiting a visited child with an equal
key. -/
theorem keysMax_eq_of_dominated {l l' : List (Key n)} {k : Key n}
    (hsub : ∀ x ∈ l', x ∈ l)
    (hdom : ∀ x ∈ l, keyLe x (keysMax k l')) :
    keysMax k l = keysMax k l' :=
  keyLe_antisym
    (keysMax_le (keyLe_keysMax (Or.inl rfl)) hdom)
    (keysMax_le (keyLe_keysMax (Or.inl rfl))
      fun y hy => keyLe_keysMax (Or.inr (hsub y hy)))

/-- The dominated-key hypothesis in the form the prune dischargers
produce it: every child either survived or has the same key as one that
did. -/
theorem keysMax_eq_of_repeats {l l' : List (Key n)} {k : Key n}
    (hsub : ∀ x ∈ l', x ∈ l)
    (hrep : ∀ x ∈ l, x ∈ l' ∨ ∃ y ∈ l', x = y) :
    keysMax k l = keysMax k l' :=
  keysMax_eq_of_dominated hsub fun x hx => by
    rcases hrep x hx with hm | ⟨y, hy, rfl⟩
    · exact keyLe_keysMax (Or.inr hm)
    · exact keyLe_keysMax (Or.inr hy)

/-- The same, with the two maxima seeded independently.

The node and the loop do not share a seed: the node's maximum is seeded
at its first child, and the loop's fold is seeded at whichever child it
visited first. Treating both seeds as ordinary members is what lets the
two be compared. -/
theorem keysMax_eq_of_dominated' {k k' : Key n} {l l' : List (Key n)}
    (hsub : ∀ x, (x = k' ∨ x ∈ l') → (x = k ∨ x ∈ l))
    (hdom : ∀ x, (x = k ∨ x ∈ l) → keyLe x (keysMax k' l')) :
    keysMax k l = keysMax k' l' :=
  keyLe_antisym
    (keysMax_le (hdom k (Or.inl rfl)) fun y hy => hdom y (Or.inr hy))
    (keysMax_le (keyLe_keysMax (hsub k' (Or.inl rfl)))
      fun y hy => keyLe_keysMax (hsub y (Or.inr hy)))

/-- **The node's absorption equation from its loop's fold.**

This is the algebra the node step performs, with the search abstracted
away: the loop folded the children it visited into the incoming
incumbent, and the node claims the incumbent absorbed the maximum over
*all* its children. The two agree exactly when every child is dominated
by the maximum over the visited ones, which is what the prune
dischargers establish for the children the loop skipped.

The incoming incumbent is handled uniformly, which is the point of
carrying it as an `Option`: with nothing installed the fold's first
child seeds the maximum, and with an incumbent present it is one more
competitor. -/
theorem node_absorbs_of_loop {inc : Option (Key n)} {k0 e : Key n}
    {rest es : List (Key n)}
    (hsub : ∀ x, (x = e ∨ x ∈ es) → (x = k0 ∨ x ∈ rest))
    (hdom : ∀ x, (x = k0 ∨ x ∈ rest) → keyLe x (keysMax e es)) :
    (e :: es).foldl (fun acc kk => some (incMax acc kk)) inc =
      some (incMax inc (keysMax k0 rest)) := by
  rw [keysMax_eq_of_dominated' hsub hdom]
  cases inc with
  | none => rw [foldl_incMax_none]; rfl
  | some b =>
    rw [foldl_incMax_some, keysMax]
    exact congrArg some (keysMax_keyMax es b e)

/-! # The root assembly

The corrected statement reaches the programme's target. The root call
of `firstPathNode` starts from a state with `canonlevel = 0`, so its
incoming incumbent is `none` and `incMax` discards it; what comes out
is therefore the node key of the root, which is `canonSpec` by
definition, and the state's own incumbent reading is `tracedKey` by
definition. `certifyCanon?_isSome_of_dominated` then closes.

The quartet's root instance is the hypothesis here, and it is the only
thing these theorems assume: the induction that supplies it is the
remaining work. -/

/-- The root state `runTraced` starts from. -/
@[expose] def rootSt (n : Nat) (lab0 : Array Nat)
    (cellEnds : List Nat) : SearchSt n :=
  { lab := lab0, ptn := initPtn n (n + 2) cellEnds,
    active := initActive n cellEnds,
    orbits := .ofFn (n := n) fun i => i.val,
    firstcode := .replicate (n + 2) 0,
    canoncode := .replicate (n + 2) 0,
    firsttc := .replicate (n + 2) (-1),
    firstlab := .replicate n 0,
    canonlab := .replicate n 0,
    canong := .replicate n 0,
    numorbits := n }

/-- The state the root call returns. -/
@[expose] def rootOut (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : SearchSt n :=
  (firstPathNode { g } (n + 2) 100 (n + 2) 1 cellEnds.length
    (rootSt n lab0 cellEnds)).2

/-- `runTraced`'s reported codes are the returned state's own
reading. -/
theorem bestCodes_runTraced {g lab0 : Array Nat} {cellEnds : List Nat}
    (hn0 : n ≠ 0) :
    (runTraced n g lab0 cellEnds).bestCodes =
      bestCodesOf (rootOut n g lab0 cellEnds) := by
  rw [runTraced]
  simp only [beq_iff_eq, hn0, ite_false]
  rfl

/-- `runTraced`'s reported labelling is the returned state's. -/
theorem canonlab_runTraced {g lab0 : Array Nat} {cellEnds : List Nat}
    (hn0 : n ≠ 0) :
    (runTraced n g lab0 cellEnds).result.canonlab =
      (rootOut n g lab0 cellEnds).canonlab := by
  rw [runTraced]
  simp only [beq_iff_eq, hn0, ite_false]
  rfl

/-- The traced key is the final state's incumbent, once anything has
been installed. -/
theorem stInc_final {G : Colored n k} (hn0 : n ≠ 0)
    (hinst : (rootOut n (rowsOf G) (initialPartition G).1
      (initialPartition G).2).canonlevel ≠ 0) :
    stInc { g := rowsOf G }
        (rootOut n (rowsOf G) (initialPartition G).1
          (initialPartition G).2) =
      some (tracedKey G) := by
  rw [stInc, ite_eq_right hinst, tracedKey, runColoredTraced,
    bestCodes_runTraced hn0, canonlab_runTraced hn0]

/-- The root's node key is the specification's canonical key. -/
theorem nodeKey_root {G : Colored n k} (hn0 : n ≠ 0) :
    nodeKey { g := rowsOf G } 100 n 1 []
        (rootSt n (initialPartition G).1 (initialPartition G).2)
        (initialPartition G).2.length = canonSpecKey G := by
  rw [nodeKey, prefixKey_nil, canonSpecKey, canonSpec]
  simp only [beq_iff_eq, hn0, ite_false]
  rfl

/-- The root's incoming incumbent is the bottom: nothing is installed
before the search starts. -/
theorem stInc_rootSt {G : Colored n k} :
    stInc { g := rowsOf G }
      (rootSt n (initialPartition G).1 (initialPartition G).2) = none :=
  rfl

/-- **The root assembly.** Given the quartet's conclusion at the root
call, the traced key is the specification's key. -/
theorem dominated_of_root {G : Colored n k} (hn0 : n ≠ 0) {r : Int}
    (hroot : NodeConcl { g := rowsOf G } 100 n 1 []
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length r)
    (hr : r = Int.ofNat 1 - 1) :
    canonSpecKey G = tracedKey G := by
  have hfull := hroot.full hr
  have hinst := hroot.installed hr
  rw [stInc_final hn0 hinst, stInc_rootSt, incMax, nodeKey_root hn0] at hfull
  exact (Option.some.inj hfull).symm

/-- **The programme's target**, modulo the quartet at the root. -/
theorem certifyCanon?_isSome_of_root {G : Colored n k} (hn0 : n ≠ 0)
    {r : Int}
    (hroot : NodeConcl { g := rowsOf G } 100 n 1 []
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length r)
    (hr : r = Int.ofNat 1 - 1) :
    (certifyCanon? G).isSome :=
  certifyCanon?_isSome_of_keyEq G (dominated_of_root hn0 hroot hr)

end Hex.GraphIso.Nauty
