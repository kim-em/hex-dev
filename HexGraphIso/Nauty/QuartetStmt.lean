/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Domination

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
Two architectures were available. The first proves, at the code-one
leaf, that the leaf's own key does not improve the incumbent
(`auto_keyMax`), which needs the leaf's path codes to equal the first
path's, hence needs first-path geometry inside the domination
argument. The second absorbs the abandonment *wholesale at the
greatest common ancestor*: `processnode` returns `gcaFirst`, and the
recorded generator carries the first path's child of that ancestor
onto the current one, so `childKey_of_carried` equates the two child
subtree keys and the abandoned one is dominated by a sibling the
search already explored.

The second is what this file states, because the carrier fact it
needs is immediate. `processnode` builds its generator as
`workperm[firstlab[i]] := lab[i]`, so `γ` maps `firstlab` to `lab`
pointwise by construction; the ancestor's target position is frozen
from that level down, so the two entries at that position are exactly
the two individualized vertices. No statement about codes, code
lengths, or where the first path went discrete enters anywhere.

`auto_keyMax` is therefore not applied by the induction under this
architecture, and `cs = fs` is not among the quartet's obligations.
First-path geometry is still required, but only by store validity:
the scan-free admission arm of `processnode_checkAutom` needs
`leafRows firstlab = leafRows lab`, which is the `harm2` obligation
that `FirstDescOk` supplies.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The subtree key of a node, under its path codes. -/
@[expose] def nodeKey (ctx : Ctx) (tcLevel fuel level : Nat)
    (cs : List Nat) (st : SearchSt) (numcells : Nat) : Key :=
  prefixKey cs
    (specNode ctx tcLevel fuel level st.lab st.ptn st.active numcells)

/-- The payload a generator return carries to its target level.

`γ` is the generator `processnode` recorded, it is a checked
automorphism, and it maps the first path's labelling onto the
current one pointwise. The last clause is the whole content: at any
position frozen at or above the return level, the two labellings hold
the two paths' individualized vertices, so `γ` carries one child of
the return level's node onto another. -/
@[expose] def CarrierOut (ctx : Ctx) (out : SearchSt) : Prop :=
  ∃ γ ∈ out.genTrace,
    checkAutom ctx.g γ ctx.n = true ∧
      ∀ i, i < ctx.n → γ[out.firstlab[i]!]! = out.lab[i]!

/-- What one node call establishes.

`mono` and `sound` hold on every return; `full` is the absorption
equation, available exactly when the node ran to completion; and
`carried` is the generator payload, available exactly when it did
not. The two are stated as implications on the returned level rather
than as a disjunction so that a caller which knows which case it is
in can use the corresponding clause without a case split. -/
structure NodeConcl (ctx : Ctx) (tcLevel fuel level : Nat)
    (cs bs bs' : List Nat) (st out : SearchSt) (numcells : Nat)
    (r : Int) : Prop where
  /-- The incumbent never moves down. -/
  mono : keyLe (incKey ctx bs st.canonlab) (incKey ctx bs' out.canonlab)
  /-- The incumbent never exceeds what this subtree and the incoming
  incumbent contain. -/
  sound : keyLe (incKey ctx bs' out.canonlab)
    (keyMax (incKey ctx bs st.canonlab)
      (nodeKey ctx tcLevel fuel level cs st numcells))
  /-- Ran to completion: the whole subtree is absorbed. -/
  full : r = Int.ofNat level - 1 →
    incKey ctx bs' out.canonlab =
      keyMax (incKey ctx bs st.canonlab)
        (nodeKey ctx tcLevel fuel level cs st numcells)
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
structure LoopConcl (ctx : Ctx) (tcLevel fuel level : Nat)
    (cs bs bs' : List Nat) (st out : SearchSt)
    (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (explored : List Nat) (r : Option Int) : Prop where
  mono : keyLe (incKey ctx bs st.canonlab) (incKey ctx bs' out.canonlab)
  /-- Completed: the incumbent absorbed exactly the children the loop
  visited, under the node's own code prefix. -/
  full : r = none →
    incKey ctx bs' out.canonlab =
      keysMax (incKey ctx bs st.canonlab)
        (explored.map fun o =>
          prefixKey cs
            (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o))
  /-- Stopped early: the incumbent absorbed the children visited so
  far, and the payload identifies the remainder. -/
  carried : ∀ rr, r = some rr → rr < Int.ofNat level →
    keyLe (incKey ctx bs' out.canonlab)
        (keysMax (incKey ctx bs st.canonlab)
          (explored.map fun o =>
            prefixKey cs
              (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o)))
      ∧ rr = Int.ofNat out.gcaFirst ∧ CarrierOut ctx out

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
@[expose] def PayloadAbsorbs (ctx : Ctx) (tcLevel fuel level : Nat)
    (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (oFirst oCur : Nat) (out : SearchSt) : Prop :=
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
theorem payloadAbsorbs_of_positions {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) (tcLevel fuel level : Nat)
    {rsLab rsPtn : Array Nat} {tc lenT numcells oFirst oCur : Nat}
    {out : SearchSt}
    (hstab : ∀ γ, checkAutom ctx.g γ ctx.n = true →
      (∀ i, i < ctx.n → γ[out.firstlab[i]!]! = out.lab[i]!) →
      CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (hoC : oCur < lenT) (hoF : oFirst < lenT)
    (hlf : level + 1 + fuel ≤ n + 1) (htc : tc < ctx.n)
    (hfirst : out.firstlab[tc]! = rsLab[tc + oFirst]!)
    (hcur : out.lab[tc]! = rsLab[tc + oCur]!) :
    PayloadAbsorbs ctx tcLevel fuel level rsLab rsPtn tc numcells
      oFirst oCur out := by
  rintro ⟨γ, _, hAut, hmap⟩
  refine childKey_of_carried hn hgsz hAut tcLevel fuel level
    (hstab γ hAut hmap) hs hok hsp hend hvals hic hrange hoC hoF hlf ?_
  have h := hmap tc htc
  rwa [hfirst, hcur] at h

end Hex.GraphIso.Nauty
