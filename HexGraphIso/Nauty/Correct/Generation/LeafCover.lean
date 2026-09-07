/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Coverage
public import HexGraphIso.Nauty.Correct.Generation.VisitCover

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- The reference occurrence sought in one frozen child of a sweep. -/
@[expose] def ChildLeaf (ctx : Ctx n) (tcLevel level : Nat) (st : RefineSt n)
    (tc : Nat) (targets : List Nat) (key : Key n) (o : Nat) : Prop :=
  HasLeaf ctx tcLevel (level + 1) (childSt ctx level st tc st.lab[tc + o]!) targets key

/-- Coverage for an off-path sweep under the hypothesis that no visited
child produced the sought reference. Pruning may use any checked cell
stabilizer; membership in the final generated subgroup is not required. -/
abbrev LeafCover (ctx : Ctx n) (tcLevel level : Nat) (st : RefineSt n)
    (tc len : Nat) (targets : List Nat) (key : Key n) (tcell : VSet n)
    (cursor : Option Nat) : Prop :=
  VisitCover (ChildLeaf ctx tcLevel level st tc targets key) st.lab tc len tcell cursor

namespace LeafCover

variable {ctx : Ctx n} {tcLevel level tc len : Nat} {st : RefineSt n}
    {targets : List Nat} {key : Key n} {tcell tcell' : VSet n} {cursor : Option Nat}

/-- Initially every occurrence is in the live target window. -/
theorem start (hlab : ∀ o, o < len → st.lab[tc + o]! < n) :
    LeafCover ctx tcLevel level st tc len targets key (windowSet n st.lab tc len) none := by
  exact VisitCover.start hlab

/-- A child proved to have no matching occurrence advances the sweep. -/
theorem advance (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {tv : Nat} (hnext : tcell.nextElem cursor = some tv)
    (hcur : ∀ o, o < len → st.lab[tc + o]! = tv →
      ¬ ChildLeaf ctx tcLevel level st tc targets key o) :
    LeafCover ctx tcLevel level st tc len targets key tcell (some tv) := by
  exact VisitCover.advance h hnext hcur

/-- A descending filter preserves absence coverage through arbitrarily
many earlier filters. Equality here is equality of occurrence propositions,
so it retains the target hints as well as the complete leaf key. -/
theorem filterDesc (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    (hstep : ∀ o, ChildLive st.lab tc len tcell cursor o →
      tcell'.mem st.lab[tc + o]! = true ∨ ∃ j, j < len ∧
        ChildLeaf ctx tcLevel level st tc targets key o =
          ChildLeaf ctx tcLevel level st tc targets key j ∧ st.lab[tc + j]! < st.lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    LeafCover ctx tcLevel level st tc len targets key tcell' cursor := by
  exact VisitCover.filterDesc h hstep hsub

/-- A checked cell stabilizer transports the entire reference occurrence
through a pruning step. It need not belong to the emitted generator list. -/
theorem filterAutom (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    (hdrop : ∀ o, ChildLive st.lab tc len tcell cursor o →
      tcell'.mem st.lab[tc + o]! = false → ∃ γ, checkAutom ctx.g γ = true ∧
        CellStab st.ptn level st.lab γ ∧ γ[st.lab[tc + o]!]! < st.lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    LeafCover ctx tcLevel level st tc len targets key tcell' cursor := by
  apply VisitCover.filterAutom h hok hcell hne hlen ?_ hdrop hsub
  intro γ o j hc hs ho hj hmap
  exact HasLeaf.carried_iff hok hlvl hgsz hc hs hcell hne (by omega) (by omega) hmap

/-- The off-path long-prune ledger preserves every sought reference. -/
theorem longprune (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    {fixedpts : VSet n} {autos : Array (VSet n × VSet n)}
    (haut : ∀ p ∈ autos.toList, fixedpts.subset p.1 = true →
      PairOk ctx.g st.ptn st.lab level p.1 p.2) :
    LeafCover ctx tcLevel level st tc len targets key
      (Nauty.longprune tcell fixedpts autos) cursor := by
  apply VisitCover.longprune h hok hcell hne hlen ?_ haut
  intro γ o j hc hs ho hj hmap
  exact HasLeaf.carried_iff hok hlvl hgsz hc hs hcell hne (by omega) (by omega) hmap

/-- The off-path short-prune ledger preserves every sought reference,
including when the last pair is implicit. -/
theorem shortprune (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc) {out : SearchSt n}
    (hlast : ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g st.ptn st.lab level fix mcr) :
    LeafCover ctx tcLevel level st tc len targets key (Nauty.shortprune tcell out) cursor := by
  apply VisitCover.shortprune h hok hcell hne hlen ?_ hlast
  intro γ o j hc hs ho hj hmap
  exact HasLeaf.carried_iff hok hlvl hgsz hc hs hcell hne (by omega) (by omega) hmap

/-- Exhausting a sweep with no matching visited child rules out every
matching child of the original target window. -/
theorem finish (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    (hnext : tcell.nextElem cursor = none) :
    ∀ o, o < len → ¬ ChildLeaf ctx tcLevel level st tc targets key o :=
  h.cover.finish (fun o ho => no_child_after hnext st.lab[tc + o]! ho.2.1 ho.2.2)

end LeafCover

end Hex.GraphIso.Nauty.Generation
