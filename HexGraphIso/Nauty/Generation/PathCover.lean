/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.RefPath
public import HexGraphIso.Nauty.Generation.VisitCover

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- The reference occurrence sought in one frozen child of a sweep. -/
@[expose] def ChildPath (ctx : Ctx n) (tcLevel boundary level : Nat) (st : RefineSt n)
    (tc : Nat) (targets : List Nat) (key : Key n) (o : Nat) : Prop :=
  RefPath ctx tcLevel boundary (level + 1) (childSt ctx level st tc st.lab[tc + o]!) targets key

/-- Coverage of references carrying a saved uniformity boundary. The
sweep accounting is shared with ordinary leaf coverage. -/
abbrev PathCover (ctx : Ctx n) (tcLevel boundary level : Nat) (st : RefineSt n)
    (tc len : Nat) (targets : List Nat) (key : Key n) (tcell : VSet n)
    (cursor : Option Nat) : Prop :=
  VisitCover (ChildPath ctx tcLevel boundary level st tc targets key) st.lab tc len tcell cursor

namespace PathCover

variable {ctx : Ctx n} {tcLevel boundary level tc len : Nat} {st : RefineSt n}
    {targets : List Nat} {key : Key n} {tcell tcell' : VSet n} {cursor : Option Nat}

/-- Initially every occurrence is in the live target window. -/
theorem start (hlab : ∀ o, o < len → st.lab[tc + o]! < n) :
    PathCover ctx tcLevel boundary level st tc len targets key (windowSet n st.lab tc len) none := by
  exact VisitCover.start hlab

/-- A child proved to have no matching occurrence advances the sweep. -/
theorem advance (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    {tv : Nat} (hnext : tcell.nextElem cursor = some tv)
    (hcur : ∀ o, o < len → st.lab[tc + o]! = tv →
      ¬ ChildPath ctx tcLevel boundary level st tc targets key o) :
    PathCover ctx tcLevel boundary level st tc len targets key tcell (some tv) := by
  exact VisitCover.advance h hnext hcur

/-- A descending filter preserves absence coverage through arbitrarily
many earlier filters. Equality here is equality of occurrence propositions,
so it retains the target hints as well as the complete leaf key. -/
theorem filterDesc (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    (hstep : ∀ o, ChildLive st.lab tc len tcell cursor o →
      tcell'.mem st.lab[tc + o]! = true ∨ ∃ j, j < len ∧
        ChildPath ctx tcLevel boundary level st tc targets key o =
          ChildPath ctx tcLevel boundary level st tc targets key j ∧ st.lab[tc + j]! < st.lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    PathCover ctx tcLevel boundary level st tc len targets key tcell' cursor := by
  exact VisitCover.filterDesc h hstep hsub

/-- A checked cell stabilizer transports the entire reference occurrence
through a pruning step. It need not belong to the emitted generator list. -/
theorem filterAutom (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    (hdrop : ∀ o, ChildLive st.lab tc len tcell cursor o →
      tcell'.mem st.lab[tc + o]! = false → ∃ γ, checkAutom ctx.g γ = true ∧
        CellStab st.ptn level st.lab γ ∧ γ[st.lab[tc + o]!]! < st.lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    PathCover ctx tcLevel boundary level st tc len targets key tcell' cursor := by
  apply VisitCover.filterAutom h hok hcell hne hlen ?_ hdrop hsub
  intro γ o j hc hs ho hj hmap
  exact RefPath.carried_iff hok hlvl hgsz hc hs hcell hne (by omega) (by omega) hmap

/-- The off-path long-prune ledger preserves every sought reference. -/
theorem longprune (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    {fixedpts : VSet n} {autos : Array (VSet n × VSet n)}
    (haut : ∀ p ∈ autos.toList, fixedpts.subset p.1 = true →
      PairOk ctx.g st.ptn st.lab level p.1 p.2) :
    PathCover ctx tcLevel boundary level st tc len targets key
      (Nauty.longprune tcell fixedpts autos) cursor := by
  apply VisitCover.longprune h hok hcell hne hlen ?_ haut
  intro γ o j hc hs ho hj hmap
  exact RefPath.carried_iff hok hlvl hgsz hc hs hcell hne (by omega) (by omega) hmap

/-- The off-path short-prune ledger preserves every sought reference,
including when the last pair is implicit. -/
theorem shortprune (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc) {out : SearchSt n}
    (hlast : ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g st.ptn st.lab level fix mcr) :
    PathCover ctx tcLevel boundary level st tc len targets key (Nauty.shortprune tcell out) cursor := by
  apply VisitCover.shortprune h hok hcell hne hlen ?_ hlast
  intro γ o j hc hs ho hj hmap
  exact RefPath.carried_iff hok hlvl hgsz hc hs hcell hne (by omega) (by omega) hmap

/-- Exhausting a sweep with no matching visited child rules out every
matching child of the original target window. -/
theorem finish (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    (hnext : tcell.nextElem cursor = none) :
    ∀ o, o < len → ¬ ChildPath ctx tcLevel boundary level st tc targets key o :=
  h.cover.finish (fun o ho => no_child_after hnext st.lab[tc + o]! ho.2.1 ho.2.2)

/-- An earlier original child has no matching occurrence, even if an
older pruning filter removed it from the current target set. -/
theorem smaller (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    {tv o : Nat} (hnext : tcell.nextElem cursor = some tv)
    (ho : o < len) (hlt : st.lab[tc + o]! < tv) :
    ¬ ChildPath ctx tcLevel boundary level st tc targets key o := by
  exact VisitCover.smaller h hnext ho hlt

/-- A recorded carrier transfers absence from its reference child to the
current child. This consumes canonical returns without claiming that the
interrupted child was exhaustively searched. -/
theorem carrier (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    {tv e oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : tcell.nextElem cursor = some tv)
    (hok : IterOk ctx level st) (hlvl : level < n) (hgsz : ctx.g.size = n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e) (hlen : len = e + 1 - tc)
    (href : oRef < len) (habsent : ¬ ChildPath ctx tcLevel boundary level st tc targets key oRef)
    (hcarrier : CellCarrier ctx st.ptn level st.lab ref cur store)
    (hatRef : ref[tc]! = st.lab[tc + oRef]!) (hatCur : cur[tc]! = tv) :
    PathCover ctx tcLevel boundary level st tc len targets key tcell (some tv) := by
  have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  apply VisitCover.carrier h hnext (by omega) href habsent hcarrier hatRef hatCur
  intro γ o j hc hs ho hj hmap
  exact RefPath.carried_iff hok hlvl hgsz hc hs hcell hne (by omega) (by omega) hmap

/-- A carrier to an earlier reference child discharges the current child
using the ranked coverage invariant, including references removed by
previous filters. -/
theorem reference (h : PathCover ctx tcLevel boundary level st tc len targets key tcell cursor)
    {tv e oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : tcell.nextElem cursor = some tv)
    (hok : IterOk ctx level st) (hlvl : level < n) (hgsz : ctx.g.size = n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e) (hlen : len = e + 1 - tc)
    (href : oRef < len) (hearlier : st.lab[tc + oRef]! < tv)
    (hcarrier : CellCarrier ctx st.ptn level st.lab ref cur store)
    (hatRef : ref[tc]! = st.lab[tc + oRef]!) (hatCur : cur[tc]! = tv) :
    PathCover ctx tcLevel boundary level st tc len targets key tcell (some tv) :=
  h.carrier hnext hok hlvl hgsz hcell hne hlen href (h.smaller hnext href hearlier)
    hcarrier hatRef hatCur

end PathCover

end Hex.GraphIso.Nauty.Generation
