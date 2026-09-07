/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.LeafCover

public section

namespace Hex.GraphIso.Nauty.Generation.LeafCover

variable {n : Nat} {ctx : Ctx n} {tcLevel level tc len : Nat} {st : RefineSt n}
    {targets : List Nat} {key : Key n} {tcell : VSet n} {cursor : Option Nat}

/-- An earlier original child has no matching occurrence, even if an
older pruning filter removed it from the current target set. -/
theorem smaller (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {tv o : Nat} (hnext : tcell.nextElem cursor = some tv)
    (ho : o < len) (hlt : st.lab[tc + o]! < tv) :
    ¬ ChildLeaf ctx tcLevel level st tc targets key o := by
  rcases h.cover o ho with hd | ⟨j, hj, _, hle⟩
  · exact hd
  · have hmin := nextElem_le hnext hj.2.1 hj.2.2
    dsimp only at hle
    omega

/-- A recorded carrier transfers absence from its reference child to the
current child. This consumes canonical returns without claiming that the
interrupted child was exhaustively searched. -/
theorem carrier (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {tv e oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : tcell.nextElem cursor = some tv)
    (hok : IterOk ctx level st) (hlvl : level < n) (hgsz : ctx.g.size = n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e) (hlen : len = e + 1 - tc)
    (href : oRef < len) (habsent : ¬ ChildLeaf ctx tcLevel level st tc targets key oRef)
    (hcarrier : CellCarrier ctx st.ptn level st.lab ref cur store)
    (hatRef : ref[tc]! = st.lab[tc + oRef]!) (hatCur : cur[tc]! = tv) :
    LeafCover ctx tcLevel level st tc len targets key tcell (some tv) := by
  have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  obtain ⟨γ, _, hcheck, hmap, hstab⟩ := hcarrier
  apply h.advance hnext
  intro o ho hat
  have hact : γ[st.lab[tc + oRef]!]! = st.lab[tc + o]! := by
    rw [← hatRef, hat, ← hatCur]
    exact hmap tc (by omega)
  exact fun hleaf => habsent ((HasLeaf.carried_iff hok hlvl hgsz hcheck hstab
    hcell hne (by omega) (by omega) hact).mpr hleaf)

/-- A carrier to an earlier reference child discharges the current child
using the ranked coverage invariant, including references removed by
previous filters. -/
theorem reference (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {tv e oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : tcell.nextElem cursor = some tv)
    (hok : IterOk ctx level st) (hlvl : level < n) (hgsz : ctx.g.size = n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e) (hlen : len = e + 1 - tc)
    (href : oRef < len) (hearlier : st.lab[tc + oRef]! < tv)
    (hcarrier : CellCarrier ctx st.ptn level st.lab ref cur store)
    (hatRef : ref[tc]! = st.lab[tc + oRef]!) (hatCur : cur[tc]! = tv) :
    LeafCover ctx tcLevel level st tc len targets key tcell (some tv) :=
  h.carrier hnext hok hlvl hgsz hcell hne hlen href (h.smaller hnext href hearlier)
    hcarrier hatRef hatCur

end Hex.GraphIso.Nauty.Generation.LeafCover
