/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.Descent

public section

namespace Hex.GraphIso.Nauty

/-- A sentinel cannot occur inside the real codes of the first path. -/
theorem FirstCodeInv.sentinel_bound {n slot elev : Nat} {cs fs : List Nat}
    {store : Array Nat} (h : FirstCodeInv n cs fs store elev)
    (hslot : 1 ≤ slot) (hsent : store[slot]! = codeSentinel) : fs.length < slot := by
  by_cases hlt : fs.length < slot
  · exact hlt
  have hle : slot ≤ fs.length := by omega
  have hc := h.fcontent slot hslot hle
  have hi : slot - 1 < fs.length := by omega
  have hm : fs[slot - 1]! ∈ fs := by
    rw [getElem!_pos fs (slot - 1) hi]
    exact List.getElem_mem hi
  have hlt := h.flt _ hm
  omega

namespace Engine

variable {n k : Nat}

/-- A frozen ancestor's selected descent to the saved first leaf.
The sentinel connects its actual depth to the first-code comparison. -/
structure FirstRef (ctx : Ctx n) (tcLevel base : Nat) (root : RefineSt n) (st : Search n) where
  last : Nat
  leaf : RefineSt n
  path : List (Nat × Nat)
  descent : DescPath ctx base root path last leaf
  selects : Selects ctx tcLevel base root path
  targets : Targets st.firsttc base (path.map Prod.fst)
  lab : leaf.lab = st.firstlab
  discrete : ∀ i, i < n → leaf.ptn[i]! ≤ last
  sentinel : st.firstcode[last + 1]! = codeSentinel

/-- Updating other state fields leaves a saved reference history valid. -/
def FirstRef.congr {ctx : Ctx n} {tcLevel base : Nat} {root : RefineSt n}
    {st out : Search n} (h : FirstRef ctx tcLevel base root st)
    (heq : out.reference = st.reference) : FirstRef ctx tcLevel base root out := by
  have hcodes := congrArg (fun x : Array Nat × Array Int × Array Nat => x.1) heq
  have htargets := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) heq
  have hlab := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2) heq
  change out.firstcode = st.firstcode at hcodes
  change out.firsttc = st.firsttc at htargets
  change out.firstlab = st.firstlab at hlab
  exact ⟨h.last, h.leaf, h.path, h.descent, h.selects, htargets.symm ▸ h.targets,
    h.lab.trans hlab.symm, h.discrete, by rw [hcodes]; exact h.sentinel⟩

/-- An off-path call preserves every frozen first-reference history. -/
def FirstRef.node {ctx : Ctx n} {inf tcLevel fuel base level numcells : Nat}
    {root : RefineSt n} {st : Search n} (h : FirstRef ctx tcLevel base root st) :
    FirstRef ctx tcLevel base root (node false ctx inf tcLevel fuel level numcells st).2 :=
  h.congr (node_reference ctx inf tcLevel fuel level numcells st)

/-- A later sibling sweep preserves every frozen first-reference history. -/
def FirstRef.sweep {ctx : Ctx n} {first : Bool}
    {inf tcLevel fuel cfuel base level numcells tc tv1 index : Nat}
    {cursor : Option Nat} {cell : VSet n} {root : RefineSt n} {st : Search n}
    (h : FirstRef ctx tcLevel base root st) (hpast : Generic.Past first tv1 cursor) :
    FirstRef ctx tcLevel base root
      (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 :=
  h.congr (sweep_reference first ctx inf tcLevel fuel cfuel level numcells tc tv1 index cursor cell st hpast)

/-- A completed first-path call supplies a reference history at its own frame. -/
theorem firstRef_of_path {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel fuel level numcells last : Nat} {st leaf : Search n}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st.view)
    (heq : Equitable ctx level (st.refined ctx level numcells).lab
      (st.refined ctx level numcells).ptn)
    (htsize : n < st.firsttc.size) (hcsize : st.firstcode.size = n + 2) :
    Nonempty (FirstRef ctx tcLevel level (st.refined ctx level numcells)
      (node true ctx inf tcLevel fuel level numcells st).2) := by
  obtain ⟨path, U, hd, hs, ht, hl, hdisc⟩ :=
    firstPath_saved (inf := inf) hn0 hsymm hpath hlevel hok heq htsize
  have hlast := (descends_iterOk hd.descends (refined_iter hn0 hlevel hok)).lvl
  exact ⟨⟨last, U, path, hd, hs, ht, hl, hdisc, firstPath_sentinel hpath hcsize hlast⟩⟩

/-- First-code agreement cannot extend below the saved first leaf. -/
theorem FirstRef.depth {ctx : Ctx n} {tcLevel base : Nat} {root : RefineSt n}
    {st : Search n} (h : FirstRef ctx tcLevel base root st) {cs fs : List Nat}
    (hc : FirstCodeInv n cs fs st.firstcode st.eqlevFirst) : st.eqlevFirst ≤ h.last := by
  have hb := hc.sentinel_bound (by omega) h.sentinel
  have := hc.elev_fs
  omega

/-- A surviving first-code comparison follows the saved target at a cheap ancestor. -/
theorem FirstRef.target {ctx : Ctx n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : Search n}
    (h : FirstRef ctx tcLevel base root st) (hdepth : level ≤ h.last)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsmall : SubtreeOk ctx base root)
    (hcurrent : FollowsPerm ctx st.firsttc base root level current)
    (hopen : ∃ i, i < n ∧ level < current.ptn[i]!) :
    Int.ofNat (specTargetcell ctx current.lab current.ptn level tcLevel) = st.firsttc[level]! := by
  apply hcurrent.target hgsz hsymm hloop hsmall h.descent h.selects h.targets
  · exact hdepth
  · exact h.discrete
  · exact hopen

/-- The reference history and current descent justify the executable cheap scatter. -/
theorem FirstRef.scatter {ctx : Ctx n} {tcLevel level : Nat}
    {root current : RefineSt n} {st : Search n}
    (h : FirstRef ctx tcLevel st.gcaFirst root st) (hdepth : level ≤ h.last)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsmall : SubtreeOk ctx st.gcaFirst root)
    (hcurrent : FollowsPerm ctx st.firsttc st.gcaFirst root level current)
    (hdisc : ∀ i, i < n → current.ptn[i]! ≤ level)
    (hlab : st.lab = current.lab) (hwork : st.workperm.size = n) :
    checkAutom ctx.g (scatter st.firstlab st).workperm = true := by
  obtain ⟨V, ⟨path, hd, ht⟩, hVL, hVP⟩ := hcurrent.leaf hsmall.it hdisc
  apply scatter_of_descPaths hgsz hsymm hloop hsmall h.descent hd
    (ht.prefix h.targets ?_) h.discrete (fun i hi => by rw [hVP]; exact hdisc i hi)
    h.lab.symm (hlab.trans hVL.symm) hwork
  have hlen := h.descent.length
  have hclen := hd.length
  simp only [List.length_map]
  omega

end Engine

end Hex.GraphIso.Nauty
