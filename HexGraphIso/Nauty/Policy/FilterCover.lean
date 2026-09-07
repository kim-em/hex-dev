/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.ChildKey
public import HexGraphIso.Nauty.Policy.Filters
public import HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty

/-- A descending filter composes with coverage of the current live set.
Its carrier may land in an already visited child or outside an earlier
filter's survivors; ranked coverage resolves both cases. -/
theorem ChildCover.pruned {n : Nat} {g : Array (VSet n)}
    {lab ptn : Array Nat} {level tc len : Nat} {key : Nat → Key n}
    {live : Nat → Prop} {best : Option (Key n)} {filtered : VSet n}
    (h : ChildCover key id (fun v => (windowSet n lab tc len).mem v = true)
      (fun v => Generic.Covers (key v) best) live)
    (hok : LabOk lab n) (hc : IsCell ptn level tc len) (hr : tc + len ≤ lab.size)
    (hsub : ∀ v, live v → (windowSet n lab tc len).mem v = true)
    (hkey : ∀ γ, checkAutom g γ = true → CellStab ptn level lab γ →
      ∀ v, (windowSet n lab tc len).mem v = true → key v = key γ[v]!)
    (hdrop : ∀ v, live v → filtered.mem v = false →
      ∃ γ, checkAutom g γ = true ∧ CellStab ptn level lab γ ∧ γ[v]! < v) :
    ChildCover key id (fun v => (windowSet n lab tc len).mem v = true)
      (fun v => Generic.Covers (key v) best) (fun v => live v ∧ filtered.mem v = true) := by
  apply h.filterDesc
  · intro x y he hy
    rwa [he]
  · intro v hv
    cases hf : filtered.mem v with
    | true => exact Or.inl ⟨hv, rfl⟩
    | false =>
      obtain ⟨γ, ha, hs, hlt⟩ := hdrop v hv hf
      exact Or.inr ⟨γ[v]!, windowSet_carry hs hc hr hok (hsub v hv),
        hkey γ ha hs v (hsub v hv), hlt⟩

namespace Engine

variable {n k : Nat}

/-- Coverage of a frozen target cell, indexed by vertex labels. Live
vertices can include the cursor condition as well as mutable set membership. -/
@[expose] def CellCover (ctx : Ctx n) (tcLevel fuel level numcells tc len : Nat)
    (cs : List Nat) (st : Search n) (live : Nat → Prop) (best : Option (Key n)) : Prop :=
  ChildCover (fun v => prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v))
    id (fun v => (windowSet n st.lab tc len).mem v = true)
    (fun v => Generic.Covers
      (prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v)) best) live

/-- Before visiting children, every target vertex represents itself. -/
theorem CellCover.init (ctx : Ctx n) (tcLevel fuel level numcells tc len : Nat)
    (cs : List Nat) (st : Search n) (best : Option (Key n)) :
    CellCover ctx tcLevel fuel level numcells tc len cs st
      (fun v => (windowSet n st.lab tc len).mem v = true) best :=
  (ChildCover.init _ _ _).monoDone (fun _ h => h.elim)

/-- Growing the incumbent preserves all previously covered children. -/
theorem CellCover.grow {ctx : Ctx n} {tcLevel fuel level numcells tc len : Nat}
    {cs : List Nat} {st : Search n} {live : Nat → Prop} {before after : Option (Key n)}
    (h : CellCover ctx tcLevel fuel level numcells tc len cs st live before)
    (hg : Generic.Grows before after) :
    CellCover ctx tcLevel fuel level numcells tc len cs st live after :=
  h.monoDone (fun _ hc => hc.grow hg)

/-- Visiting the least live vertex advances the cursor and absorbs every
original child represented by that vertex. -/
theorem CellCover.visit {ctx : Ctx n} {tcLevel fuel level numcells tc len tv : Nat}
    {cs : List Nat} {st : Search n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hle : ∀ v, live v → tv ≤ v)
    (hc : Generic.Covers
      (prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells tv)) best) :
    CellCover ctx tcLevel fuel level numcells tc len cs st (fun v => live v ∧ tv < v) best := by
  apply h.step ?_ (fun _ hd => hd)
  intro v hv
  by_cases he : v = tv
  · subst v
    left
    intro z hz
    rwa [hz]
  · exact Or.inr ⟨v, ⟨hv, by have := hle v hv; omega⟩, rfl, Nat.le_refl _⟩

/-- A child repeating a smaller representative is already covered when
it reaches the cursor. Ranked coverage rules out a still-live carrier
below that cursor, including after earlier filters. -/
theorem CellCover.skip {ctx : Ctx n} {tcLevel fuel level numcells tc len tv rep : Nat}
    {cs : List Nat} {st : Search n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hle : ∀ v, live v → tv ≤ v)
    (hr : (windowSet n st.lab tc len).mem rep = true) (hlt : rep < tv)
    (hkey : vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells tv =
      vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells rep) :
    CellCover ctx tcLevel fuel level numcells tc len cs st (fun v => live v ∧ tv < v) best := by
  apply h.visit hle
  rcases h rep hr with hd | ⟨w, hw, _, hrank⟩
  · rwa [hkey]
  · have := hle w hw
    change w ≤ rep at hrank
    omega

/-- Exhausting the live set covers the full original target cell. -/
theorem CellCover.finish {ctx : Ctx n} {tcLevel fuel level numcells tc len : Nat}
    {cs : List Nat} {st : Search n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hempty : ∀ v, ¬ live v) :
    ∀ v, (windowSet n st.lab tc len).mem v = true → Generic.Covers
      (prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v)) best :=
  ChildCover.finish h hempty

/-- The executable cursor terminator exhausts every live member at or
after its scan start, closing coverage of the original target cell. -/
theorem CellCover.finish_cursor {ctx : Ctx n} {tcLevel fuel level numcells tc len : Nat}
    {cs : List Nat} {st : Search n} {live : Nat → Prop} {best : Option (Key n)}
    {cell : VSet n} {cursor : Option Nat}
    (h : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hmem : ∀ v, live v → cell.mem v = true)
    (hle : ∀ v, live v → VSet.scanStart cursor ≤ v)
    (hnone : cell.nextElem cursor = none) :
    ∀ v, (windowSet n st.lab tc len).mem v = true → Generic.Covers
      (prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v)) best := by
  apply h.finish
  intro v hv
  have hf := VSet.nextElem_none hnone v (hle v hv)
  rw [hmem v hv] at hf
  cases hf

/-- Restoring a parent can reorder its labels, but preserves every
vertex-indexed child key and the accumulated coverage relation. -/
theorem CellCover.frame {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc len : Nat} {cs : List Nat}
    {st out : Search n} {live : Nat → Prop} {best : Option (Key n)}
    (h : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hf : SearchOut G level level st.view out.view)
    (hok : SearchOk G level numcells st.view) (hout : SearchOk G level numcells out.view)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hc : IsCell st.ptn level tc len) (hlen : 2 ≤ len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + fuel ≤ n + 1)
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true) :
    CellCover ctx tcLevel fuel level numcells tc len cs out live best := by
  have hw : windowSet n st.lab tc len = windowSet n out.lab tc len := hf.window_eq hc
  have hk : ∀ v, (windowSet n st.lab tc len).mem v = true →
      prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v) =
        prefixKey cs (vertexKey ctx tcLevel fuel level out.lab out.ptn tc numcells v) := by
    intro v hv
    exact congrArg (prefixKey cs) (hf.vertex_key hok hout hn0 hlevel hc hlen hr hv hfuel)
  intro v hv
  have hv' : (windowSet n st.lab tc len).mem v = true := by rwa [hw]
  rcases h v hv' with hd | ⟨w, hl, he, hrank⟩
  · left
    dsimp only
    rwa [← hk v hv']
  · right
    refine ⟨w, hl, ?_, hrank⟩
    dsimp only
    rw [← hk v hv', ← hk w (hsub w hl)]
    exact he

/-- The actual long filter preserves coverage of the shrinking live set.
It uses the restored sweep's local interpretation of fix-passing pairs. -/
theorem SweepPre.long_cover {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 len : Nat} {first : Bool} {cursor : Option Nat}
    {cell : VSet n} {st : Search n} {cs : List Nat} {live : Nat → Prop} {best : Option (Key n)}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + fuel ≤ n + 1)
    (hcover : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true)
    (hmem : ∀ v, live v → cell.mem v = true) :
    CellCover ctx tcLevel fuel level numcells tc len cs st
      (fun v => live v ∧ (Nauty.longprune cell st.fixedpts st.autos).mem v = true) best := by
  apply ChildCover.pruned hcover (labOk_of_reach h.partition.labSize h.partition.reach)
    hc (by change tc + len ≤ st.view.lab.size; rw [h.partition.labSize]; exact hr) hsub
  · intro γ ha hs v hv
    exact congrArg (prefixKey cs)
      (h.partition.vertex_key hn0 h.positive hgsz ha hs hc hr hv hfuel tcLevel)
  · intro v hv hd
    exact longprune_drop (windowSet_lt (hsub v hv)) (hmem v hv) hd h.local_pairs

/-- The actual short filter preserves ranked coverage once its newest
pair passes the receiving loop's fix test. -/
theorem SweepPre.short_cover {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 len : Nat} {first : Bool} {cursor : Option Nat}
    {cell : VSet n} {st : Search n} {cs : List Nat} {live : Nat → Prop} {best : Option (Key n)}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + fuel ≤ n + 1)
    (hcover : CellCover ctx tcLevel fuel level numcells tc len cs st live best)
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true)
    (hmem : ∀ v, live v → cell.mem v = true)
    (hfix : ∀ fix mcr, st.autos.back? = some (fix, mcr) → st.fixedpts.subset fix = true) :
    CellCover ctx tcLevel fuel level numcells tc len cs st
      (fun v => live v ∧ (shortprune cell st).mem v = true) best := by
  apply ChildCover.pruned hcover (labOk_of_reach h.partition.labSize h.partition.reach)
    hc (by change tc + len ≤ st.view.lab.size; rw [h.partition.labSize]; exact hr) hsub
  · intro γ ha hs v hv
    exact congrArg (prefixKey cs)
      (h.partition.vertex_key hn0 h.positive hgsz ha hs hc hr hv hfuel tcLevel)
  · intro v hv hd
    apply Nauty.shortprune_drop (st := st.view) (windowSet_lt (hsub v hv)) (hmem v hv) hd
    intro fix mcr he
    apply h.local_pairs (fix, mcr) ?_ (hfix fix mcr he)
    simpa using Array.mem_of_back? he

end Engine
end Hex.GraphIso.Nauty
