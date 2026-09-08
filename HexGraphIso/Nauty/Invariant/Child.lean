/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.Invariant.Refine
public import HexGraphIso.Nauty.Spec.Descent
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

/-- The child specification indexed by its individualized vertex. -/
@[expose] def vertexKey (ctx : Ctx n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (tc numcells v : Nat) : Key n :=
  let child := breakout n lab ptn (level + 1) tc v
  specNode ctx tcLevel fuel (level + 1) child.1 child.2.1 child.2.2 (numcells + 1)

/-- Vertex and offset indexing give the same child specification. -/
theorem vertexKey_offset (ctx : Ctx n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (tc numcells offset : Nat) :
    vertexKey ctx tcLevel fuel level lab ptn tc numcells lab[tc + offset]! =
      childKey ctx tcLevel fuel level lab ptn tc numcells offset := rfl

/-- A checked cell stabilizer identifies the child keys at the vertices
it carries, independently of their offsets in the target cell. -/
theorem SearchOk.vertex_key {G : Colored n k} {ctx : Ctx n}
    {st : SearchSt n} {level numcells tc len v fuel : Nat} {γ : Array Nat}
    (h : SearchOk G level numcells st) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = n) (ha : checkAutom ctx.g γ = true)
    (hstab : CellStab st.ptn level st.lab γ)
    (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n)
    (hv : (windowSet n st.lab tc len).mem v = true)
    (hfuel : level + 1 + fuel ≤ n + 1) (tcLevel : Nat) :
    vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v =
      vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells γ[v]! := by
  have hok := labOk_of_reach h.labSize h.reach
  have hw := windowSet_carry hstab hc (by rw [h.labSize]; exact hr) hok hv
  obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
  obtain ⟨o', ho', he'⟩ := mem_segN_iff.mp (mem_windowSet.mp hw).2
  have hvals : ∀ q : Nat, st.ptn[q]! ≤ level ∨ st.ptn[q]! = n + 2 := by
    intro q
    by_cases hq : q < n
    · exact h.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [h.ptnSize]; omega)]
      exact Nat.zero_le _
  have heq := childKey_of_carried (numcells := numcells) hgsz ha tcLevel fuel level hstab h.labSize hok
    h.ptnSize (searchOk_end hn0 h hlevel) hvals hc hr ho' ho hfuel (by rw [he, he'])
  have e₁ : vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v =
      childKey ctx tcLevel fuel level st.lab st.ptn tc numcells o := by
    rw [← he]
    rfl
  have e₂ : vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells γ[v]! =
      childKey ctx tcLevel fuel level st.lab st.ptn tc numcells o' := by
    rw [← he']
    rfl
  exact e₁.trans (heq.symm.trans e₂.symm)

/-- A recovered loop state individualizes the same vertex as its frozen
entry frame, possibly at a different offset within the target cell.  The
two resulting child labellings remain cell-equivalent. -/
theorem SearchOut.breakoutPerm {G : Colored n k} {level numcells tc len o : Nat}
    {st out : SearchSt n} (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    ∃ oCur, oCur < len ∧ out.lab[tc + oCur]! = st.lab[tc + o]! ∧
      cellsPerm (st.ptn.set! tc (level + 1)) (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (breakout n out.lab out.ptn (level + 1) tc st.lab[tc + o]!).1 := by
  have hend := searchOk_end hn0 hok hlevel
  have hmem : st.lab[tc + o]! ∈ segN st.lab tc len :=
    mem_segN_iff.mpr ⟨o, ho, rfl⟩
  have hmem' : st.lab[tc + o]! ∈ segN out.lab tc len :=
    (h.perm tc len hcell).mem_iff.mp hmem
  obtain ⟨oCur, hoCur, hat⟩ := mem_segN_iff.mp hmem'
  refine ⟨oCur, hoCur, hat, ?_⟩
  have hptn := h.ptnEq hok hout
  let σ : Renaming n := {
    toFun := id
    inj := fun _ _ heq => heq
    maps := fun _ => Iff.rfl }
  have hmap : out.lab.map σ.toFun = out.lab := by
    apply Array.ext (by simp)
    intro i hi hi'
    simp [σ]
  have hcp : cellsPerm st.ptn level st.lab (out.lab.map σ.toFun) := by
    rw [hmap]
    exact h.perm
  have hvals : ∀ q, q < n →
      st.ptn[q]! ≤ level ∨ level + 1 < st.ptn[q]! := by
    have hleveln : level ≤ n :=
      Nat.le_trans hok.bc (bcount_le st.ptn level n)
    intro q hq
    rcases hok.vals q hq with hq' | hq'
    · exact Or.inl hq'
    · exact Or.inr (by rw [hq']; omega)
  have hcell' : (tc, tc + len - 1) ∈ cells st.ptn level n :=
    isCell_mem_cells hcell (by rw [hok.ptnSize]; exact Nat.le_refl n)
      hend (by omega)
  have hb := breakout_cellsPerm_map (n := n)
    (σ := σ) (labV := st.lab) (labU := out.lab) (ptn := st.ptn)
    (level := level) (tc := tc) (e := tc + len - 1)
    (oV := o) (oU := oCur) hok.ptnSize hok.labSize hout.labSize hend
    hvals hcp hcell' (by omega) (by omega) (by omega) (by
      dsimp only [σ, id]
      exact hat.symm)
  have map_id (a : Array Nat) : a.map σ.toFun = a := by
    apply Array.ext (by simp)
    intro i hi hi'
    simp [σ]
  rw [map_id, hat] at hb
  rw [hptn]
  exact hb

/-- Splitting a nonempty cell start keeps the final partition position
closed one level later. -/
theorem split_end {ptn : Array Nat} {level tc : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) (htc : tc < ptn.size) :
    (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
  rw [Array.size_set!]
  rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
  · rw [Array.getElem!_set!_self _ _ _ (by omega)]
    omega
  · rw [Array.getElem!_set!_ne _ _ _ _ hx]
    omega

/-- The active singleton created by individualization marks a cell start
of the split partition. -/
theorem split_starts {ptn : Array Nat} {level tc len : Nat}
    (hcell : IsCell ptn level tc len)
    (hrange : tc + len ≤ n) :
    ∀ v : Nat, ((VSet.empty : VSet n).insert tc).mem v = true →
      v = 0 ∨ (ptn.set! tc (level + 1))[v - 1]! ≤ level + 1 := by
  intro v hv
  have htc : tc < n := by
    have := hcell.1
    omega
  rw [mem_single htc] at hv
  have hvtc : v = tc := of_decide_eq_true hv
  subst v
  rcases Decidable.em (tc = 0) with h0 | h0
  · exact Or.inl h0
  · rcases hcell.2.1 with hstart | hstart
    · exact Or.inl hstart
    · right
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      omega

/-- Individualizing the same vertex after recovering its parent leaves
the specification child key unchanged, despite within-cell label movement. -/
theorem SearchOut.child_key {G : Colored n k} {ctx : Ctx n}
    {level numcells tc len o specFuel tcLevel : Nat}
    {st out child : SearchSt n}
    (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len)
    (hclab : child.lab = (breakout n out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).1)
    (hcptn : child.ptn = (breakout n out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).2.1)
    (hcactive : child.active = (breakout n out.lab out.ptn (level + 1) tc
      st.lab[tc + o]!).2.2)
    (hcanon : child.canonlab = out.canonlab)
    (hfuel : level + 1 + specFuel ≤ n + 1) :
    childKey ctx tcLevel specFuel level st.lab st.ptn tc numcells o =
      specNode ctx tcLevel specFuel (level + 1) child.lab child.ptn child.active (numcells + 1) := by
  obtain ⟨oCur, hoCur, hat, hperm⟩ :=
    h.breakoutPerm hok hout hn0 hlevel hcell hlen hrange ho
  have hptn := h.ptnEq hok hout
  have hcellOut : IsCell out.ptn level tc len := by
    rw [hptn]
    exact hcell
  have hclab' : child.lab = (breakout n out.lab out.ptn (level + 1) tc
      out.lab[tc + oCur]!).1 := by
    rw [hat]
    exact hclab
  have hcptn' : child.ptn = out.ptn.set! tc (level + 1) := by
    rw [hcptn, breakout_ptn]
  have hchildOk := breakout_searchOk (st' := child) hn0 hout hlevel
    hcellOut hlen hrange hoCur hclab' hcptn' hcanon
  let refChild : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.2 }
  have hrefOk : SearchOk G (level + 1) (numcells + 1) refChild := by
    apply breakout_searchOk hn0 hok hlevel hcell hlen hrange ho
    · rfl
    · exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!
    · rfl
  have hpart : child.ptn = refChild.ptn := by
    rw [hcptn', hptn]
    rfl
  have hactive : child.active = refChild.active := by
    rw [hcactive]
    rfl
  change specNode ctx tcLevel specFuel (level + 1) refChild.lab refChild.ptn refChild.active (numcells + 1) = _
  rw [hpart, hactive]
  apply specNode_perm tcLevel specFuel (level + 1) refChild.lab child.lab refChild.ptn
    refChild.active (numcells + 1)
  · change cellsPerm
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).2.1 (level + 1)
      (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1 child.lab
    rw [breakout_ptn, hclab]
    exact hperm
  · rw [hchildOk.labSize, hrefOk.labSize]
  · exact hrefOk.labSize
  · exact labOk_of_reach hrefOk.labSize hrefOk.reach
  · exact labOk_of_reach hchildOk.labSize hchildOk.reach
  · exact hrefOk.ptnSize
  · exact split_end (searchOk_end hn0 hok hlevel) (by
      rw [hok.ptnSize]
      omega)
  · exact split_starts hcell (by omega)
  · intro q
    rcases Nat.lt_or_ge q n with hq | hq
    · exact hrefOk.vals q hq
    · left
      rw [getElem!_neg _ _ (by rw [hrefOk.ptnSize]; omega)]
      exact Nat.zero_le _
  · exact hfuel

/-- Recovery preserves each target vertex's child specification. -/
theorem SearchOut.vertex_key {G : Colored n k} {ctx : Ctx n}
    {level numcells tc len v fuel tcLevel : Nat} {st out : SearchSt n}
    (h : SearchOut G level level st out)
    (hok : SearchOk G level numcells st) (hout : SearchOk G level numcells out)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hc : IsCell st.ptn level tc len) (hlen : 2 ≤ len) (hr : tc + len ≤ n)
    (hv : (windowSet n st.lab tc len).mem v = true)
    (hfuel : level + 1 + fuel ≤ n + 1) :
    vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v =
      vertexKey ctx tcLevel fuel level out.lab out.ptn tc numcells v := by
  obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (mem_windowSet.mp hv).2
  let b := breakout n out.lab out.ptn (level + 1) tc v
  let child : SearchSt n := { out with lab := b.1, ptn := b.2.1, active := b.2.2 }
  have hchild := h.child_key (ctx := ctx) (tcLevel := tcLevel) (child := child) hok hout hn0 hlevel hc hlen hr ho
    (by change b.1 = _; rw [he]) (by change b.2.1 = _; rw [he])
    (by change b.2.2 = _; rw [he]) rfl hfuel
  have heq : vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v =
      childKey ctx tcLevel fuel level st.lab st.ptn tc numcells o := by
    rw [← he]
    rfl
  exact heq.trans hchild

/-- The recovered labelling has the same target-cell vertex set. -/
theorem SearchOut.window_eq {G : Colored n k} {level tc len : Nat} {st out : SearchSt n}
    (h : SearchOut G level level st out) (hc : IsCell st.ptn level tc len) :
    windowSet n st.lab tc len = windowSet n out.lab tc len := by
  apply VSet.ext
  intro v
  apply Bool.eq_iff_iff.mpr
  rw [mem_windowSet, mem_windowSet]
  exact and_congr Iff.rfl (h.perm tc len hc).mem_iff

end Hex.GraphIso.Nauty
