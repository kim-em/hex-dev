/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Cheap
public import HexGraphIso.Nauty.Correct.Generation.Frame

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- The actual matching small-cell visit supplies a generated vertex
carrier at its enclosing frame. SearchOut preserves the individualized
singleton, locating the emitted deep-leaf carrier at the caller's vertex. -/
theorem cheap_visit {G : Colored n k} {ctx : Ctx n} {base : List (Fin n)}
    {inf tcLevel fuel level numcells pos : Nat} {st : SearchSt n}
    {targets : List Nat} {key : Key n} {u v : Fin n}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hsearch : SearchOk G level numcells st)
    (hS : SubtreeOk ctx level (refine ctx level st.lab st.ptn st.active numcells))
    (hsize : st.firstlab.size = n) (hperm : st.firstlab.toList.Perm (List.range n))
    (hm : Matches ctx level st targets key)
    (hleaf : HasLeaf ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells) targets key)
    (hlevel : st.eqlevFirst = level - 1) (hclear : st.needshortprune = false)
    (hguide : st.gcaFirst < level) (hfuel : n < level + fuel)
    (hpos : pos < n) (hcell : IsCell st.ptn level pos 1)
    (hatRef : st.firstlab[pos]! = u.val) (hatCur : st.lab[pos]! = v.val)
    (htrace : ∀ γ ∈ (otherNode ctx inf tcLevel fuel level numcells st).2.genTrace, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ (otherNode ctx inf tcLevel fuel level numcells st).2.genTrace,
      ∀ b ∈ base, γ[b.val]! = b.val) :
    (otherNode ctx inf tcLevel fuel level numcells st).1 = Int.ofNat st.gcaFirst ∧
      Aut.Carries G base u v := by
  have hbound : level ≤ n := Nat.le_trans hsearch.bc (bcount_le st.ptn level n)
  have hgsz : ctx.g.size = n := by rw [hg]; exact size_rowsOf G
  have hsymm : ∀ a b, a < n → b < n → (ctx.g[a]!).mem b = (ctx.g[b]!).mem a := by
    rw [hg]
    exact rowsOf_symm G
  have hloop : ∀ a, a < n → (ctx.g[a]!).mem a = false := by
    rw [hg]
    exact rowsOf_loopless G
  obtain ⟨hr, hc⟩ := cheap_reference inf tcLevel hgsz hsymm hloop fuel level numcells st targets key
    hS hsize hperm hm hleaf hlevel hclear hguide hbound hfuel
  have hout := otherNode_ok G ctx inf hinf tcLevel (by omega : 0 < n) fuel level numcells st
    hsearch (by omega) (by omega)
  exact ⟨hr, carries_label hc htrace hfix hpos hatRef ((hout.atSingleton hcell).trans hatCur)⟩

end Hex.GraphIso.Nauty.Generation
