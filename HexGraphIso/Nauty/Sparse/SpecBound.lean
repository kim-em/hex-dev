/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecFuel

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every target member increases the accurate count by one and preserves
the node invariants and depth bound used to exhaust the unpruned tree. -/
theorem breakout_node {n level numcells tc len o : Nat} {lab ptn : Array Nat} {active : VSet n}
    (hp : lab.toList.Perm (List.range n)) (h : NodeOk n level lab ptn active)
    (hc : numcells = bcount ptn level n) (hl : level ≤ numcells)
    (ht : IsCell ptn level tc len) (hr : tc + len ≤ n) (hn : 1 < len) (ho : o < len) :
    let child := breakout n lab ptn (level + 1) tc lab[tc + o]!
    child.1.toList.Perm (List.range n) ∧ NodeOk n (level + 1) child.1 child.2.1 child.2.2 ∧
    numcells + 1 = bcount child.2.1 (level + 1) n ∧ level + 1 ≤ numcells + 1 := by
  have hend : ptn[n - 1]! ≤ level := by simpa only [h.ptnSize] using h.ptnEnd
  have hbound := bcount_le ptn level n
  have hweak : ∀ q, q < n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]! := by
    intro q _
    rcases h.vals q with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by omega)
  have hopen := ht.2.2.1 tc (Nat.le_refl _) (by omega)
  have hsplit := bcount_breakout_eq hweak hopen (by rw [h.ptnSize]; omega) n (Nat.le_refl _)
  rw [ite_eq_left (by omega : tc < n)] at hsplit
  exact ⟨breakout_perm hp h.ptnSize hend ht hr ho,
    childNodeOk h.labSize h.labOk h.ptnSize h.ptnEnd h.vals ht hr ho,
    by dsimp only [breakout]; omega, by omega⟩

/-- Increasing an already sufficient recursion bound changes no leaf. The
induction covers every target member, so no branch is silently truncated. -/
theorem specLeaves_succ (G : Hex.SparseGraph n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (hp : lab.toList.Perm (List.range n)) (h : NodeOk n level lab ptn active)
    (hc : numcells = bcount ptn level n) (hl : level ≤ numcells)
    (hf : n < fuel + numcells) :
    specLeaves G tcLevel (fuel + 1) level lab ptn active numcells =
      specLeaves G tcLevel fuel level lab ptn active numcells := by
  induction fuel generalizing level lab ptn active numcells with
  | zero => have := bcount_le ptn level n; omega
  | succ fuel ih =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    obtain ⟨hp', h', hc', hm⟩ := refine_node G level lab ptn active numcells hp h hc
    change r.lab.toList.Perm (List.range n) at hp'
    change NodeOk n level r.lab r.ptn r.active at h'
    change r.numcells = bcount r.ptn level n at hc'
    change numcells ≤ r.numcells at hm
    have hend : r.ptn[n - 1]! ≤ level := by simpa only [h'.ptnSize] using h'.ptnEnd
    conv => lhs; rw [specLeaves]
    conv => rhs; rw [specLeaves]
    dsimp only
    by_cases hd : discreteAt r.ptn level n = true
    · dsimp only [r] at hd
      simp only [hd, ite_true]
    · have hd' := hd
      dsimp only [r] at hd'
      simp only [hd']
      have hcount : bcount r.ptn level n < n := by
        have hbound := bcount_le r.ptn level n
        have hn : bcount r.ptn level n ≠ n := fun hh =>
          hd ((discreteAt_iff_bcount h'.ptnSize.symm h'.ptnEnd).mpr hh)
        omega
      let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
      obtain ⟨ht, hn, hr⟩ := maketargetcell_valid G r.lab r.ptn level tcLevel (-1) hp'
        h'.ptnSize hend hcount
      apply congrArg List.flatten
      apply List.map_congr_left
      intro o ho
      have ho : o < target.2.2 := List.mem_range.mp ho
      obtain ⟨hpchild, hchild, hcchild, hlchild⟩ := breakout_node hp' h' hc' (by omega) ht hr hn ho
      apply congrArg (List.map (SpecLeaf.prepend r.longcode))
      exact ih _ _ _ _ _ hpchild hchild hcchild hlchild
        (by change n < fuel + (r.numcells + 1); omega)

/-- Every larger recursion bound enumerates exactly the same complete tree. -/
theorem specLeaves_add (G : Hex.SparseGraph n) (tcLevel fuel extra level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (hp : lab.toList.Perm (List.range n)) (h : NodeOk n level lab ptn active)
    (hc : numcells = bcount ptn level n) (hl : level ≤ numcells)
    (hf : n < fuel + numcells) :
    specLeaves G tcLevel (fuel + extra) level lab ptn active numcells =
      specLeaves G tcLevel fuel level lab ptn active numcells := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [Nat.add_succ, specLeaves_succ G tcLevel (fuel + extra) level lab ptn active numcells
      hp h hc hl (by omega), ih]

end Hex.GraphIso.Nauty.Sparse
