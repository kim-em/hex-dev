/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineTransport
public import HexGraphIso.Nauty.Sparse.Renaming
public import HexGraphIso.Nauty.Invariant.PathStab

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A checked automorphism stabilizing the input cells also stabilizes
the cells produced by the actual cached sparse refinement. The proof uses
native refinement equivariance with the same input on both sides. -/
theorem cellStab_refineWith (G : Hex.SparseGraph n) (level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n scratch) {gamma : Array Nat}
    (hg : checkAutom (Graph.context G).g gamma = true) (hc : CellStab ptn level lab gamma) :
    let r := refineWith (.ofGraph G) level lab ptn active numcells scratch
    CellStab r.ptn level r.lab gamma := by
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound (by simp [Graph.context]) hg
  have hmap (a : Array Nat) (h : a.toList.Perm (List.range n)) :
      a.map (renamingOf σ.toPerm).toFun = a.map (fun v => gamma[v]!) := by
    have hs : a.size = n := by simpa using h.length_eq
    apply map_congr_of_labOk (fun i hi => perm_bound h (by omega))
    intro v hv
    exact (renamingOf_lt σ.toPerm hv).trans ((Renaming.get_toPerm σ ⟨v, hv⟩).trans (hσ v hv))
  have hi : cellsPerm ptn level lab (lab.map (renamingOf σ.toPerm).toFun) := by
    rw [hmap lab hp]
    exact hc
  have he := refineWith_equiv G G σ.toPerm (Graph.context_iso G G σ hrows)
    level lab lab ptn active numcells scratch scratch hp hp hs hend ha hb hb hi
  have hr := refineWith_state G level lab ptn active numcells scratch hp hs hend ha hb
  have hh := he.cells
  rw [hmap _ hr.1] at hh
  exact hh

end Hex.GraphIso.Nauty.Sparse
