/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ChildTransport

public section

namespace Hex.GraphIso.Nauty.Sparse.DescPath

/-- Transport an entire literal native descent under an isomorphism.
Target positions, depths and refinement observations agree; corresponding
vertices may occupy different offsets within a tied cell. -/
theorem map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {base last : Nat} {root leaf other : RefineSt n} {path : List (Nat × Nat)}
    (hpath : DescPath G base root path last leaf)
    (hr : RefineSt.Ready G base root) (ht : RefineSt.Ready H base other)
    (he : RefineSt.Equiv (renamingOf p) base root other) :
    ∃ out path', DescPath H base other path' last out ∧
      path'.map Prod.fst = path.map Prod.fst ∧ RefineSt.Equiv (renamingOf p) last leaf out := by
  induction hpath generalizing other with
  | refl level st => exact ⟨other, [], .refl level other, rfl, he⟩
  | @step level last st leaf path tc len o scratch hc hb hn ho hs tail ih =>
    let fresh := Scratch.fresh n
    have hf : Scratch.Bounded n fresh :=
      (Scratch.fresh_valid n other.lab other.ptn (level + 1)).toBounded
    obtain ⟨j, hj, _, hchild⟩ := child_match G H p hiso hr ht he.ptn he.count.symm he.cells
      hc hb hn ho scratch fresh hs hf
    have hc' : IsCell other.ptn level tc len := by rw [he.ptn]; exact hc
    obtain ⟨out, path', hout, htcs, hend⟩ := ih
      (hr.child hc hb hn ho scratch hs) (ht.child hc' hb hn hj fresh hf) hchild
    refine ⟨out, (tc, j) :: path', .step tc len j fresh hc' hb hn hj hf hout, ?_, hend⟩
    simp only [List.map_cons, htcs]

end Hex.GraphIso.Nauty.Sparse.DescPath
