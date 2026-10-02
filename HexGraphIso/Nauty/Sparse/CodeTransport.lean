/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PathCodes
public import HexGraphIso.Nauty.Sparse.ReadyTarget

public section

namespace Hex.GraphIso.Nauty.Sparse.CodePath

/-- Transport a selected native descent under isomorphism, retaining its
entire refinement-code sequence and unhinted target rule. Corresponding
vertices may occupy different offsets and caches remain independent. -/
theorem map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {tcLevel base last : Nat} {root leaf other : RefineSt n}
    {path : List (Nat × Nat)} {codes : List Nat}
    (hpath : CodePath G base root path last leaf codes)
    (hr : RefineSt.Ready G base root) (ht : RefineSt.Ready H base other)
    (he : RefineSt.Equiv (renamingOf p) base root other) (hsel : hpath.Selects tcLevel) :
    ∃ out path', ∃ trace : CodePath H base other path' last out codes,
      trace.Selects tcLevel ∧ path'.map Prod.fst = path.map Prod.fst ∧
      RefineSt.Equiv (renamingOf p) last leaf out := by
  induction hpath generalizing other with
  | refl level st =>
    rw [he.code]
    exact ⟨other, [], .refl _ _, trivial, rfl, he⟩
  | @step level last st leaf path codes tc len o scratch hc hb hn ho hs tail ih =>
    let fresh := Scratch.fresh n
    have hf : Scratch.Bounded n fresh :=
      (Scratch.fresh_valid n other.lab other.ptn (level + 1)).toBounded
    obtain ⟨j, hj, _, hchild⟩ := child_match G H p hiso hr ht he.ptn he.count.symm he.cells
      hc hb hn ho scratch fresh hs hf
    have hc' : IsCell other.ptn level tc len := by rw [he.ptn]; exact hc
    obtain ⟨out, path', trace, hselected, htcs, hend⟩ := ih
      (hr.child hc hb hn ho scratch hs) (ht.child hc' hb hn hj fresh hf) hchild hsel.2
    have htarg := RefineSt.Equiv.target G H p hiso hr ht he tcLevel (-1)
    have hchoice : tc = targetcell (.ofGraph H) other.lab other.ptn level tcLevel (-1) :=
      hsel.1.trans htarg.symm
    rw [he.code]
    refine ⟨out, (tc, j) :: path', .step tc len j fresh hc' hb hn hj hf trace, ?_, ?_, hend⟩
    · simpa only [CodePath.Selects] using And.intro hchoice hselected
    · simp only [List.map_cons, htcs]

end Hex.GraphIso.Nauty.Sparse.CodePath
