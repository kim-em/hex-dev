/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CheapPrefix
public import HexGraphIso.Nauty.Sparse.CodeTransport

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An open native descent following a prefix of a selected cheap subtree
chooses the next saved target. Sibling offsets and cache contents may differ. -/
theorem CodePath.target_prefix {G : Hex.SparseGraph n} {tcLevel base last level : Nat}
    {root leaf current : RefineSt n} {path xs : List (Nat × Nat)} {codes : List Nat}
    (h : CodePath G base root path last leaf codes)
    (hr : RefineSt.Ready G base root) (hshape : NodeShape n base root.ptn)
    (hsel : h.Selects tcLevel) (hd : discreteAt leaf.ptn last n = true)
    (hp : DescPath G base root xs level current) (hprefix : xs.map Prod.fst <+: path.map Prod.fst)
    (hopen : discreteAt current.ptn level n ≠ true) :
    xs.length < path.length ∧
      targetcell (.ofGraph G) current.lab current.ptn level tcLevel (-1) = (path.map Prod.fst)[xs.length]! := by
  induction h generalizing level current xs with
  | refl base root =>
    have hx : xs = [] := List.map_eq_nil_iff.mp (List.prefix_nil.mp hprefix)
    subst xs
    cases hp
    exact (hopen hd).elim
  | @step base last root leaf path codes tc len a scratch hc hb hn ha hs tail ih =>
    cases hp with
    | refl =>
      refine ⟨by simp, ?_⟩
      simpa only [List.length_nil, List.map_cons, List.getElem!_cons_zero] using hsel.1.symm
    | @step _ level _ current xs tcV lenV b other hcV hbV hnV hb' ht tailV =>
      have hp' : tcV = tc ∧ xs.map Prod.fst <+: path.map Prod.fst := by
        simpa only [List.map_cons, List.cons_prefix_cons] using hprefix
      rcases hp' with ⟨heqtc, hp'⟩
      subst tcV
      have hlen : len = lenV := by
        rcases isCell_disjoint_or_eq hc hcV with h | h | h
        · omega
        · omega
        · exact h.2
      subst lenV
      have hready := hr.child hc hb hn ha scratch hs
      have hreadyV := hr.child hcV hbV hnV hb' other ht
      obtain ⟨p, hiso, hchild⟩ := hr.children hshape hc hb hn hb' ha other scratch ht hs
      obtain ⟨W, zs, hW, hz, he⟩ := tailV.map G G p hiso hreadyV hready hchild
      have hprefixW : zs.map Prod.fst <+: path.map Prod.fst := by rw [hz]; exact hp'
      have hopenW : discreteAt W.ptn level n ≠ true := by rw [he.ptn]; exact hopen
      obtain ⟨hshort, htarget⟩ := ih hready (hr.child_shape hc hb hn ha scratch hs hshape)
        hsel.2 hd hW hprefixW hopenW
      have hlength : zs.length = xs.length := by
        simpa only [List.length_map] using congrArg List.length hz
      rw [hlength] at hshort htarget
      have heTarget := RefineSt.Equiv.target G G p hiso (tailV.ready hreadyV) (hW.ready hready)
        he tcLevel (-1)
      refine ⟨by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hshort, ?_⟩
      simpa only [List.length_cons, List.map_cons, List.getElem!_cons_succ] using heTarget.symm.trans htarget

end Hex.GraphIso.Nauty.Sparse
