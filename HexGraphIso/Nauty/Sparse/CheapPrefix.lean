/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CheapLeaves

public section

namespace Hex.GraphIso.Nauty.Sparse.DescPath

/-- A valid discrete native node has no further individualization step. -/
theorem nil_of_discrete {G : Hex.SparseGraph n} {base last : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath G base root path last leaf)
    (hr : RefineSt.Ready G base root) (hd : discreteAt root.ptn base n = true) : path = [] := by
  cases h with
  | refl => rfl
  | step tc len o scratch hc hb hn ho hs tail =>
    have hm := mem_cells_of_isCell (nn := n) (Nat.le_of_eq hr.spec.node.ptnSize.symm)
      hr.spec.node.ptnEnd hc (by omega) (by rw [hr.spec.node.ptnSize]; exact hb)
    have he := beq_iff_eq.mp (cells_eq_of_discreteAt hd _ hm)
    omega

/-- Below a cheap-shaped equitable node, a discrete descent following a
prefix of another discrete descent's targets reaches its full depth.
Each branch keeps its own executed cached refinement calls. -/
theorem leaf_depth (G : Hex.SparseGraph n) (tcs : List Nat) :
    ∀ {level last current : Nat} {root U V : RefineSt n} {xs ys : List (Nat × Nat)},
      RefineSt.Ready G level root → NodeShape n level root.ptn →
      DescPath G level root xs last U → discreteAt U.ptn last n = true →
      DescPath G level root ys current V → ys.map Prod.fst = tcs →
      tcs <+: xs.map Prod.fst → discreteAt V.ptn current n = true → current = last := by
  induction tcs with
  | nil =>
    intro level last current root U V xs ys hr hshape hU hdU hV hy hp hdV
    have hy' : ys = [] := by cases ys <;> simp_all
    subst ys
    cases hV
    have hx := hU.nil_of_discrete hr hdV
    subst xs
    cases hU
    rfl
  | cons tc tcs ih =>
    intro level last current root U V xs ys hr hshape hU hdU hV hy hp hdV
    cases hV with
    | refl => simp at hy
    | @step level current root V ys tcV lenV b other hcV hbV hnV hb ht tailV =>
      have hy' : tcV = tc ∧ ys.map Prod.fst = tcs := by
        simpa only [List.map_cons, List.cons.injEq] using hy
      rcases hy' with ⟨hVtc, hy'⟩
      subst tcV
      cases hU with
      | refl => simp at hp
      | @step _ last _ U xs tcU lenU a scratch hcU hbU hnU ha hs tailU =>
        have hp' : tc = tcU ∧ tcs <+: xs.map Prod.fst := by
          simpa only [List.map_cons, List.cons_prefix_cons] using hp
        rcases hp' with ⟨rfl, hp'⟩
        have hlen : lenU = lenV := by
          rcases isCell_disjoint_or_eq hcU hcV with h | h | h
          · omega
          · omega
          · exact h.2
        subst lenV
        obtain ⟨p, hiso, hchild⟩ := hr.children hshape hcU hbU hnU ha hb scratch other hs ht
        have hreadyU := hr.child hcU hbU hnU ha scratch hs
        have hreadyV := hr.child hcV hbV hnV hb other ht
        obtain ⟨W, zs, hW, hz, he⟩ := tailU.map G G p hiso hreadyU hreadyV hchild
        apply ih hreadyV (hr.child_shape hcV hbV hnV hb other ht hshape) hW
          (by rw [he.ptn]; exact hdU) tailV hy'
        · rw [hz]
          exact hp'
        · exact hdV

/-- Matching a saved target prefix at a discrete leaf gives both the saved
depth and the saved normalized sparse graph. -/
theorem leaf_prefix {G : Hex.SparseGraph n} {level last current : Nat}
    {root U V : RefineSt n} {xs ys : List (Nat × Nat)} {u v : Label n}
    (hr : RefineSt.Ready G level root) (hshape : NodeShape n level root.ptn)
    (hU : DescPath G level root xs last U) (hdU : discreteAt U.ptn last n = true)
    (hu : Label.ofArray? n U.lab = some u)
    (hV : DescPath G level root ys current V) (hp : ys.map Prod.fst <+: xs.map Prod.fst)
    (hdV : discreteAt V.ptn current n = true) (hv : Label.ofArray? n V.lab = some v) :
    current = last ∧ G.relabel v.perm = G.relabel u.perm := by
  have hdepth := leaf_depth G (ys.map Prod.fst) hr hshape hU hdU hV rfl hp hdV
  have htcs : ys.map Prod.fst = xs.map Prod.fst := by
    apply hp.eq_of_length
    have := hU.length
    have := hV.length
    simp only [List.length_map]
    omega
  refine ⟨hdepth, ?_⟩
  subst current
  exact (leaf_graph G (xs.map Prod.fst) hr hshape hU rfl hdU hu hV htcs hdV hv).symm

end Hex.GraphIso.Nauty.Sparse.DescPath
