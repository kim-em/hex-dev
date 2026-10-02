/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CheapChildren

public section

namespace Hex.GraphIso.Nauty.Sparse.DescPath

/-- Two discrete native descents below a cheap-shaped equitable node,
following the same target positions, have identical normalized leaf graphs.
Each descent retains its own actual cached refinement calls. -/
theorem leaf_graph (G : Hex.SparseGraph n) (tcs : List Nat) :
    ∀ {level last : Nat} {root U V : RefineSt n} {xs ys : List (Nat × Nat)} {u v : Label n},
      RefineSt.Ready G level root → NodeShape n level root.ptn →
      DescPath G level root xs last U → xs.map Prod.fst = tcs →
      discreteAt U.ptn last n = true → Label.ofArray? n U.lab = some u →
      DescPath G level root ys last V → ys.map Prod.fst = tcs →
      discreteAt V.ptn last n = true → Label.ofArray? n V.lab = some v →
      G.relabel u.perm = G.relabel v.perm := by
  induction tcs with
  | nil =>
    intro level last root U V xs ys u v hr hshape hU hx hdU hu hV hy hdV hv
    have hx' : xs = [] := by cases xs <;> simp_all
    have hy' : ys = [] := by cases ys <;> simp_all
    subst xs
    subst ys
    cases hU
    cases hV
    rw [hu] at hv
    have he := Option.some.inj hv
    rw [he]
  | cons tc tcs ih =>
    intro level last root U V xs ys u v hr hshape hU hx hdU hu hV hy hdV hv
    cases hU with
    | refl => simp at hx
    | @step level last root U xs tcU lenU a scratch hcU hbU hnU ha hs tailU =>
      cases hV with
      | refl => simp at hy
      | @step _ _ _ V ys tcV lenV b other hcV hbV hnV hb ht tailV =>
        have hx' : tcU = tc ∧ xs.map Prod.fst = tcs := by simpa only [List.map_cons, List.cons.injEq] using hx
        have hy' : tcV = tc ∧ ys.map Prod.fst = tcs := by simpa only [List.map_cons, List.cons.injEq] using hy
        rcases hx' with ⟨rfl, hx'⟩
        rcases hy' with ⟨rfl, hy'⟩
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
        have hreadyLeaf := tailU.ready hreadyU
        have hreadyW := hW.ready hreadyV
        have hdiscW : discreteAt W.ptn last n = true := by rw [he.ptn]; exact hdU
        have harray := he.discrete hreadyLeaf.spec.node.ptnSize
          (by simpa only [hreadyLeaf.spec.node.ptnSize] using hreadyLeaf.spec.node.ptnEnd)
          hreadyLeaf.spec.node.labSize hreadyW.spec.node.labSize hdU
        have hw : Label.ofArray? n W.lab = some (⟨p.comp u.perm⟩ : Label n) := by
          rw [harray]
          exact SpecLeaf.parse_map p hreadyLeaf.spec.label hu
        have hgraph := ih hreadyV (hr.child_shape hcV hbV hnV hb other ht hshape)
          hW (hz.trans hx') hdiscW hw tailV hy' hdV hv
        have hsame : G.relabel (p.comp u.perm) = G.relabel u.perm := by
          apply Hex.SparseGraph.ext
          intro i j
          simp only [Hex.SparseGraph.adj_relabel, Perm.get_comp]
          exact hiso _ _
        exact hsame.symm.trans hgraph

end Hex.GraphIso.Nauty.Sparse.DescPath
