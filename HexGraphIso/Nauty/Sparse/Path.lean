/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefinedNode
public import HexGraphIso.Nauty.SmallCell.Monotone

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A descent through literal native child calls. Each step records its
target, selected offset and actual bounded scratch argument; no fresh-cache
substitution or dense refinement appears in the relation. -/
inductive DescPath (G : Hex.SparseGraph n) :
    Nat → RefineSt n → List (Nat × Nat) → Nat → RefineSt n → Prop where
  | refl (level : Nat) (st : RefineSt n) : DescPath G level st [] level st
  | step {level last : Nat} {st leaf : RefineSt n} {path : List (Nat × Nat)}
      (tc len o : Nat) (scratch : Scratch)
      (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
      (hs : Scratch.Bounded n scratch)
      (tail : DescPath G (level + 1)
        (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) path last leaf) :
      DescPath G level st ((tc, o) :: path) last leaf

namespace RefineSt.Ready

/-- The precise cached child call preserves the shape supplied by a cheap
ancestor: individualization and native refinement only add boundaries. -/
theorem child_shape {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) {tc len o : Nat}
    (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (scratch : Scratch) (hs : Scratch.Bounded n scratch) (hshape : NodeShape n level s.ptn) :
    NodeShape n (level + 1) (s.child (.ofGraph G) level tc s.lab[tc + o]! scratch).ptn := by
  have ht := (h.child hc hb hn ho scratch hs).spec.node.ptnSize
  have hsplit := (Boundary.refl (level + 1) s.ptn).set tc
  let b := breakout n s.lab s.ptn (level + 1) tc s.lab[tc + o]!
  have href := refineWith_boundary (.ofGraph G) (level + 1) b.1 b.2.1 b.2.2 (s.numcells + 1) scratch
  have hg : ∀ q : Nat, s.ptn[q]! ≤ level →
      (s.child (.ofGraph G) level tc s.lab[tc + o]! scratch).ptn[q]! ≤ level + 1 := by
    intro q hq
    exact href.closed (hsplit.closed (by omega))
  exact hshape.mono h.spec.node.ptnSize ht
    (by simpa only [h.spec.node.ptnSize] using h.spec.node.ptnEnd) hg

end RefineSt.Ready

namespace DescPath

variable {G : Hex.SparseGraph n} {base last : Nat} {root leaf : RefineSt n} {path : List (Nat × Nat)}

theorem length (h : DescPath G base root path last leaf) : last = base + path.length := by
  induction h with
  | refl => simp
  | step tc len o scratch hc hb hn ho hs tail ih => simp only [List.length_cons]; omega

theorem ready (h : DescPath G base root path last leaf) (hr : RefineSt.Ready G base root) :
    RefineSt.Ready G last leaf := by
  induction h with
  | refl => exact hr
  | step tc len o scratch hc hb hn ho hs tail ih =>
    exact ih (hr.child hc hb hn ho scratch hs)

theorem shape (h : DescPath G base root path last leaf) (hr : RefineSt.Ready G base root)
    (hshape : NodeShape n base root.ptn) : NodeShape n last leaf.ptn := by
  induction h with
  | refl => exact hshape
  | step tc len o scratch hc hb hn ho hs tail ih =>
    exact ih (hr.child hc hb hn ho scratch hs) (hr.child_shape hc hb hn ho scratch hs hshape)

theorem append {middle : RefineSt n} {level : Nat} {xs ys : List (Nat × Nat)}
    (h : DescPath G base root xs level middle) (h' : DescPath G level middle ys last leaf) :
    DescPath G base root (xs ++ ys) last leaf := by
  induction h with
  | refl => exact h'
  | step tc len o scratch hc hb hn ho hs tail ih =>
    exact .step tc len o scratch hc hb hn ho hs (ih h')

end DescPath
end Hex.GraphIso.Nauty.Sparse
