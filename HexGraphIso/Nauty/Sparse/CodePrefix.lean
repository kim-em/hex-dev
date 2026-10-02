/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CheapTarget
public import HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.Selection

public section

namespace Hex.GraphIso.Nauty.Sparse.CodePath

/-- Below a cheap-shaped node, following a prefix of a saved descent's
targets gives its exact refinement code at the reached depth. Offsets,
native row orders and bounded scratch contents may differ. -/
theorem code_prefix {G : Hex.SparseGraph n} {base last level : Nat}
    {root leaf current : RefineSt n} {path xs : List (Nat × Nat)} {codes : List Nat}
    (h : CodePath G base root path last leaf codes)
    (hr : RefineSt.Ready G base root) (hshape : NodeShape n base root.ptn)
    (hp : DescPath G base root xs level current)
    (hprefix : xs.map Prod.fst <+: path.map Prod.fst) :
    current.longcode = codes[xs.length]! := by
  induction h generalizing level current xs with
  | refl base root =>
    have hx : xs = [] := List.map_eq_nil_iff.mp (List.prefix_nil.mp hprefix)
    subst xs
    cases hp
    rfl
  | @step base last root leaf path codes tc len a scratch hc hb hn ha hs tail ih =>
    cases hp with
    | refl => rfl
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
      have hcode := ih hready (hr.child_shape hc hb hn ha scratch hs hshape) hW hprefixW
      have hlength : zs.length = xs.length := by
        simpa only [List.length_map] using congrArg List.length hz
      rw [hlength] at hcode
      simpa only [List.length_cons, List.getElem!_cons_succ] using he.code.trans hcode

end Hex.GraphIso.Nauty.Sparse.CodePath

namespace Hex.GraphIso.Nauty.Sparse

/-- The exact code reached along stored targets below a cheap ancestor
is the code the native first descent wrote at that depth. -/
theorem FirstRef.code {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n} {xs : List (Nat × Nat)}
    (h : FirstRef G tcLevel base root st) (hdepth : level ≤ h.last)
    (hr : RefineSt.Ready G base root) (hshape : NodeShape n base root.ptn)
    (hp : DescPath G base root xs level current)
    (ht : Targets st.firsttc base (xs.map Prod.fst)) :
    current.longcode = st.firstcode[level]! := by
  have hprefix : xs.map Prod.fst <+: h.path.map Prod.fst := by
    apply ht.prefix h.targets
    have := hp.length
    have := h.trace.descent.length
    simp only [List.length_map]
    omega
  have hi : xs.length < h.codes.length := by
    have hb := List.IsPrefix.length_le hprefix
    rw [List.length_map, List.length_map] at hb
    rw [h.trace.length]
    omega
  have he := h.trace.code_prefix hr hshape hp hprefix
  rw [hp.length, h.stored xs.length hi]
  exact he

end Hex.GraphIso.Nauty.Sparse
