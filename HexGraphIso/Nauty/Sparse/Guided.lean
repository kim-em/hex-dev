/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Positions
public import HexGraphIso.Nauty.Sparse.CodeTransport
public import HexGraphIso.Nauty.Sparse.CheapPrefix
public import HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.History

public section

namespace Hex.GraphIso.Nauty.Sparse.CodePath

/-- A live first-reference path uses either the native canonical target
or the saved target. Every step still records its actual cached call. -/
@[expose] def Guided (tcLevel : Nat) (store : Array Int) :
    {base last : Nat} → {root leaf : RefineSt n} → {path : List (Nat × Nat)} → {codes : List Nat} →
      CodePath G base root path last leaf codes → Prop
  | _, _, _, _, _, _, .refl _ _ => True
  | _, _, _, _, _, _, @CodePath.step _ _ level _ st _ _ _ tc _ _ _ _ _ _ _ _ tail =>
    (tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1) ∨
      store[level]! = Int.ofNat tc) ∧ tail.Guided tcLevel store

/-- Append one actual cached individualization to a guided history,
retaining all earlier codes and recording the new refinement code. -/
theorem Guided.extend {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {store : Array Int} {root leaf : RefineSt n} {path : List (Nat × Nat)} {codes : List Nat}
    {h : CodePath G base root path level leaf codes} (hg : h.Guided tcLevel store)
    {tc len o : Nat} (hc : IsCell leaf.ptn level tc len) (hb : tc + len ≤ n)
    (hn : 1 < len) (ho : o < len) (scratch : Scratch) (hs : Scratch.Bounded n scratch)
    (hchoice : tc = targetcell (.ofGraph G) leaf.lab leaf.ptn level tcLevel (-1) ∨
      store[level]! = Int.ofNat tc) :
    let next := leaf.child (.ofGraph G) level tc leaf.lab[tc + o]! scratch
    ∃ trace : CodePath G base root (path ++ [(tc, o)]) (level + 1) next (codes ++ [next.longcode]),
      trace.Guided tcLevel store := by
  induction h with
  | refl => exact ⟨.step tc len o scratch hc hb hn ho hs (.refl _ _), hchoice, trivial⟩
  | step first width offset cache hcell hbound hnon ho' hcache tail ih =>
    obtain ⟨trace, ht⟩ := ih hg.2 hc hchoice
    exact ⟨.step first width offset cache hcell hbound hnon ho' hcache trace, hg.1, ht⟩

/-- Matching final labels force equal depths and complete code sequences for a selected reference
and a guided path, even with independent caches and label order within
corresponding cells. Individualized vertices persist at literal positions. -/
theorem guided_codes (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {tcLevel base last₁ last₂ : Nat} {root other first current : RefineSt n}
    {path₁ path₂ : List (Nat × Nat)} {codes₁ codes₂ : List Nat} {store : Array Int}
    (hfirst : CodePath G base root path₁ last₁ first codes₁)
    (hr : RefineSt.Ready G base root) (ht : RefineSt.Ready H base other)
    (he : RefineSt.Equiv (renamingOf p) base root other)
    (hselect : hfirst.Selects tcLevel) (htarget : Targets store base (path₁.map Prod.fst))
    (hcurrent : CodePath H base other path₂ last₂ current codes₂)
    (hguided : hcurrent.Guided tcLevel store)
    (hd₁ : discreteAt first.ptn last₁ n = true) (hd₂ : discreteAt current.ptn last₂ n = true)
    (hlabels : first.lab.map (renamingOf p).toFun = current.lab) :
    last₂ = last₁ ∧ codes₂ = codes₁ := by
  induction hfirst generalizing other last₂ current path₂ codes₂ with
  | refl base root =>
    have hd : discreteAt other.ptn base n = true := by rw [he.ptn]; exact hd₁
    cases hcurrent with
    | refl => exact ⟨rfl, congrArg (fun c : Nat => [c]) he.code.symm⟩
    | step tc len o scratch hc hb hn ho hs tail =>
      have hh := (CodePath.step tc len o scratch hc hb hn ho hs tail).descent.nil_of_discrete ht hd
      cases hh
  | @step base last₁ root first path₁ codes₁ tc len o scratch hc hb hn ho hs tail ih =>
    cases hcurrent with
    | refl =>
      have hd : discreteAt root.ptn base n = true := by rw [← he.ptn]; exact hd₂
      have hn := (CodePath.step tc len o scratch hc hb hn ho hs tail).descent.nil_of_discrete hr hd
      cases hn
    | @step _ last₂ _ current path₂ codes₂ tc₂ len₂ o₂ scratch₂ hc₂ hb₂ hn₂ ho₂ hs₂ tail₂ =>
      have htc : tc₂ = tc := by
        rcases hguided.1 with hspec | hstored
        · exact hspec.trans ((he.target G H p hiso hr ht tcLevel (-1)).trans hselect.1.symm)
        · have hf : store[base]! = Int.ofNat tc := htarget 0 (by simp)
          exact Int.ofNat.inj (hstored.symm.trans hf)
      subst tc₂
      have hlen : len₂ = len := by
        have hc' : IsCell root.ptn base tc len₂ := by rw [← he.ptn]; exact hc₂
        rcases isCell_disjoint_or_eq hc hc' with hh | hh | hh <;> omega
      subst len₂
      have hp₁ := (CodePath.step tc len o scratch hc hb hn ho hs tail).descent.picked hr
      have hp₂ := (CodePath.step tc len o₂ scratch₂ hc₂ hb₂ hn₂ ho₂ hs₂ tail₂).descent.picked ht
      have hf := tail.descent.ready (hr.child hc hb hn ho scratch hs)
      have hv : other.lab[tc + o₂]! = renamingOf p root.lab[tc + o]! := by
        rw [← hp₂, ← hp₁, ← hlabels, getElem!_map_of_lt _ _ (by rw [hf.spec.node.labSize]; omega)]
      obtain ⟨j, hj, hm, hchild⟩ := child_match G H p hiso hr ht he.ptn he.count.symm he.cells
        hc hb hn ho scratch scratch₂ hs hs₂
      have hj' : j = o₂ := by
        have hi := perm_injective ht.spec.label (show tc + j < n by omega)
          (show tc + o₂ < n by omega) (hm.trans hv.symm)
        omega
      subst j
      have htargets : Targets store (base + 1) (path₁.map Prod.fst) := by
        simpa only [List.map_cons, List.drop_succ_cons, List.drop_zero] using htarget.drop 1
      obtain ⟨hdepth, hcodes⟩ := ih (hr.child hc hb hn ho scratch hs) (ht.child hc₂ hb₂ hn₂ ho₂ scratch₂ hs₂)
        hchild hselect.2 htargets tail₂ hguided.2 hd₁ hd₂ hlabels
      exact ⟨hdepth, by simp only [he.code, hcodes]⟩

end Hex.GraphIso.Nauty.Sparse.CodePath
