/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecNode

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A post-refinement native node. The certificate records the actual
active set; equitability justifies the next individualization. -/
structure RefineSt.Ready (G : Hex.SparseGraph n) (level : Nat) (s : RefineSt n) : Prop where
  spec : SpecNode G level s.lab s.ptn s.active s.numcells
  equitable : Equitable (Graph.context G) level s.lab s.ptn

/-- Tree-entry invariants hold for the actual cached refinement as well
as fresh refinement. Incoming scratch may have any proved bounded contents. -/
theorem SpecNode.refineWith {G : Hex.SparseGraph n} {level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n}
    (h : SpecNode G level lab ptn active numcells) (scratch : Scratch)
    (hb : Scratch.Bounded n scratch) :
    RefineSt.Ready G level (Sparse.refineWith (.ofGraph G) level lab ptn active numcells scratch) := by
  have hend : ptn[n - 1]! ≤ level := by simpa only [h.node.ptnSize] using h.node.ptnEnd
  have ht := refineWith_state G level lab ptn active numcells scratch h.label h.node.ptnSize hend h.node.starts hb
  have hcount := refineWith_count G level lab ptn active numcells scratch h.label h.node.ptnSize hend h.node.starts hb h.count
  let st : State n := { (default : State n) with
    lab, ptn, active
    canong := { (default : Storage n) with scratch } }
  have ho := visit_nodeOk G level numcells st h.label h.node hb
  have hmono := bcount_mono (fun q hq => (refineWith_boundary (.ofGraph G) level lab ptn
    active numcells scratch).closed hq) (nn := n)
  have hdepth : level ≤ (Sparse.refineWith (.ofGraph G) level lab ptn active numcells scratch).numcells := by
    have := h.depth
    have := h.count
    omega
  exact ⟨⟨ht.1, ho, hcount, hdepth,
    refineWith_cert G level lab ptn active numcells scratch h.label h.node.ptnSize hend h.node.starts hb h.cert⟩,
    refineWith_equitable G level lab ptn active numcells scratch h.label h.node.ptnSize hend h.node.starts hb h.count h.cert⟩

/-- The exact individualization and cached refinement performed by a
native child call; the supplied scratch is the call's actual storage. -/
@[expose] def RefineSt.child (g : Graph n) (level : Nat) (s : RefineSt n)
    (tc tv : Nat) (scratch : Scratch) : RefineSt n :=
  let b := breakout n s.lab s.ptn (level + 1) tc tv
  refineWith g (level + 1) b.1 b.2.1 b.2.2 (s.numcells + 1) scratch

/-- Every member of a nontrivial cell gives a valid equitable child under
the literal native child operation, independently of bounded scratch. -/
theorem RefineSt.Ready.child {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) {tc len o : Nat}
    (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (scratch : Scratch) (hs : Scratch.Bounded n scratch) :
    RefineSt.Ready G (level + 1) (s.child (.ofGraph G) level tc s.lab[tc + o]! scratch) :=
  (h.spec.child h.equitable hc hb hn ho).refineWith scratch hs

end Hex.GraphIso.Nauty.Sparse
