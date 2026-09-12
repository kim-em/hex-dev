/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Children
public import HexGraphIso.Nauty.Sparse.Cert.Sound

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- Sparse replay with checked references to earlier siblings. Every ordinary
record recomputes its refinement and target; references reuse only justified
attainment flags, after checking the full child-partition automorphism. -/
@[expose] def checkNode (G : Hex.SparseGraph n) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → VSet n → Nat → CertNode → Key n → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, B =>
    match cert with
    | .node children =>
      let r := refine (.ofGraph G) level lab ptn active numcells
      match B.codes with
      | [] => none
      | b :: bs =>
        if r.longcode = b ∧ discreteAt r.ptn level n = false then
          let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
          if children.length = t.2.2 then
            checkChildren G level r.lab r.ptn t.1 (fun o c =>
              let child := breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
              checkNode G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
                (r.numcells + 1) c ⟨bs, B.graph⟩) children
          else none
        else none
    | _ => Sparse.checkNode G tcLevel (fuel + 1) level lab ptn active numcells cert B
  termination_by structural fuel => fuel

/-- Accepted compact replay bounds every actual subtree leaf and records
attainment exactly. The tree invariants are preserved by the literal native
refinement and individualization operations. -/
theorem checkNode_valid {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} {cert : CertNode} {B : Key n} {a : Bool}
    (hp : SpecNode G level lab ptn active numcells)
    (h : checkNode G tcLevel fuel level lab ptn active numcells cert B = some a) :
    Replay.Valid G B (specLeaves G tcLevel fuel level lab ptn active numcells) a := by
  induction fuel generalizing level lab ptn active numcells cert B a with
  | zero => simp [checkNode] at h
  | succ fuel ih =>
    cases cert with
    | leaf =>
      exact Sparse.checkNode_valid (cert := .leaf) (by simpa only [checkNode] using h)
    | codePrune =>
      exact Sparse.checkNode_valid (cert := .codePrune) (by simpa only [checkNode] using h)
    | autom earlier images =>
      exact Sparse.checkNode_valid (cert := .autom earlier images) (by simpa only [checkNode] using h)
    | node children =>
      let r := refine (.ofGraph G) level lab ptn active numcells
      have hr : SpecNode G level r.lab r.ptn r.active r.numcells := hp.refined.1
      have heq : Equitable (Graph.context G) level r.lab r.ptn := hp.refined.2
      cases B with
      | mk codes H =>
        cases codes with
        | nil => simp [checkNode] at h
        | cons b bs =>
          simp only [checkNode] at h
          split at h
          · rename_i hd
            split at h
            · rename_i hlen
              have hcount : bcount r.ptn level n < n := by
                have hb := bcount_le r.ptn level n
                have hn : bcount r.ptn level n ≠ n := fun he => by
                  have ht := (discreteAt_iff_bcount hr.node.ptnSize.symm hr.node.ptnEnd).mpr he
                  rw [hd.2] at ht
                  cases ht
                omega
              let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
              obtain ⟨ht, hn, hb⟩ := maketargetcell_valid G r.lab r.ptn level tcLevel (-1)
                hr.label hr.node.ptnSize (by simpa only [hr.node.ptnSize] using hr.node.ptnEnd) hcount
              have hv := checkChildren_valid (tcLevel := tcLevel) (fuel := fuel)
                hr heq (by simpa only [hlen] using ht) (by simpa only [hlen] using hb)
                (by simpa only [hlen] using hn)
                (fun o c a ho hc => ih (hr.child heq ht hb hn (by simpa only [hlen] using ho)) hc) h
              rw [hlen] at hv
              have hv' := hv.prepend r.longcode
              rw [specLeaves]
              simp only [hd.2, Bool.false_eq_true, ite_false]
              simpa only [List.map_flatMap, prefixKey, List.singleton_append, r, hd.1] using hv'
            · cases h
          · cases h

/-- Compact canonical-key replay from the actual ordered-colour initializer.
An automorphism reference is invalid at the root and on the empty graph. -/
@[expose] def checkKey (G : GraphIso.Sparse.Colored n k) (cert : CertNode) (B : Key n) : Bool :=
  if n = 0 then Sparse.checkKey G cert B else
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    checkNode G.graph 100 (n + 2) 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length cert B == some true

theorem checkKey_sound {G : GraphIso.Sparse.Colored n k} {cert : CertNode} {B : Key n}
    (h : checkKey G cert B = true) : canonSpecKey G = B := by
  by_cases hn : n = 0
  · simp only [checkKey, hn, ite_true] at h
    exact Sparse.checkKey_sound h
  · simp only [checkKey, hn, ite_false, beq_iff_eq] at h
    have hv := checkNode_valid (SpecNode.initial G (by omega)) h
    have hr : Replay.Valid G.graph B (rootLeaves G) true := by
      simpa only [rootLeaves, hn, ite_false] using hv
    obtain ⟨l, hl, he⟩ := hr.attains.mp rfl
    rw [← he]
    exact canonSpecKey_eq G hl (by simpa only [he] using hr.bound)

end Hex.GraphIso.Nauty.Sparse.Compact
