/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Check

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Accepted sparse proof records bound every leaf of the literal native
tree and identify attainment. No correctness assumption about a producer,
cached code, target size, or proposed label enters the theorem. -/
theorem checkNode_valid {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} {cert : CertNode} {B : Key n} {a : Bool}
    (h : checkNode G tcLevel fuel level lab ptn active numcells cert B = some a) :
    Replay.Valid G B (specLeaves G tcLevel fuel level lab ptn active numcells) a := by
  induction fuel generalizing level lab ptn active numcells cert B a with
  | zero => simp [checkNode] at h
  | succ fuel ih =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    cases cert with
    | autom _ _ => simp [checkNode] at h
    | leaf =>
      simp only [checkNode] at h
      split at h
      · rename_i hd
        split at h
        · cases h
        · rename_i l hl
          have hv := Replay.leaf_valid h
          simpa only [specLeaves, hd, ite_true, hl] using hv
      · cases h
    | codePrune =>
      cases B with
      | mk codes H =>
        cases codes with
        | nil => simp [checkNode] at h
        | cons b bs =>
          simp only [checkNode] at h
          split at h
          · rename_i hc
            have ha : a = false := Option.some.inj h.symm
            subst a
            exact Replay.prune_valid hc
          · cases h
    | node children =>
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
              let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
              let leaves := fun o =>
                let child := breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
                specLeaves G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
                  (r.numcells + 1)
              have hv : Replay.Valid G ⟨bs, H⟩
                  (children.zipIdx.flatMap (fun co => leaves co.2)) a :=
                Replay.all_valid (fun co _ _ hc => ih hc) h
              have hidx : children.zipIdx.map Prod.snd = List.range t.2.2 := by
                rw [List.zipIdx_map_snd, hlen, ← List.range_eq_range']
              have he : children.zipIdx.flatMap (fun co => leaves co.2) =
                  (List.range t.2.2).flatMap leaves := by
                rw [← hidx, List.flatMap_map]
              rw [he] at hv
              have hp := hv.prepend r.longcode
              rw [specLeaves]
              simp only [hd.2, Bool.false_eq_true, ite_false]
              simpa only [List.map_flatMap, prefixKey, List.singleton_append,
                leaves, t, r, hd.1] using hp
            · cases h
          · cases h

/-- A checked attaining upper bound is the sparse declarative maximum. -/
theorem checkKey_sound {G : GraphIso.Sparse.Colored n k} {cert : CertNode} {B : Key n}
    (h : checkKey G cert B = true) : canonSpecKey G = B := by
  have hv : Replay.Valid G.graph B (rootLeaves G) true := by
    by_cases hn : n = 0
    · simp only [checkKey, hn, ite_true] at h
      cases cert with
      | leaf =>
        have hr := Replay.leaf_valid (beq_iff_eq.mp h)
        simpa only [rootLeaves, hn, ite_true] using hr
      | codePrune => cases h
      | autom _ _ => cases h
      | node _ => cases h
    · simp only [checkKey, hn, ite_false] at h
      have hr := checkNode_valid (beq_iff_eq.mp h)
      simpa only [rootLeaves, hn, ite_false] using hr
  obtain ⟨l, hl, he⟩ := hv.attains.mp rfl
  rw [← he]
  exact canonSpecKey_eq G hl (by simpa only [he] using hv.bound)

end Hex.GraphIso.Nauty.Sparse
