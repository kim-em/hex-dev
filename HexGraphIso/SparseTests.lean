/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexGraph
import HexGraphIso.Sparse
import HexGraphIso.SparseKernelTests
import HexGraphIso.SparseCertTests
import HexGraphIso.SparseTacticTests
import HexGraphIso.SparseLimitTests
meta import HexGraph.Sparse
meta import HexGraph.Sparse.Build
meta import HexGraph.Sparse.Relabel
meta import HexGraphIso.Sparse.Run
meta import HexGraphIso.Sparse.Ops
meta import HexGraphIso.Nauty.Sparse.Search
meta import HexGraphIso.Nauty.Sparse.Sort
meta import HexGraphIso.Sparse.Iso
meta import HexGraphIso.Sparse.Kernel
meta import HexGraphIso.Sparse.Uncolored
meta import HexGraphIso.Sparse.UncoloredOps
meta import HexGraphIso.Sparse.Autos
meta import HexGraphIso.Sparse.UncoloredAutos
meta import HexGraphIso.Nauty.Sparse.Key
meta import HexPermGroup.Perm

open Hex

-- The linear checked constructor must reject duplicate images, including
-- a repeated final image after an otherwise valid prefix.
#guard (Perm.check (n := 0) #v[]).isSome
#guard (Perm.check (n := 4) #v[2, 0, 3, 1]).isSome
#guard (Perm.check (n := 4) #v[2, 0, 3, 2]).isNone
#guard (Perm.check (n := 4) #v[0, 0, 0, 0]).isNone

private def path : SparseGraph 4 := SparseGraph.ofEdges [(0, 1), (1, 2), (2, 3)]

#guard path.offsets == #[0, 1, 3, 5, 6]
#guard path.neighbors.map Fin.val == #[1, 0, 2, 1, 3, 2]
#guard (List.finRange 4).map path.degree == [1, 2, 2, 1]
#guard (List.finRange 4).map (fun i => (path.nbrs i).map Fin.val) ==
  [#[1], #[0, 2], #[1, 3], #[2]]
#guard SparseGraph.ofEdges? 4 [(0, 0)] == none
#guard SparseGraph.ofEdges? 4 [(0, 4)] == none
#guard SparseGraph.ofEdges? 4 [(0, 1), (2, 1), (2, 3), (1, 0), (1, 2)] == some path
#guard SparseGraph.ofEdges? 0 [] == some (SparseGraph.empty 0)
#guard SparseGraph.ofEdges? 0 [(0, 0)] == none
#guard (SparseGraph.empty 0).offsets == #[0]
#guard (SparseGraph.empty 4).offsets == #[0, 0, 0, 0, 0]
#guard (SparseGraph.empty 4).neighbors.isEmpty
#guard path.edges.map (fun (i, j) => (i.val, j.val)) == [(0, 1), (1, 2), (2, 3)]
#guard SparseGraph.ofEdges [(0, 0), (0, 1), (1, 0), (1, 2), (2, 3)] == path

example : path.toDense.toSparse = path := SparseGraph.toSparse_toDense path
example : path.toDense = Graph.ofEdges [(0, 1), (1, 2), (2, 3)] :=
  SparseGraph.toDense_ofEdges _

private def rotate : Perm 4 := Perm.ofFn (fun i => ⟨(i.val + 1) % 4, by omega⟩)
  (by intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv; omega)
  (by intro i; refine ⟨⟨(i.val + 3) % 4, by omega⟩, ?_⟩; apply Fin.ext; dsimp; omega)

#guard (path.relabel rotate).edges.map (fun (i, j) => (i.val, j.val)) ==
  [(0, 1), (0, 3), (1, 2)]
example : (path.relabel rotate).relabel rotate.inv = path := by
  rw [SparseGraph.relabel_relabel, Perm.comp_inv_self, SparseGraph.relabel_id]

open Hex.GraphIso

-- Pinned C sparse nauty result. Dense nauty returns a different label.
private def matching : Sparse.Colored 4 1 :=
  ⟨SparseGraph.ofEdges [(0, 3), (1, 2)], Coloring.trivial 4⟩

private def matchingResult := Nauty.Sparse.runColored matching

#guard matchingResult.canonlab == #[0, 1, 2, 3]
#guard matchingResult.genTrace == #[#[0, 2, 1, 3], #[1, 0, 3, 2]]
#guard matchingResult.orbits == #[0, 0, 0, 0]
#guard matchingResult.order == 8
#guard [matchingResult.numorbits, matchingResult.numgenerators, matchingResult.numnodes,
  matchingResult.numbadleaves, matchingResult.maxlevel, matchingResult.tctotal,
  matchingResult.canupdates] == [1, 2, 6, 0, 3, 8, 1]
#guard (Nauty.Sparse.searchResult? matching).map (·.form.graph) == some matching.graph

-- This partition-free entry must finish with one node and no array accesses.
private def emptyResult := Nauty.Sparse.run
  (Nauty.Sparse.Graph.ofGraph (SparseGraph.empty 0)) #[] []
#guard emptyResult.canonlab.isEmpty && emptyResult.numnodes == 1 && emptyResult.order == 1

-- Pinned equal-key permutation from SORT_OF_SORT = 3, above the insertion cutoff.
#guard Nauty.Sparse.Sort.indirect (Array.range 12) #[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] 0 12 ==
  #[3, 7, 1, 9, 5, 11, 0, 2, 4, 6, 8, 10]

private def pathColored : Sparse.Colored 4 1 := ⟨path, Coloring.trivial 4⟩

-- A forward transporter is the inverse of the new-to-old labelling.
#guard Sparse.checkIso pathColored (pathColored.relabel rotate.toLabel) rotate
#guard !Sparse.checkIso pathColored (pathColored.relabel rotate.toLabel) rotate.inv
private def emptyColored : Sparse.Colored 0 0 :=
  ⟨SparseGraph.empty 0, ⟨#v[], fun c => Fin.elim0 c⟩⟩
#guard Sparse.checkIso emptyColored emptyColored (Perm.id 0)

-- Total extraction retains the pinned label, handles zero colours, and
-- composes labels in the forward transporter direction.
#guard (Sparse.label matching).toArray == #[0, 1, 2, 3]
#guard (Sparse.canonicalize emptyColored).form == emptyColored
#guard (Sparse.label emptyColored).toArray.isEmpty
#guard Sparse.isIso pathColored (pathColored.relabel rotate.toLabel)
#guard !Sparse.isIso pathColored matching
#guard ((Sparse.findIso pathColored (pathColored.relabel rotate.toLabel)).map
  (Sparse.checkIso pathColored (pathColored.relabel rotate.toLabel))).getD false

-- Bare wrappers use zero colours at order zero and preserve transporter
-- direction on a nontrivial relabelling. No positivity witness is needed.
#guard (SparseGraph.canonicalize (SparseGraph.empty 0)).form == SparseGraph.empty 0
#guard (SparseGraph.label (SparseGraph.empty 0)).toArray.isEmpty
#guard SparseGraph.isIso (SparseGraph.empty 0) (SparseGraph.empty 0)
#guard (SparseGraph.canon (SparseGraph.empty 1)) == SparseGraph.empty 1
#guard (SparseGraph.canon matching.graph) == matching.graph
#guard !SparseGraph.isIso path matching.graph
#guard ((SparseGraph.findIso path (path.relabel rotate)).map
  (SparseGraph.checkIso path (path.relabel rotate))).getD false

-- Sparse row order prioritizes degree, then the first differing neighbour.
#guard Nauty.Sparse.rowCmp (n := 4) [3] [0, 1] == .gt
#guard Nauty.Sparse.rowCmp (n := 4) [0, 3] [1, 2] == .gt
#guard Nauty.Sparse.rowCmp (n := 0) [] [] == .eq

example (x y : Array Nat) (start len : Nat) (h : start + len ≤ x.size) :
    (Nauty.Sparse.Sort.indirect x y start len).toList.Perm x.toList :=
  Nauty.Sparse.Sort.indirect_perm x y start len h

example (x y : Array Nat) (start len : Nat) (h : start + len ≤ x.size) :
    Nauty.Sparse.Sort.Sorted (Nauty.Sparse.Sort.insertion x y start len) y start len :=
  Nauty.Sparse.Sort.insertion_sorted x y start len h

example (x y : Array Nat) (start len : Nat) (h : start + len ≤ x.size) :
    Nauty.Sparse.Sort.Sorted (Nauty.Sparse.Sort.indirect x y start len) y start len :=
  Nauty.Sparse.Sort.indirect_sorted x y start len h

example (G : SparseGraph n) (root : Fin n) :
    Nauty.Sparse.Distances G root (Nauty.Sparse.distvals (.ofGraph G) root.val) :=
  Nauty.Sparse.distvals_correct G root

example (G : SparseGraph n) (p : Perm n) (root v : Fin n) :
    (Nauty.Sparse.distvals (.ofGraph (G.relabel p)) root.val)[v.val]! =
      (Nauty.Sparse.distvals (.ofGraph G) (p.get root).val)[(p.get v).val]! :=
  Nauty.Sparse.distvals_relabel G p root v

-- The star fills the queue before the leaves' rows are processed.
#guard Nauty.Sparse.distvals (.ofGraph (SparseGraph.ofEdges (n := 5)
  [(0, 1), (0, 2), (0, 3), (0, 4)])) 0 == #[0, 1, 1, 1, 1]
-- Isolated vertices keep the unreachable sentinel after queue exhaustion.
#guard Nauty.Sparse.distvals (.ofGraph (SparseGraph.ofEdges (n := 6)
  [(0, 1), (1, 2), (2, 3)])) 0 == #[0, 1, 2, 3, 6, 6]

example (x y : Array Nat) (start len : Nat) (h : start + len ≤ x.size) :
    ((Nauty.Sparse.Sort.indirect x y start len).extract start (start + len)).toList.Perm
      (x.extract start (start + len)).toList := Nauty.Sparse.Sort.indirect_segment x y start len h

example (x y : Array Nat) (start len q : Nat) (h : start + len ≤ x.size)
    (hq : q < start ∨ start + len ≤ q) :
    (Nauty.Sparse.Sort.indirect x y start len)[q]! = x[q]! :=
  Nauty.Sparse.Sort.indirect_outside x y start len q h hq

-- Installation and subsequent suffix updates use the same checked label
-- contract. Neither theorem requires sorted working canonical rows.
example (G : SparseGraph n) (lab : Array Nat) (l : Label n)
    (hl : Label.ofArray? n lab = some l) :
    (Nauty.Sparse.updatecan (.ofGraph G) (Nauty.Sparse.Graph.ofGraph G).blank lab 0).Prefix
      (G.relabel l.perm) n := Nauty.Sparse.updatecan_blank G lab l hl

example (G : SparseGraph n) (R : Nauty.Sparse.Rows n) (lab : Array Nat) (l : Label n)
    (same : Nat) (hl : Label.ofArray? n lab = some l) (hR : R.Prefix (G.relabel l.perm) same) :
    (Nauty.Sparse.updatecan (.ofGraph G) R lab same).Prefix (G.relabel l.perm) n :=
  Nauty.Sparse.updatecan_relabel G R lab l same hl hR

example (G H : Sparse.Colored n k) (p : Perm n) (h : Sparse.checkIso G H p = true) :
  Sparse.IsIso G H p := (Sparse.checkIso_iff ..).mp h

example (G H : SparseGraph n) (R : Nauty.Sparse.Rows n) (lab : Array Nat)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (hR : R.Prefix H n) :
    (Nauty.Sparse.testcanlab (.ofGraph G) R lab).1 =
      Nauty.ordInt (Nauty.Sparse.graphCmp (G.relabel l.perm) H) :=
  Nauty.Sparse.testcanlab_fst G H R lab l hl hR

example (G H : SparseGraph n) (R : Nauty.Sparse.Rows n) (lab : Array Nat)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (hR : R.Prefix H n) :
    (Nauty.Sparse.testcanlab (.ofGraph G) R lab).1 = 0 ↔ G.relabel l.perm = H :=
  Nauty.Sparse.testcanlab_eq_zero G H R lab l hl hR

example (G : SparseGraph n) (R : Nauty.Sparse.Rows n) (lab : Array Nat)
    (l c : Label n) (hl : Label.ofArray? n lab = some l)
    (hR : R.Prefix (G.relabel c.perm) n) :
    (Nauty.Sparse.updatecan (.ofGraph G) R lab
      (Nauty.Sparse.testcanlab (.ofGraph G) R lab).2).Prefix (G.relabel l.perm) n :=
  Nauty.Sparse.testcanlab_update G R lab l c hl hR

example (G : SparseGraph n) (p : Perm n) (raw : Array Nat)
    (hp : ∀ i : Fin n, raw[i.val]! = (p.get i).val)
    (h : Nauty.Sparse.isautom (.ofGraph G) raw = true) :
    ∀ i j, G.adj (p.get i) (p.get j) = G.adj i j :=
  (Nauty.Sparse.isautom_iff G p raw hp).mp h

example (lab ptn starts ends : Array Nat) (level : Nat) (l : Label n)
    (hl : Label.ofArray? n lab = some l) (hp : ptn.size = n) (hc : ptn[n - 1]! ≤ level)
    (hs : starts.size = n) (he : ends.size = n) :
    Nauty.Sparse.Index.Valid n lab ptn level
      (Nauty.Sparse.indexCells n lab ptn level starts ends).1
      (Nauty.Sparse.indexCells n lab ptn level starts ends).2 :=
  Nauty.Sparse.indexCells_label lab ptn starts ends level l hl hp hc hs he

example (G : SparseGraph n) (lab ptn : Array Nat) (level : Nat)
    (s t : Nauty.Sparse.Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hp : ptn.size = n) (hc : ptn[n - 1]! ≤ level)
    (hs : Nauty.Sparse.Index.Valid n lab ptn level s.cellstart s.cellend) (hss : s.hits.size = n)
    (ht : Nauty.Sparse.Index.Valid n lab ptn level t.cellstart t.cellend) (hts : t.hits.size = n) :
    (Nauty.Sparse.bestcellCached (.ofGraph G) lab s).1 =
      (Nauty.Sparse.bestcellCached (.ofGraph G) lab t).1 :=
  Nauty.Sparse.bestcellCached_congr G lab ptn level s t l hl hp hc hs hss ht hts

example (G : SparseGraph n) (lab ptn : Array Nat) (level : Nat)
    (hint : Int) (s : Nauty.Sparse.Scratch) (l : Label n)
    (hl : Label.ofArray? n lab = some l) (hp : ptn.size = n) (hc : ptn[n - 1]! ≤ level)
    (hs : Nauty.Sparse.Scratch.Valid n lab ptn level s)
    (hne : Nauty.Sparse.Target.nontrivial (Nauty.cells ptn level n) ≠ []) :
    let out := Nauty.Sparse.maketargetCached (.ofGraph G) lab ptn level 100 hint s
    (out.1, out.2.1, out.2.2.1) = Nauty.Sparse.maketargetcell (.ofGraph G) lab ptn level 100 hint :=
  Nauty.Sparse.maketargetCached_eq G lab ptn level 100 hint s l hl hp hc hs hne

example (G : SparseGraph n) (lab ptn : Array Nat) (level numcells : Nat)
    (active : Nauty.VSet n) (scratch : Nauty.Sparse.Scratch) (ha : active.card ≤ numcells) :
    let out := Nauty.Sparse.refineWith (.ofGraph G) level lab ptn active numcells scratch
    out.queue.isEmpty = true ∨ n ≤ out.numcells :=
  Nauty.Sparse.refineWith_saturated (.ofGraph G) level lab ptn active numcells scratch ha

example (level first : Nat) (distance : Bool) (s : Nauty.Sparse.RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (hc : Nauty.IsCell s.ptn level first (s.cellend[first]! + 1 - first)) :
    Nauty.cellsPerm s.ptn level (Nauty.Sparse.splitCounts level first distance s).lab s.lab :=
  Nauty.Sparse.splitCounts_cells level first distance s hf hb hc

example (level first : Nat) (distance : Bool) (s : Nauty.Sparse.RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (hk : s.hits[s.lab[first]!]! ≤ n + 1) :
    Nauty.Sparse.Sort.Sorted (Nauty.Sparse.splitCounts level first distance s).lab s.hits first
      (s.cellend[first]! + 1 - first) :=
  Nauty.Sparse.splitCounts_sorted level first distance s hf hb (by omega)

-- Reusing stamps and skipping the fixed centre still checks both incident edges.
#guard Nauty.Sparse.isautom (.ofGraph (SparseGraph.ofEdges (n := 3) [(0, 1), (1, 2)]))
  #[2, 1, 0]
#guard !Nauty.Sparse.isautom (.ofGraph (SparseGraph.ofEdges (n := 3) [(0, 1), (1, 2)]))
  #[1, 0, 2]

-- Bucketing preserves vertex order inside each ordered colour class.
#guard Nauty.Sparse.initialPartition 7 3 #[0, 1, 2, 0, 1, 2, 0] ==
  (#[0, 3, 6, 1, 4, 2, 5], [2, 4, 6])
example (G : Sparse.Colored n k) :
    (Nauty.Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val).1.toList.Perm
      (List.range n) := Nauty.Sparse.initialPartition_perm G
example (G : Sparse.Colored n k) :
    (Nauty.Sparse.initialPartitionWith n k G.coloring.cells.toArray Fin.val).2.length = k :=
  Nauty.Sparse.initialPartition_count G

private def cycle3 : Perm 3 := Perm.ofFn (fun i => ⟨(i.val + 1) % 3, by omega⟩)
  (by intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv; omega)
  (by intro i; refine ⟨⟨(i.val + 2) % 3, by omega⟩, ?_⟩; apply Fin.ext; dsimp; omega)

#guard !Sparse.Kernel.checkIso 3 [[1], [0], []] [[], [2], [1]]
  [0, 0, 0] [0, 0, 0] [0, 1, 2]
#guard !Sparse.Kernel.checkIso 3 [[1], [0], []] [[], [2], [1]]
  [0, 0, 0] [0, 1, 0] [1, 2, 0]
#guard !Sparse.Kernel.checkIso 3 [[1], [0], []] [[], [2, 2], [1]]
  [0, 0, 0] [0, 0, 0] [1, 2, 0]
#guard Sparse.Kernel.checkIso 0 [] [] [] [] []
#guard SparseGraph.checkIso (SparseGraph.empty 0) (SparseGraph.empty 0) (Perm.id 0)

private def differentlyColored : Sparse.Colored 3 2 :=
  ⟨SparseGraph.ofEdges [(0, 1)], Coloring.mod 3 2⟩
#guard !Sparse.checkIso differentlyColored differentlyColored cycle3

-- Public automorphism results retain the native single-traversal data.
#guard let r := path.autos
  r.orbits == #[0, 1, 1, 0] && r.numOrbits == 2 && r.order == 2 &&
    r.gens.all (SparseGraph.checkIso path path)
#guard let r := (SparseGraph.empty 0).autos
  r.gens.isEmpty && r.orbits.isEmpty && r.numOrbits == 0 && r.order == 1
#guard let r := (SparseGraph.empty 5).autos
  r.orbits == #[0, 0, 0, 0, 0] && r.numOrbits == 1 && r.order == 120
#guard let r := Sparse.autos differentlyColored
  r.orbits == #[0, 1, 2] && r.numOrbits == 3 && r.order == 1
