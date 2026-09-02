/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Iso
public import HexGraphIso.Nauty.CanonForm

public section

/-!
A kernel-priced positive-path checker. The `graph_iso` tactic proves
`Isomorphic G H` by tying each side to a literal — one sequential
kernel evaluation per graph — and validating the transporter entirely
on those literals. `checkIsoLit` walks row-chunked literal lists with
bare-`Nat`-match accessors, so the kernel pays a short list walk per
probe instead of per-probe flat `Array` indexing into the adjacency
matrix, whose walk length grows with the flat index and made positive
replays quartic in `n`.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-- Literal list access priced for kernel reduction: one bare match
per step, no bounds proofs, no `Array` wrapper. -/
@[expose] def atD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: as, i + 1, d => atD as i d

theorem atD_eq_getElem {α : Type} {d : α} :
    ∀ (l : List α) (i : Nat) (h : i < l.length), atD l i d = l[i]
  | _ :: _, 0, _ => rfl
  | _ :: as, i + 1, h => by
    rw [atD, List.getElem_cons_succ]
    exact atD_eq_getElem as i (by simpa using h)

/-- The flat matrix list cut into `r` rows of `m` entries. -/
@[expose] def chunkRows : Nat → Nat → List Bool → List (List Bool)
  | 0, _, _ => []
  | r + 1, m, l => l.take m :: chunkRows r m (l.drop m)

theorem atD_chunkRows (m : Nat) :
    ∀ (r : Nat) (l : List Bool) (i : Nat), i < r →
      atD (chunkRows r m l) i [] = (l.drop (m * i)).take m
  | r + 1, l, 0, _ => by
    rw [chunkRows, atD, Nat.mul_zero, List.drop_zero]
  | r + 1, l, i + 1, h => by
    rw [chunkRows, atD, atD_chunkRows m r (l.drop m) i (by omega),
      List.drop_drop, Nat.mul_succ, Nat.add_comm (m * i) m]

/-- Validate a forward transporter on literal data: `flatA`/`flatB`
are the flat adjacency lists, `cellsA`/`cellsB` the colour values,
and `pl` the transporter images, all tied back to the graphs by the
hypotheses of `isomorphic_of_checkIsoLit`. -/
@[expose] def checkIsoLit (n : Nat) (flatA flatB : List Bool)
    (cellsA cellsB pl : List Nat) : Bool :=
  let rowsA := chunkRows n n flatA
  let rowsB := chunkRows n n flatB
  ((List.range n).all fun i =>
    atD cellsB (atD pl i 0) 0 == atD cellsA i 0) &&
  (List.range n).all fun i =>
    let rA := atD rowsA i []
    let rB := atD rowsB (atD pl i 0) []
    (List.range n).all fun j =>
      atD rB (atD pl j 0) false == atD rA j false

/-- The flat-index read of a chunked literal is the flat read. -/
theorem atD_chunk_flat {l : List Bool} {i j : Nat}
    (hlen : l.length = n * n) (hi : i < n) (hj : j < n) :
    atD (atD (chunkRows n n l) i []) j false =
      l.getD (n * i + j) false := by
  have hb : n * i + j < l.length := by
    rw [hlen]
    calc n * i + j < n * i + n := by omega
      _ = n * (i + 1) := by rw [Nat.mul_succ]
      _ ≤ n * n := Nat.mul_le_mul_left n hi
  rw [← List.getElem_eq_getD (h := hb), atD_chunkRows n n l i hi]
  have hdl : (l.drop (n * i)).length = n * n - n * i := by
    rw [List.length_drop, hlen]
  have hjt : j < ((l.drop (n * i)).take n).length := by
    rw [List.length_take, hdl]
    have : n * i + n ≤ n * n := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left n hi
    omega
  rw [atD_eq_getElem _ j hjt, List.getElem_take, List.getElem_drop]

/-- The flat-list read of an adjacency matrix is the adjacency test. -/
theorem adj_eq_toList_flat (Gm : Graph n) (i j : Fin n) :
    Gm.adj i j =
      Gm.adjMatrix.data.toList.getD (i.val * n + j.val) false := by
  rw [← List.getElem_eq_getD
    (h := by simp [Matrix.flatIdx_lt i.isLt j.isLt]), Graph.adj]
  show Gm.adjMatrix.data[i.val * n + j.val]'(Matrix.flatIdx_lt i.isLt j.isLt) = _
  simp

/-- Tying equalities plus a literal transporter check prove
isomorphism: the kernel evaluates each graph once — sequentially,
into its literal — and the rest of the replay runs on literals. -/
theorem isomorphic_of_checkIsoLit {G H : Colored n k} {p : Perm n}
    {LA LB : List Bool} {CA CB PL : List Nat}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (hcA : G.coloring.cells.toList.map Fin.val = CA)
    (hcB : H.coloring.cells.toList.map Fin.val = CB)
    (hp : p.vec.toList.map Fin.val = PL)
    (hchk : checkIsoLit n LA LB CA CB PL = true) :
    Isomorphic G H := by
  subst hA hB hcA hcB hp
  simp only [checkIsoLit, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, beq_iff_eq] at hchk
  obtain ⟨hcol, hadj⟩ := hchk
  have hPL : ∀ i : Fin n,
      atD (p.vec.toList.map Fin.val) i.val 0 = (p.get i).val := by
    intro i
    rw [atD_eq_getElem _ i.val (by simp), List.getElem_map,
      Perm.get_toList]
  have hcell : ∀ (c : Vector (Fin k) n) (i : Fin n),
      atD (c.toList.map Fin.val) i.val 0 = c[i].val := by
    intro c i
    rw [atD_eq_getElem _ i.val (by simp), List.getElem_map]
    simp
  have hflat : ∀ (Gm : Graph n) (i j : Fin n),
      atD (atD (chunkRows n n Gm.adjMatrix.data.toList) i.val [])
        j.val false = Gm.adj i j := by
    intro Gm i j
    rw [atD_chunk_flat (by simp) i.isLt j.isLt, adj_eq_toList_flat,
      Nat.mul_comm i.val n]
  refine Isomorphic.intro p (IsIso.mk (fun i => ?_) fun i j => ?_)
  · have h := hcol i.val i.isLt
    rw [hPL i, hcell, hcell] at h
    exact Fin.val_inj.mp h
  · have h := hadj i.val i.isLt j.val j.isLt
    rw [hPL i, hPL j, hflat, hflat] at h
    exact h

/-! # The literal-tie negative route

The negative kernel obligation `checkKey G cert B = true` forces
`rowsOf G`, whose per-entry adjacency probes walk the flat matrix
from the front — the same quartic trap the positive route escaped.
`checkKeyFlat` rebuilds the rows from the tied flat literal instead:
the flat list is cut into rows once, sequentially, and each row
bitset folds over its own short segment. -/

theorem chunkRows_length (m : Nat) :
    ∀ (r : Nat) (l : List Bool), (chunkRows r m l).length = r
  | 0, _ => rfl
  | r + 1, l => by
    rw [chunkRows, List.length_cons, chunkRows_length m r]

private theorem foldl_congr_mem {α β : Type} {f g : α → β → α} :
    ∀ (l : List β), (∀ a b, b ∈ l → f a b = g a b) →
      ∀ (a : α), l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, h, a => by
    rw [List.foldl_cons, List.foldl_cons, h a b List.mem_cons_self]
    exact foldl_congr_mem l
      (fun a' b' hb' => h a' b' (List.mem_cons_of_mem _ hb')) _

/-- Adjacency rows rebuilt from the flat literal, priced for kernel
reduction: the flat list is cut into rows once, and each row bitset
folds over its own short segment instead of probing the flat list. -/
@[expose] def flatRows (nn : Nat) (flat : List Bool) : Array Nat :=
  ((chunkRows nn nn flat).map fun seg =>
    (List.range nn).foldl
      (fun row j => if atD seg j false then Nauty.insert row j else row)
      0).toArray

theorem flatRows_eq_rowsOf (G : Colored n k) :
    flatRows n G.graph.adjMatrix.data.toList = Nauty.rowsOf G := by
  rw [flatRows, Nauty.rowsOf]
  refine congrArg List.toArray (List.ext_getElem ?_ ?_)
  · rw [List.length_map, chunkRows_length, List.length_map,
      List.length_range]
  · intro i h1 h2
    rw [List.length_map, chunkRows_length] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range,
      ← atD_eq_getElem _ i (by rw [chunkRows_length]; exact h1),
      Nauty.rowOf]
    refine foldl_congr_mem _ (fun row j hj => ?_) 0
    have hjn := List.mem_range.mp hj
    rw [dite_eq_left (⟨h1, hjn⟩ : i < n ∧ j < n),
      atD_chunk_flat (by simp) h1 hjn, Nat.mul_comm n i,
      ← adj_eq_toList_flat G.graph ⟨i, h1⟩ ⟨j, hjn⟩]

/-- `Nauty.checkKey` with the adjacency rows rebuilt from a flat
literal: the negative route's kernel obligation, evaluating the tied
literal instead of forcing `rowsOf`. -/
@[expose] def checkKeyFlat (G : Colored n k) (flat : List Bool)
    (cert : Nauty.CertNode) (B : Nauty.Key) : Bool :=
  if n == 0 then
    B.codes == [] && B.rows == []
  else
    Nauty.checkNode { n := n, g := flatRows n flat } 100 B.rows n 1
      (Nauty.initialPartition G).1
      (Nauty.initPtn n (n + 2) (Nauty.initialPartition G).2)
      (Nauty.initActive (Nauty.initialPartition G).2)
      (Nauty.initialPartition G).2.length cert B.codes = some true

theorem checkKeyFlat_eq (G : Colored n k) (cert : Nauty.CertNode)
    (B : Nauty.Key) :
    checkKeyFlat G G.graph.adjMatrix.data.toList cert B =
      Nauty.checkKey G cert B := by
  rw [checkKeyFlat, Nauty.checkKey, flatRows_eq_rowsOf]

/-- Tying equalities plus two flat-literal key certificates with
differing keys prove non-isomorphism: the kernel evaluates each graph
once into its literal, and both replays run on rebuilt literal
rows. -/
theorem not_isomorphic_of_checkKeysLit {G H : Colored n k}
    {certG certH : Nauty.CertNode} {BG BH : Nauty.Key}
    {LA LB : List Bool}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (hG : checkKeyFlat G LA certG BG = true)
    (hH : checkKeyFlat H LB certH BH = true)
    (hd : Nauty.checkDiff BG BH = true) : ¬Isomorphic G H := by
  subst hA hB
  rw [checkKeyFlat_eq] at hG hH
  exact Nauty.not_isomorphic_of_checkKeys hG hH hd

end Hex.GraphIso
