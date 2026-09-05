/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Iso
public import HexGraphIso.Nauty.Cert.CanonForm

public section

/-!
The positive route's kernel checker. `graph_iso` proves `Isomorphic G H`
by reducing each side to a list literal, one kernel evaluation per
graph, then validating the transporter entirely on those literals.
`Kernel.checkIso` reads row-chunked literal lists through bare `Nat`
matches, so the kernel walks one short row per probe instead of
indexing the flat adjacency matrix, whose spine walk grows with the
flat index.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-- Indexed list access built for cheap kernel reduction: one bare match
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

theorem chunkRows_length (m : Nat) :
    ∀ (r : Nat) (l : List Bool), (chunkRows r m l).length = r
  | 0, _ => rfl
  | r + 1, l => by
    rw [chunkRows, List.length_cons, chunkRows_length m r]

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

namespace Kernel

/-- Validate a forward transporter on literal data: `flatA`/`flatB`
are the flat adjacency lists, `cellsA`/`cellsB` the colour values,
and `pl` the transporter images, each identified with the graph it
comes from by a hypothesis of `Kernel.isIso_of_checkIso`. -/
@[expose] def checkIso (n : Nat) (flatA flatB : List Bool)
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

/-- Equalities identifying the graph data with the literals, plus a
literal transporter check, prove that the permutation transports. The
kernel evaluates each graph once, into its literal, and the rest of the
check runs on literals. -/
theorem isIso_of_checkIso {G H : Colored n k} {p : Perm n}
    {LA LB : List Bool} {CA CB PL : List Nat}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (hcA : G.coloring.cells.toList.map Fin.val = CA)
    (hcB : H.coloring.cells.toList.map Fin.val = CB)
    (hp : p.vec.toList.map Fin.val = PL)
    (hchk : checkIso n LA LB CA CB PL = true) :
    IsIso G H p := by
  subst hA hB hcA hcB hp
  simp only [checkIso, Bool.and_eq_true, List.all_eq_true,
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
  refine IsIso.mk (fun i => ?_) fun i j => ?_
  · have h := hcol i.val i.isLt
    rw [hPL i, hcell, hcell] at h
    exact Fin.val_inj.mp h
  · have h := hadj i.val i.isLt j.val j.isLt
    rw [hPL i, hPL j, hflat, hflat] at h
    exact h

/-- Equalities identifying the graph data with the literals, plus a
literal transporter check, prove isomorphism. -/
theorem isomorphic_of_checkIso {G H : Colored n k} {p : Perm n}
    {LA LB : List Bool} {CA CB PL : List Nat}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (hcA : G.coloring.cells.toList.map Fin.val = CA)
    (hcB : H.coloring.cells.toList.map Fin.val = CB)
    (hp : p.vec.toList.map Fin.val = PL)
    (hchk : checkIso n LA LB CA CB PL = true) :
    Isomorphic G H :=
  Isomorphic.intro p (isIso_of_checkIso hA hB hcA hcB hp hchk)

end Kernel

end Hex.GraphIso
