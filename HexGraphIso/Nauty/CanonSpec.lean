/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search
public import HexGraphIso.Nauty.Equivariance

public section

/-!
The nauty-semantic canonical form as a total specification: the maximal
leaf key of the unpruned individualization-refinement tree.

A leaf key is the chain of refinement codes ending with the sentinel,
followed by the leaf's `g^lab` adjacency rows; keys compare
lexicographically, codes numerically and rows in nauty's row order.
The production search's canonical leaf realizes this maximum:

- a node whose chain is dominated (`compCanon < 0`) can never supply the
  canonical leaf, and those are exactly the nodes where nauty's
  history-dependent `firsttc` hint applies, so the specification's
  target-cell rule is the plain hint-free `targetcell`;
- the sentinel exceeds every real (cleaned) refinement code, which
  reproduces nauty's preference for shallower leaves on equal prefixes
  (`level < canonlevel` forcing `compCanon = 1`);
- children may be enumerated in any order under a maximum; the
  specification enumerates the target cell by position, which makes
  renaming-equivariance pointwise.

The branch guard is structural discreteness of the partition rather than
nauty's `numcells` counter; the two agree on every reachable state, and
the certificate checker replays concrete refinements where discreteness
is directly decidable.
-/

namespace Hex.GraphIso.Nauty

/-- A leaf key of the unpruned search tree: the level codes ending with
the sentinel, then the leaf's adjacency rows. -/
structure Key where
  /-- The refinement codes along the path, ending with the sentinel. -/
  codes : List Nat
  /-- The leaf's `g^lab` rows in nauty's row order. -/
  rows : List Nat
deriving Inhabited

/-- Lexicographic list comparison from an element comparison. -/
@[expose] def listCmp (cmp : Nat → Nat → Ordering) :
    List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmp a b with
    | .eq => listCmp cmp as bs
    | .lt => .lt
    | .gt => .gt

/-- Key order: level codes first, then rows in nauty's row order. -/
@[expose] def keyCmp (k1 k2 : Key) : Ordering :=
  match listCmp compare k1.codes k2.codes with
  | .eq => listCmp rowCmp k1.rows k2.rows
  | .lt => .lt
  | .gt => .gt

/-- The greater key, the first argument winning ties. -/
@[expose] def keyMax (k1 k2 : Key) : Key :=
  if keyCmp k1 k2 = .lt then k2 else k1

/-- The maximum of a list of keys, seeded by an initial key. -/
@[expose] def keysMax (k : Key) : List Key → Key
  | [] => k
  | k' :: rest => keysMax (keyMax k k') rest

/-- Discreteness of the partition at `level`: every cell a singleton. -/
@[expose] def discreteAt (ptn : Array Nat) (level nn : Nat) : Bool :=
  (cells ptn level nn).all fun p => p.1 == p.2

/-- The key of the maximal leaf of the unpruned search tree below one
node. -/
@[expose] def specNode (ctx : Ctx) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → Key
  | 0, _, _, _, _, _ => ⟨[], []⟩
  | fuel + 1, level, lab, ptn, active, numcells =>
    let rs := refine ctx level lab ptn active numcells
    if discreteAt rs.ptn level ctx.n then
      ⟨[rs.longcode, codeSentinel], leafRows ctx rs.lab⟩
    else
      let tcr := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
      let children := (List.range tcr.2.2).map fun o =>
        let br := breakout rs.lab rs.ptn (level + 1) tcr.1 rs.lab[tcr.1 + o]!
        specNode ctx tcLevel fuel (level + 1) br.1 br.2.1 br.2.2
          (numcells + 1)
      match children with
      | [] => ⟨[], []⟩
      | c :: cs =>
        ⟨rs.longcode :: (keysMax c cs).codes, (keysMax c cs).rows⟩

/-- The canonical key of the unpruned nauty search on `n` vertices with
adjacency rows `g` and initial ordered partition `(lab0, cellEnds)`. -/
@[expose] def canonSpec (n : Nat) (g : Array Nat) (lab0 : Array Nat)
    (cellEnds : List Nat) : Key :=
  if n == 0 then
    ⟨[], []⟩
  else
    specNode { n, g } 100 (n + 2) 1 lab0 (initPtn n (n + 2) cellEnds)
      (initActive cellEnds) cellEnds.length

variable {n k : Nat}

/-- The nauty-semantic canonical key of a coloured graph. -/
@[expose] def canonSpecKey (G : Colored n k) : Key :=
  canonSpec n (rowsOf G) (initialPartition G).1 (initialPartition G).2

/-! # Equivariance -/

/-- The unpruned search tree's maximal leaf key is invariant under a
vertex renaming: on the renamed graph with the transported labelling,
every node produces the same key. -/
theorem specNode_map (σ : Renaming n) {ctx ctx' : Ctx}
    (hn : ctx.n = n) (hn' : ctx'.n = n) (hg : RowsMap σ ctx.g ctx'.g)
    (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat) (active numcells : Nat),
      lab.size = n → LabOk lab n → ptn.size = n → active < 2 ^ n →
      ptn[ptn.size - 1]! ≤ level →
      specNode ctx' tcLevel fuel level (lab.map σ.toFun) ptn active
          numcells =
        specNode ctx tcLevel fuel level lab ptn active numcells
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, level, lab, ptn, active, numcells, hsl, hlab, hsp, hact,
      hend => by
    rw [specNode, specNode,
      refine_map σ hn hn' hg level lab ptn active numcells hsl hlab hsp
        hact hend]
    dsimp only
    rw [hn', hn]
    have hst := refine_stOk (ctx := ctx) hn (level := level)
      (numcells := numcells) hsl hlab hsp hact hend
    generalize hR : refine ctx level lab ptn active numcells = R
    rw [hR] at hst
    rcases hdisc : discreteAt R.ptn level n with _ | _
    · simp only [Bool.false_eq_true, if_false]
      obtain ⟨p, hpm, hpne, hptc⟩ := targetcell_nontrivial
        (lab := R.lab) (tcLevel := tcLevel)
        (by
          rw [discreteAt, List.all_eq_false] at hdisc
          rcases hdisc with ⟨q, hqm, hq⟩
          exact ⟨q, by rw [hn]; exact hqm, by simpa using hq⟩)
      have htc1 : targetcell ctx R.lab R.ptn level tcLevel (-1) + 1 < n := by
        have hb := cells_bound (nn := ctx.n)
          (by
            have h1 := hst.ptnSize
            have h2 := hn
            omega)
          hst.ptnEnd p hpm
        have hl := cells_le p hpm
        have h1 := hst.ptnSize
        rw [hptc]
        omega
      rw [maketargetcell_map σ hn hn' hg hst.labOk hst.labSize hst.ptnSize
        hst.ptnEnd htc1]
      dsimp only
      generalize hM : maketargetcell ctx R.lab R.ptn level tcLevel (-1) = M
      have hM1 : M.1 = targetcell ctx R.lab R.ptn level tcLevel (-1) := by
        rw [← hM]
        rfl
      have hM22 : M.2.2 = cellEnd R.ptn level
          (targetcell ctx R.lab R.ptn level tcLevel (-1) + 1) -
            targetcell ctx R.lab R.ptn level tcLevel (-1) + 1 := by
        rw [← hM]
        rfl
      have htc1' : M.1 + 1 < n := by
        rw [hM1]
        exact htc1
      have hjlt : cellEnd R.ptn level (M.1 + 1) < n := by
        have h1 := cellEnd_lt (ptn := R.ptn) (level := level)
          (i := M.1 + 1)
          (by
            have := hst.ptnSize
            omega)
          hst.ptnEnd
        have h2 := hst.ptnSize
        omega
      have hjge : M.1 + 1 ≤ cellEnd R.ptn level (M.1 + 1) := cellEnd_ge
      congr 1
      refine List.map_congr_left fun o ho => ?_
      have ho' := List.mem_range.mp ho
      have hpos : M.1 + o < R.lab.size := by
        have h1 := hst.labSize
        rw [hM22, ← hM1] at ho'
        omega
      rw [getElem!_map_of_lt σ.toFun R.lab hpos,
        breakout_map σ hst.labOk ⟨M.1 + o, by omega, hpos, rfl⟩]
      dsimp only
      exact specNode_map σ hn hn' hg tcLevel fuel (level + 1) _ _ _ _
        (show ((breakout R.lab R.ptn (level + 1) M.1
              R.lab[M.1 + o]!).1).size = n from
          ((breakout_ok hst.labOk (by omega) (hst.labOk _ hpos)).1).trans
            hst.labSize)
        ((breakout_ok hst.labOk (by omega) (hst.labOk _ hpos)).2)
        (by
          show (R.ptn.set! M.1 (level + 1)).size = n
          rw [Array.size_set!]
          exact hst.ptnSize)
        (by
          show insert 0 M.1 < 2 ^ n
          exact insert_lt (Nat.two_pow_pos n) (by omega))
        (by
          show (R.ptn.set! M.1 (level + 1))[(R.ptn.set! M.1
              (level + 1)).size - 1]! ≤ level + 1
          exact ptnEnd_set! (Nat.le_succ_of_le hst.ptnEnd))
    · simp only [if_true]
      rw [leafRows_map σ hn hn' hg hst.labOk hst.labSize]

end Hex.GraphIso.Nauty
