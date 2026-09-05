/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.NodeLit

public section

/-!
Invariant separators for negative goals: the first two codes of the
spec key, computed without a tree search — one refinement for the
head and one refinement per root child for the second (the maximum
child code, because the key order compares codes first). Isomorphic
graphs have equal spec keys, so a difference in this prefix is a
kernel-cheap witness of non-isomorphism, replacing the full
certificate replay whenever it fires. `sepDiffLit` is the kernel
obligation over tied flat literals, following `checkKeyFlat`.
-/

namespace Hex.GraphIso

open Nauty

private theorem foldl_congr_mem {α β : Type} {f g : α → β → α} :
    ∀ (l : List β), (∀ a b, b ∈ l → f a b = g a b) →
      ∀ (a : α), l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, h, a => by
    rw [List.foldl_cons, List.foldl_cons, h a b List.mem_cons_self]
    exact foldl_congr_mem l
      (fun a' b' hb' => h a' b' (List.mem_cons_of_mem _ hb')) _

/-- The greater key's code list keeps the greater head. -/
theorem keyMax_codes_head {k1 k2 : Key n} {a b : Nat}
    {as bs : List Nat} (h1 : k1.codes = a :: as)
    (h2 : k2.codes = b :: bs) :
    ∃ rest, (keyMax k1 k2).codes = Nat.max a b :: rest := by
  have e1 : k1 = ⟨a :: as, k1.rows⟩ := by
    rw [← h1]
  have e2 : k2 = ⟨b :: bs, k2.rows⟩ := by
    rw [← h2]
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have hcmp := keyCmp_cons_lt hab as bs k1.rows k2.rows
    rw [e1, e2, keyMax, hcmp, ite_eq_left rfl]
    have hm : Nat.max a b = b := by
      show max a b = b
      rw [Nat.max_def, ite_eq_left (Nat.le_of_lt hab)]
    rw [hm]
    exact ⟨bs, rfl⟩
  · subst hab
    have hm : Nat.max a a = a := by
      show max a a = a
      rw [Nat.max_def, ite_eq_left (Nat.le_refl a)]
    rw [e1, e2, keyMax, hm]
    split
    · exact ⟨bs, rfl⟩
    · exact ⟨as, rfl⟩
  · have hcmp := keyCmp_cons_gt hab as bs k1.rows k2.rows
    rw [e1, e2, keyMax, hcmp,
      ite_eq_right (fun h => Ordering.noConfusion h)]
    have hm : Nat.max a b = a := by
      show max a b = a
      rw [Nat.max_def, ite_eq_right (Nat.not_le.mpr hab)]
    rw [hm]
    exact ⟨as, rfl⟩

/-- The maximal key's code list starts with the maximum of the heads,
whenever every key in play has a head. -/
theorem keysMax_codes_head :
    ∀ (cs : List (Key n)) (c : Key n) (a : Nat) (as : List Nat),
      c.codes = a :: as →
      (∀ k ∈ cs, ∃ b bs, k.codes = b :: bs) →
      ∃ rest, (keysMax c cs).codes =
        cs.foldl (fun mx k => Nat.max mx (k.codes.headD 0)) a :: rest
  | [], _, a, as, h, _ => ⟨as, by rw [keysMax, h, List.foldl_nil]⟩
  | k' :: rest, c, a, as, h, hall => by
    obtain ⟨b, bs, hb⟩ := hall k' List.mem_cons_self
    obtain ⟨r2, hr2⟩ := keyMax_codes_head h hb
    obtain ⟨rr, hrr⟩ := keysMax_codes_head rest (keyMax c k')
      (Nat.max a b) r2 hr2
      (fun k hk => hall k (List.mem_cons_of_mem _ hk))
    refine ⟨rr, ?_⟩
    rw [keysMax, hrr, List.foldl_cons, hb, List.headD_cons]

/-- The maximal key over an indexed child family keeps, as its head,
the running maximum of the family's head codes. -/
theorem sep_fold_eq (mt : Nat) (ch : Nat → Key n) (H : Nat → Nat)
    (hch : ∀ o, ∃ rest, (ch o).codes = H o :: rest) :
    ∃ rest,
      (keysMax (ch 0) ((List.range mt).map (ch ∘ Nat.succ))).codes =
        ((List.range mt).foldl
          (fun mx j => Nat.max mx (H (j + 1))) (H 0)) :: rest := by
  obtain ⟨r0, hr0⟩ := hch 0
  obtain ⟨restM, hM⟩ := keysMax_codes_head
    ((List.range mt).map (ch ∘ Nat.succ)) (ch 0) (H 0) r0 hr0
    (fun k hk => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
      obtain ⟨r, hr⟩ := hch (Nat.succ j)
      exact ⟨_, r, hr⟩)
  refine ⟨restM, ?_⟩
  rw [hM, List.foldl_map]
  refine congrArg (· :: restM) (foldl_congr_mem (List.range mt)
    (fun acc j _ => ?_) _)
  obtain ⟨r, hr⟩ := hch (Nat.succ j)
  show Nat.max acc ((ch (Nat.succ j)).codes.headD 0) = _
  rw [hr, List.headD_cons]

/-- The first two spec-key codes of one node, computed with a single
refinement for the head and one refinement per child for the second —
the shallow view of `specNode` the separator evaluates. -/
@[expose] def nodeSep (ctx : Ctx n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) : Option Nat × Option Nat :=
  let rs := refine ctx level lab ptn active numcells
  if discreteAt rs.ptn level n then
    (some rs.longcode, some codeSentinel)
  else
    let tcr := specMaketargetcell ctx rs.lab rs.ptn level 100
    let childHead := fun (o : Nat) =>
      let br := breakout n rs.lab rs.ptn (level + 1) tcr.1
        rs.lab[tcr.1 + o]!
      (refine ctx (level + 1) br.1 br.2.1 br.2.2
        (rs.numcells + 1)).longcode
    (some rs.longcode,
      some ((List.range (tcr.2.2 - 1)).foldl
        (fun mx j => Nat.max mx (childHead (j + 1))) (childHead 0)))

/-- With two levels of fuel in hand, the first two codes of `specNode`
are exactly `nodeSep`. -/
theorem specNode_codes_two (ctx : Ctx n) (fuel level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) :
    ((specNode ctx 100 (fuel + 2) level lab ptn active
        numcells).codes.head?,
      (specNode ctx 100 (fuel + 2) level lab ptn active
        numcells).codes.tail.head?) =
      nodeSep ctx level lab ptn active numcells := by
  rw [specNode, nodeSep]
  rcases hdisc : discreteAt
      (refine ctx level lab ptn active numcells).ptn level n
    with _ | _
  · simp only [Bool.false_eq_true, ite_false]
    obtain ⟨mt, hmt⟩ : ∃ mt, (specMaketargetcell ctx
        (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn level
          100).2.2 = mt + 1 := ⟨_, rfl⟩
    rw [hmt, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hchild : ∀ o : Nat, ∃ rest,
        (specNode ctx 100 (fuel + 1) (level + 1)
          (breakout n (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            (specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1
            (refine ctx level lab ptn active
              numcells).lab[(specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1 + o]!).1
          (breakout n (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            (specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1
            (refine ctx level lab ptn active
              numcells).lab[(specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1 + o]!).2.1
          (breakout n (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            (specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1
            (refine ctx level lab ptn active
              numcells).lab[(specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1 + o]!).2.2
          ((refine ctx level lab ptn active numcells).numcells + 1)).codes =
        (refine ctx (level + 1)
          (breakout n (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            (specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1
            (refine ctx level lab ptn active
              numcells).lab[(specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1 + o]!).1
          (breakout n (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            (specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1
            (refine ctx level lab ptn active
              numcells).lab[(specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1 + o]!).2.1
          (breakout n (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            (specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1
            (refine ctx level lab ptn active
              numcells).lab[(specMaketargetcell ctx
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
                100).1 + o]!).2.2
          ((refine ctx level lab ptn active numcells).numcells + 1)).longcode :: rest :=
      fun o => specNode_codes_head ctx 100 fuel (level + 1) _ _ _ _
    obtain ⟨restMax, hrestMax⟩ := sep_fold_eq mt _ _ hchild
    dsimp only
    simp only [List.head?_cons, List.tail_cons, hrestMax]
    rfl
  · simp only [ite_true]
    rfl

/-- The first two codes of the spec key of a graph presentation:
`canonSpec` read off directly below two vertices, `nodeSep` at the
root otherwise. -/
@[expose] def sepCodes (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : Option Nat × Option Nat :=
  if n < 2 then
    ((canonSpec n g lab0 cellEnds).codes.head?,
      (canonSpec n g lab0 cellEnds).codes.tail.head?)
  else
    nodeSep { g := g } 1 lab0 (initPtn n (n + 2) cellEnds)
      (initActive n cellEnds) cellEnds.length

/-- `sepCodes` is exactly the spec key's first two codes. -/
theorem sepCodes_eq (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) :
    sepCodes n g lab0 cellEnds =
      ((canonSpec n g lab0 cellEnds).codes.head?,
        (canonSpec n g lab0 cellEnds).codes.tail.head?) := by
  rw [sepCodes]
  rcases Decidable.em (n < 2) with h2 | h2
  · rw [ite_eq_left h2]
  · rw [ite_eq_right h2]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [canonSpec]
    have h0 : ((m + 2) == 0) = false := by simp
    rw [h0]
    simp only [Bool.false_eq_true, ite_false]
    exact (specNode_codes_two _ m 1 _ _ _ _).symm

/-- Isomorphic graphs agree on the separator codes. -/
theorem sepCodes_eq_of_isomorphic {n k : Nat} {G H : Colored n k}
    (hiso : Isomorphic G H) :
    sepCodes n (rowsOf G) (initialPartition G).1
        (initialPartition G).2 =
      sepCodes n (rowsOf H) (initialPartition H).1
        (initialPartition H).2 := by
  rw [sepCodes_eq, sepCodes_eq]
  have h := canonSpecKey_eq_of_isomorphic hiso
  rw [canonSpecKey, canonSpecKey] at h
  rw [h]

/-- Disagreement of optional codes, priced for kernel reduction. -/
@[expose] def optNe : Option Nat → Option Nat → Bool
  | none, none => false
  | some a, some b => a != b
  | _, _ => true

theorem optNe_self (a : Option Nat) : optNe a a = false := by
  rcases a with _ | a
  · rfl
  · show (a != a) = false
    simp

/-- Componentwise disagreement of two separator-code pairs. The
pattern match forces each pair once, so the kernel evaluates each
side's `sepCodes` a single time. -/
@[expose] def sepPair :
    Option Nat × Option Nat → Option Nat × Option Nat → Bool
  | (a1, a2), (b1, b2) => optNe a1 b1 || optNe a2 b2

theorem sepPair_self (c : Option Nat × Option Nat) :
    sepPair c c = false := by
  obtain ⟨a1, a2⟩ := c
  rw [sepPair, optNe_self, optNe_self]
  rfl

/-! # The separators over the kernel's list state

The kernel obligations mirror `nodeSep`, `sepCodes` and `sepRoot` over
the bitset list state of `HexGraphIso.NodeLit`, so that a separator
proof costs the kernel exactly the refinements it names. Two vertices
or fewer never reach a separator (the tactic gates the route on its
node budget), so the list forms cover the search branch only. -/

/-- `nodeSep` over list state. -/
@[expose] def nodeSepL (ctx : CtxL) (level : Nat) (lab ptn : List Nat)
    (active numcells : Nat) : Option Nat × Option Nat :=
  let rs := refineL ctx level lab ptn active numcells
  if discreteAtL rs.ptn level ctx.n then
    (some rs.longcode, some codeSentinel)
  else
    let tcr := specMaketargetcellL ctx rs.lab rs.ptn level 100
    let childHead := fun (o : Nat) =>
      let br := breakoutL ctx.n rs.lab rs.ptn (level + 1) tcr.1
        (atD rs.lab (tcr.1 + o) 0)
      (refineL ctx (level + 1) br.1 br.2.1 br.2.2
        (rs.numcells + 1)).longcode
    (some rs.longcode,
      some ((List.range (tcr.2.2 - 1)).foldl
        (fun mx j => Nat.max mx (childHead (j + 1))) (childHead 0)))

theorem nodeSepL_eq (ctx : Ctx n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) :
    nodeSepL ctx.toL level lab.toList ptn.toList active.toNat numcells =
      nodeSep ctx level lab ptn active numcells := by
  rw [nodeSepL, nodeSep]
  simp only [refineL_eq, toL_lab, toL_ptn, toL_longcode, toL_numcells, toL_n,
    discreteAtL_eq, specMaketargetcellL_eq, breakoutL_eq, ← getBang_eq_atD]

/-- `sepCodes` over list state, on the search branch. -/
@[expose] def sepCodesL (n : Nat) (g lab0 : List Nat) (cellEnds : List Nat) :
    Option Nat × Option Nat :=
  nodeSepL ⟨n, g⟩ 1 lab0 (initPtn n (n + 2) cellEnds).toList
    (initActive n cellEnds).toNat cellEnds.length

theorem sepCodesL_eq (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) (h2 : 2 ≤ n) :
    sepCodesL n (g.toList.map VSet.toNat) lab0.toList cellEnds =
      sepCodes n g lab0 cellEnds := by
  rw [sepCodesL, sepCodes, ite_eq_right (by omega)]
  exact nodeSepL_eq { g := g } 1 lab0 _ _ _

/-- The separator over tied flat literals: the negative route's
cheapest kernel obligation, mirroring `checkKeyLit`'s shape. -/
@[expose] def sepDiffLit {n k : Nat} (G H : Colored n k)
    (LA LB : List Bool) : Bool :=
  decide (2 ≤ n) &&
  sepPair
    (sepCodesL n (flatRows n LA).toList (initialPartition G).1.toList
      (initialPartition G).2)
    (sepCodesL n (flatRows n LB).toList (initialPartition H).1.toList
      (initialPartition H).2)

/-- Tying equalities plus a separator disagreement prove
non-isomorphism: the kernel evaluates one refinement per graph plus
one per root child, and no certificate at all. -/
theorem not_isomorphic_of_sepDiffLit {n k : Nat} {G H : Colored n k}
    {LA LB : List Bool}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (h : sepDiffLit G H LA LB = true) : ¬Isomorphic G H := by
  subst hA hB
  rw [sepDiffLit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, h⟩ := h
  rw [← toNat_rowsOfFlat, ← toNat_rowsOfFlat, sepCodesL_eq _ _ _ _ h2,
    sepCodesL_eq _ _ _ _ h2, rowsOfFlat_eq_rowsOf, rowsOfFlat_eq_rowsOf] at h
  intro hiso
  rw [sepCodes_eq_of_isomorphic hiso, sepPair_self] at h
  cases h

/-- The spec key's head code alone: a single refinement. -/
@[expose] def sepRoot (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) : Option Nat :=
  if n < 2 then
    (canonSpec n g lab0 cellEnds).codes.head?
  else
    some (refine { g := g } 1 lab0
      (initPtn n (n + 2) cellEnds) (initActive n cellEnds)
      cellEnds.length).longcode

theorem sepRoot_eq (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) :
    sepRoot n g lab0 cellEnds = (sepCodes n g lab0 cellEnds).1 := by
  rw [sepRoot, sepCodes]
  rcases Decidable.em (n < 2) with h2 | h2
  · rw [ite_eq_left h2, ite_eq_left h2]
  · rw [ite_eq_right h2, ite_eq_right h2, nodeSep]
    split
    · rfl
    · rfl

/-- `sepRoot` over list state, on the search branch. -/
@[expose] def sepRootL (n : Nat) (g lab0 : List Nat) (cellEnds : List Nat) :
    Option Nat :=
  some (refineL ⟨n, g⟩ 1 lab0 (initPtn n (n + 2) cellEnds).toList
    (initActive n cellEnds).toNat cellEnds.length).longcode

theorem sepRootL_eq (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) (h2 : 2 ≤ n) :
    sepRootL n (g.toList.map VSet.toNat) lab0.toList cellEnds =
      sepRoot n g lab0 cellEnds := by
  rw [sepRootL, sepRoot, ite_eq_right (by omega)]
  exact congrArg some (congrArg RefineStL.longcode
    (refineL_eq { g := g } 1 lab0 _ _ _))

/-- The root separator over tied flat literals: one refinement per
graph, the cheapest possible negative kernel obligation. -/
@[expose] def sepRootLit {n k : Nat} (G H : Colored n k)
    (LA LB : List Bool) : Bool :=
  decide (2 ≤ n) &&
  optNe
    (sepRootL n (flatRows n LA).toList (initialPartition G).1.toList
      (initialPartition G).2)
    (sepRootL n (flatRows n LB).toList (initialPartition H).1.toList
      (initialPartition H).2)

/-- Tying equalities plus a root-code disagreement prove
non-isomorphism with one refinement per graph. -/
theorem not_isomorphic_of_sepRootLit {n k : Nat} {G H : Colored n k}
    {LA LB : List Bool}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (h : sepRootLit G H LA LB = true) : ¬Isomorphic G H := by
  subst hA hB
  rw [sepRootLit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, h⟩ := h
  rw [← toNat_rowsOfFlat, ← toNat_rowsOfFlat, sepRootL_eq _ _ _ _ h2,
    sepRootL_eq _ _ _ _ h2, rowsOfFlat_eq_rowsOf, rowsOfFlat_eq_rowsOf,
    sepRoot_eq, sepRoot_eq] at h
  intro hiso
  rw [sepCodes_eq_of_isomorphic hiso, optNe_self] at h
  cases h

/-- The compiled-side root-separator decision. -/
@[expose] def sepRootG {n k : Nat} (G H : Colored n k) : Bool :=
  optNe
    (sepRoot n (rowsOf G) (initialPartition G).1
      (initialPartition G).2)
    (sepRoot n (rowsOf H) (initialPartition H).1
      (initialPartition H).2)

/-- The compiled-side separator decision on two coloured graphs. -/
@[expose] def sepDiffG {n k : Nat} (G H : Colored n k) : Bool :=
  sepPair
    (sepCodes n (rowsOf G) (initialPartition G).1
      (initialPartition G).2)
    (sepCodes n (rowsOf H) (initialPartition H).1
      (initialPartition H).2)

end Hex.GraphIso
