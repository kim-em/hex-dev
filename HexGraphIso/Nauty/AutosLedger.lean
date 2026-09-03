/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Stabilize
public import HexGraphIso.Nauty.OrbJoin
public import HexGraphIso.Nauty.SearchInv
import all HexGraphIso.Nauty.Search

public section

/-!
The autos-store ledger (SPEC § Verified search refinement, the
target-cell pruning clause of the domination obligation).

`shortprune` and `longprune` filter the sibling iteration through the
`(fix, mcr)` pairs of the bounded autos workspace. This file gives the
pairs their semantics and proves the filters sound against it, in the
shape the maximality induction consumes.

* **The pair semantics.** `PairOk` reads a stored `(fix, mcr)` pair at
  a node: every vertex outside `mcr` is carried strictly downward by
  some checked automorphism that fixes `fix` pointwise and stabilizes
  the node's cells. The realizers are existential per vertex, so the
  predicate covers both the explicit pairs (`fmperm` of an admitted
  generator, realized by its powers) and the implicit ones (`fmptn` of
  a cheapautom partition, realized by the small-cell subtree theorem).
* **The store.** `AutosOk` is the per-pair ledger over the workspace;
  `autosOk_pushAuto` covers both the push and the cap-slot overwrite.
  The induction maintains `AutosOk` anchored at the root partition
  (where it is unconditional) and moves single pairs down the path
  with `pairOk_descend` exactly when the pair's `fix` covers the
  vertex being individualized — for the pairs a filter actually
  applies, `fix` contains every base vertex, so the descent is always
  available where it is needed.
* **Filter soundness.** `pruned_carried` is the well-founded descent:
  a vertex of the target cell that the filter drops is carried, by a
  composite of ledger realizers that fixes the current base pointwise
  and stabilizes the node's cells, onto a vertex of the same cell that
  survives. `longprune_carried` and `shortprune_carried` instantiate
  it for the two filters. The conclusion meets `childKey_of_carried`'s
  hypothesis set: the composite is a checked automorphism, its cell
  stabilization is at the consuming node, and the carry lands on a
  surviving sibling whose subtree the incumbent already dominates.

The window of the target cell is read as a vertex bitset by
`windowSet`, and `windowSet_carry` converts cell stabilization into
preservation of that bitset, which is what keeps the descent inside
the cell.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-! # Bitset membership toolkit -/

theorem elem_and (a b v : Nat) :
    elem (a &&& b) v = (elem a v && elem b v) := by
  show (a &&& b).testBit v = _
  exact Nat.testBit_and ..

/-- A passed fix test is a pointwise inclusion of the fixed base. -/
theorem elem_of_and_eq {a b u : Nat} (h : (a &&& b == a) = true)
    (hu : elem a u = true) : elem b u = true := by
  have he : a &&& b = a := (beq_iff_eq ..).mp h
  have := elem_and a b u
  rw [he, hu] at this
  exact (Bool.and_eq_true _ _).mp this.symm |>.2

/-! # The target cell as a vertex set -/

/-- The vertex set of a labelling window, as a bitset. -/
@[expose] def windowSet (lab : Array Nat) (tc len : Nat) : Nat :=
  (segN lab tc len).foldl (fun s w => insert s w) 0

private theorem elem_foldl_insert :
    ∀ (l : List Nat) (s u : Nat),
      elem (l.foldl (fun s w => insert s w) s) u =
        (elem s u || l.any (· == u))
  | [], s, u => by simp
  | w :: l, s, u => by
    rw [List.foldl_cons, elem_foldl_insert l, List.any_cons]
    show _ = (s.testBit u || (w == u || _))
    have : elem (insert s w) u = (elem s u || w == u) := by
      show (insert s w).testBit u = (s.testBit u || w == u)
      rw [testBit_insert]
    rw [this, Bool.or_assoc]
    rfl

/-- Window-set membership is window membership. -/
theorem elem_windowSet {lab : Array Nat} {tc len u : Nat} :
    elem (windowSet lab tc len) u = true ↔ u ∈ segN lab tc len := by
  rw [windowSet, elem_foldl_insert]
  constructor
  · intro h
    rcases (Bool.or_eq_true _ _).mp h with h0 | hany
    · exact absurd h0 (by simp [elem])
    · obtain ⟨w, hw, hbeq⟩ := List.any_eq_true.mp hany
      rwa [(beq_iff_eq ..).mp hbeq] at hw
  · intro h
    exact (Bool.or_eq_true _ _).mpr <| Or.inr <|
      List.any_eq_true.mpr ⟨u, h, by simp⟩

/-- Every window vertex is a vertex. -/
theorem windowSet_lt {lab : Array Nat} {tc len u : Nat}
    (hok : LabOk lab n) (hsz : tc + len ≤ lab.size)
    (hu : elem (windowSet lab tc len) u = true) : u < n := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (elem_windowSet.mp hu)
  exact hok _ (by have := List.mem_range.mp ho; omega)

/-- Cell stabilization preserves the cell's vertex set. -/
theorem windowSet_carry {ptn lab γ : Array Nat} {level tc len u : Nat}
    (hstab : CellStab ptn level lab γ)
    (hic : IsCell ptn level tc len) (hsz : tc + len ≤ lab.size)
    (hu : elem (windowSet lab tc len) u = true) :
    elem (windowSet lab tc len) γ[u]! = true := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (elem_windowSet.mp hu)
  have ho' := List.mem_range.mp ho
  have hperm := hstab tc len hic
  refine elem_windowSet.mpr (hperm.symm.mem_iff.mp ?_)
  have : γ[lab[tc + o]!]! =
      (lab.map fun w => γ[w]!)[tc + o]! := by
    rw [getElem!_map_of_lt _ _ (by omega)]
  rw [this]
  exact List.mem_map.mpr ⟨o, ho, rfl⟩

/-! # The pair semantics and the store ledger -/

/-- The reading of one stored `(fix, mcr)` pair at a node: every
vertex outside `mcr` is carried strictly downward by a checked
automorphism fixing `fix` pointwise and stabilizing the node's cells.
The realizers are per-vertex: the explicit `fmperm` pairs use powers
of the admitted generator, the implicit `fmptn` pairs the small-cell
subtree theorem. -/
@[expose] def PairOk (g ptn lab : Array Nat) (level nn fix mcr : Nat) :
    Prop :=
  ∀ v, v < nn → elem mcr v = false → ∃ γ : Array Nat,
    checkAutom g γ nn = true ∧
    (∀ u, u < nn → elem fix u = true → γ[u]! = u) ∧
    CellStab ptn level lab γ ∧ γ[v]! < v

/-- The store ledger: every workspace pair reads validly at the node. -/
@[expose] def AutosOk (g ptn lab : Array Nat) (level nn : Nat)
    (autos : Array (Nat × Nat)) : Prop :=
  ∀ p ∈ autos.toList, PairOk g ptn lab level nn p.1 p.2

/-- Recording a valid pair keeps the ledger, in both the push and the
cap-slot overwrite branch. -/
theorem autosOk_pushAuto {g ptn lab : Array Nat} {level nn : Nat}
    {st : SearchSt} {pair : Nat × Nat}
    (hok : AutosOk g ptn lab level nn st.autos)
    (hp : PairOk g ptn lab level nn pair.1 pair.2) :
    AutosOk g ptn lab level nn (pushAuto st pair).autos := by
  intro q hq
  rw [pushAuto] at hq
  split at hq
  · rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] at hq
    rcases List.mem_or_eq_of_mem_set hq with hmem | rfl
    · exact hok q hmem
    · exact hp
  · rw [Array.toList_push] at hq
    rcases List.mem_append.mp hq with hmem | hlast
    · exact hok q hmem
    · rw [List.mem_singleton.mp hlast]
      exact hp

/-- The ledger moves down one individualize-and-refine step for any
pair whose `fix` covers the individualized vertex: each realizer's
cell stabilization is pushed through `breakout` (it fixes the split
vertex) and `refine`, and its other three clauses are untouched. -/
theorem pairOk_descend {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) {lab ptn : Array Nat}
    {level tc len o : Nat} {active' numcells' : Nat} {fix mcr : Nat}
    (hp : PairOk ctx.g ptn lab level n fix mcr)
    (hic : IsCell ptn level tc len) (hsize : tc + len ≤ ptn.size)
    (hlsz : lab.size = ptn.size) (ho : o < len) (hlen2 : 2 ≤ len)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, ptn[q]! ≠ level + 1)
    (hvo : lab[tc + o]! < n)
    (hfixmem : elem fix lab[tc + o]! = true)
    (hlab2 : LabOk (breakout lab ptn (level + 1) tc
      lab[tc + o]!).1 n)
    (hsl2 : (breakout lab ptn (level + 1) tc lab[tc + o]!).1.size = n)
    (hsp2 : (breakout lab ptn (level + 1) tc lab[tc + o]!).2.1.size = n)
    (hact2 : active' < 2 ^ n)
    (hend2 : (breakout lab ptn (level + 1) tc
      lab[tc + o]!).2.1[(breakout lab ptn (level + 1) tc
        lab[tc + o]!).2.1.size - 1]! ≤ level + 1)
    (hstarts2 : ∀ v : Nat, elem active' v = true → v = 0 ∨
      (breakout lab ptn (level + 1) tc
        lab[tc + o]!).2.1[v - 1]! ≤ level + 1) :
    PairOk ctx.g
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        (breakout lab ptn (level + 1) tc lab[tc + o]!).2.1
        active' numcells').ptn
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        (breakout lab ptn (level + 1) tc lab[tc + o]!).2.1
        active' numcells').lab
      (level + 1) n fix mcr := by
  intro v hv hmcr
  obtain ⟨γ, hca, hfixes, hstab, hlt⟩ := hp v hv hmcr
  refine ⟨γ, hca, hfixes, ?_, hlt⟩
  have hfixv : γ[lab[tc + o]!]! = lab[tc + o]! :=
    hfixes _ hvo hfixmem
  have hbstab := cellStab_breakout hstab hic hsize hlsz ho hlen2
    hend hvals hfixv
  exact cellStab_refine hn hbstab hgsz hca hsl2 hlab2 hsp2 hact2
    hend2 hstarts2

/-! # Filter soundness: the well-founded descent -/

/-- The descent core, abstract in the surviving set `R`: whenever a
dropped vertex is strictly carried down by some ledger realizer, every
cell vertex is carried by a composite realizer onto a survivor. -/
theorem pruned_carried {g ptn lab : Array Nat} {level tc len : Nat}
    {fixedpts R : Nat}
    (hb : ∀ v, v < n → g[v]! < 2 ^ n)
    (hok : LabOk lab n) (hs : lab.size = n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hic : IsCell ptn level tc len) (hsz : tc + len ≤ n)
    (hdrop : ∀ u, u < n →
      elem (windowSet lab tc len) u = true → elem R u = false →
      ∃ fix mcr, PairOk g ptn lab level n fix mcr ∧
        elem mcr u = false ∧
        (∀ w, w < n → elem fixedpts w = true → elem fix w = true)) :
    ∀ v, v < n → elem (windowSet lab tc len) v = true →
      ∃ γ, checkAutom g γ n = true ∧
        (∀ u, u < n → elem fixedpts u = true → γ[u]! = u) ∧
        CellStab ptn level lab γ ∧
        elem (windowSet lab tc len) γ[v]! = true ∧
        elem R γ[v]! = true := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro hv hW
    rcases hR : elem R v with _ | _
    · obtain ⟨fix, mcr, hpair, hmcr, hcover⟩ :=
        hdrop v hv hW hR
      obtain ⟨γ₁, hca1, hfix1, hstab1, hlt1⟩ := hpair v hv hmcr
      have hv1 : γ₁[v]! < n := checkAutom_bound hca1 v hv
      have hW1 : elem (windowSet lab tc len) γ₁[v]! = true :=
        windowSet_carry hstab1 hic (by omega) hW
      obtain ⟨γ₂, hca2, hfix2, hstab2, hW2, hR2⟩ :=
        ih γ₁[v]! hlt1 hv1 hW1
      refine ⟨composePerm γ₂ γ₁ n, checkAutom_compose hca2 hca1,
        ?_, cellStab_comp hok hsp hs hend hstab2 hstab1, ?_, ?_⟩
      · intro u hu hfu
        rw [composePerm_getElem! _ _ hu,
          hfix1 u hu (hcover u hu hfu)]
        exact hfix2 u hu hfu
      · rw [composePerm_getElem! _ _ hv]
        exact hW2
      · rw [composePerm_getElem! _ _ hv]
        exact hR2
    · exact ⟨Array.range n, checkAutom_range hb,
        fun u hu _ => by
          rw [getElem!_pos _ _ (by simpa using hu),
            Array.getElem_range],
        cellStab_range hok,
        by
          rw [getElem!_pos _ _ (by simpa using hv),
            Array.getElem_range]
          exact hW,
        by
          rw [getElem!_pos _ _ (by simpa using hv),
            Array.getElem_range]
          exact hR⟩

/-! # The two filters -/

private theorem exists_all_false {α : Type} {f : α → Bool} :
    ∀ {l : List α}, l.all f = false → ∃ x ∈ l, f x = false
  | [], h => absurd h (by simp)
  | x :: l, h => by
    rw [List.all_cons] at h
    rcases hx : f x with _ | _
    · exact ⟨x, List.mem_cons_self .., hx⟩
    · rw [hx, Bool.true_and] at h
      obtain ⟨y, hy, hfy⟩ := exists_all_false h
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

private theorem elem_foldl_prune :
    ∀ (l : List (Nat × Nat)) (t fixedpts v : Nat),
      elem (l.foldl (fun acc p =>
          if fixedpts &&& p.1 == fixedpts then acc &&& p.2
          else acc) t) v =
        (elem t v && l.all fun p =>
          !(fixedpts &&& p.1 == fixedpts) || elem p.2 v)
  | [], t, _, v => by simp
  | p :: l, t, fixedpts, v => by
    rw [List.foldl_cons, elem_foldl_prune l, List.all_cons]
    rcases htest : (fixedpts &&& p.1 == fixedpts) with _ | _
    · simp [htest]
    · simp [htest, elem_and, Bool.and_assoc]

/-- Membership after `longprune`: the cell bit survives exactly when
every fix-passing pair's `mcr` keeps it. -/
theorem elem_longprune (tcell fixedpts v : Nat)
    (autos : Array (Nat × Nat)) :
    elem (longprune tcell fixedpts autos) v =
      (elem tcell v && autos.toList.all fun p =>
        !(fixedpts &&& p.1 == fixedpts) || elem p.2 v) := by
  rw [longprune, ← Array.foldl_toList]
  exact elem_foldl_prune autos.toList tcell fixedpts v

/-- `longprune` soundness: under the ledger for fix-passing pairs,
every vertex of the target cell is carried by a checked, base-fixing,
cell-stabilizing automorphism onto a surviving vertex of the cell. -/
theorem longprune_carried {g ptn lab : Array Nat}
    {level tc len fixedpts : Nat} {autos : Array (Nat × Nat)}
    (hb : ∀ v, v < n → g[v]! < 2 ^ n)
    (hok : LabOk lab n) (hs : lab.size = n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hic : IsCell ptn level tc len) (hsz : tc + len ≤ n)
    (haut : ∀ p ∈ autos.toList,
      (fixedpts &&& p.1 == fixedpts) = true →
      PairOk g ptn lab level n p.1 p.2) :
    ∀ v, v < n → elem (windowSet lab tc len) v = true →
      ∃ γ, checkAutom g γ n = true ∧
        (∀ u, u < n → elem fixedpts u = true → γ[u]! = u) ∧
        CellStab ptn level lab γ ∧
        elem (windowSet lab tc len) γ[v]! = true ∧
        elem (longprune (windowSet lab tc len) fixedpts autos)
          γ[v]! = true := by
  refine pruned_carried hb hok hs hsp hend hic hsz ?_
  intro u hu hW hR
  rw [elem_longprune, hW, Bool.true_and] at hR
  obtain ⟨p, hpmem, hpf⟩ := exists_all_false hR
  have htest : (fixedpts &&& p.1 == fixedpts) = true := by
    rcases h : (fixedpts &&& p.1 == fixedpts) with _ | _
    · rw [h] at hpf
      exact absurd hpf (by simp)
    · rfl
  have hmcr : elem p.2 u = false := by
    rcases h : elem p.2 u with _ | _
    · rfl
    · rw [htest, h] at hpf
      exact absurd hpf (by simp)
  exact ⟨p.1, p.2, haut p hpmem htest, hmcr,
    fun w _ hw => elem_of_and_eq htest hw⟩

/-- `shortprune` soundness: with the ledger reading of the most recent
pair and its fix test (the `needshortprune` protocol's obligation),
every vertex of the target cell is carried onto a survivor. -/
theorem shortprune_carried {g ptn lab : Array Nat}
    {level tc len : Nat} {st : SearchSt}
    (hb : ∀ v, v < n → g[v]! < 2 ^ n)
    (hok : LabOk lab n) (hs : lab.size = n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hic : IsCell ptn level tc len) (hsz : tc + len ≤ n)
    (hlast : ∀ fix mcr, st.autos.back? = some (fix, mcr) →
      (st.fixedpts &&& fix == st.fixedpts) = true ∧
        PairOk g ptn lab level n fix mcr) :
    ∀ v, v < n → elem (windowSet lab tc len) v = true →
      ∃ γ, checkAutom g γ n = true ∧
        (∀ u, u < n → elem st.fixedpts u = true → γ[u]! = u) ∧
        CellStab ptn level lab γ ∧
        elem (windowSet lab tc len) γ[v]! = true ∧
        elem (shortprune (windowSet lab tc len) st) γ[v]! = true := by
  refine pruned_carried hb hok hs hsp hend hic hsz ?_
  intro u hu hW hR
  rw [shortprune] at hR
  split at hR
  · next fix mcr heq =>
    obtain ⟨htest, hpair⟩ := hlast fix mcr heq
    rw [elem_and, hW, Bool.true_and] at hR
    exact ⟨fix, mcr, hpair, hR,
      fun w _ hw => elem_of_and_eq htest hw⟩
  · rw [hW] at hR
    exact absurd hR (by simp)

end Hex.GraphIso.Nauty
