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

theorem exists_all_false {α : Type} {f : α → Bool} :
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

/-- If `longprune` removes a current member, one applicable ledger pair
carries it strictly downward while stabilizing the node's cells. -/
theorem longprune_drop {g ptn lab : Array Nat} {level fixedpts v tcell : Nat}
    {autos : Array (Nat × Nat)}
    (hv : v < n) (hmem : elem tcell v = true)
    (hdrop : elem (longprune tcell fixedpts autos) v = false)
    (haut : ∀ p ∈ autos.toList,
      (fixedpts &&& p.1 == fixedpts) = true →
      PairOk g ptn lab level n p.1 p.2) :
    ∃ γ, checkAutom g γ n = true ∧ CellStab ptn level lab γ ∧
      γ[v]! < v := by
  rw [elem_longprune, hmem, Bool.true_and] at hdrop
  obtain ⟨p, hp, hpf⟩ := exists_all_false hdrop
  have hfix : (fixedpts &&& p.1 == fixedpts) = true := by
    rcases h : (fixedpts &&& p.1 == fixedpts) with _ | _
    · rw [h] at hpf
      exact absurd hpf (by simp)
    · rfl
  have hmcr : elem p.2 v = false := by
    rcases h : elem p.2 v with _ | _
    · rfl
    · rw [hfix, h] at hpf
      exact absurd hpf (by simp)
  obtain ⟨γ, hγ, _, hstab, hlt⟩ := haut p hp hfix v hv hmcr
  exact ⟨γ, hγ, hstab, hlt⟩

/-- `longprune` only removes set members. -/
theorem longprune_subset {tcell fixedpts : Nat}
    {autos : Array (Nat × Nat)} {v : Nat}
    (h : elem (longprune tcell fixedpts autos) v = true) :
    elem tcell v = true := by
  rw [elem_longprune] at h
  exact (Bool.and_eq_true _ _).mp h |>.1

/-- `shortprune` only removes set members. -/
theorem shortprune_subset {tcell : Nat} {st : SearchSt} {v : Nat}
    (h : elem (shortprune tcell st) v = true) : elem tcell v = true := by
  rw [shortprune] at h
  split at h
  · exact (Bool.and_eq_true _ _).mp (by simpa [elem_and] using h) |>.1
  · exact h

/-- If `shortprune` removes a current member, the last ledger pair carries
it strictly downward while stabilizing the node's cells. -/
theorem shortprune_drop {g ptn lab : Array Nat} {level v tcell : Nat}
    {st : SearchSt}
    (hv : v < n) (hmem : elem tcell v = true)
    (hdrop : elem (shortprune tcell st) v = false)
    (hlast : ∀ fix mcr, st.autos.back? = some (fix, mcr) →
      PairOk g ptn lab level n fix mcr) :
    ∃ γ, checkAutom g γ n = true ∧ CellStab ptn level lab γ ∧
      γ[v]! < v := by
  rw [shortprune] at hdrop
  split at hdrop
  · next fix mcr heq =>
    have hmcr : elem mcr v = false := by
      rw [elem_and, hmem, Bool.true_and] at hdrop
      exact hdrop
    obtain ⟨γ, hγ, _, hstab, hlt⟩ := hlast fix mcr heq v hv hmcr
    exact ⟨γ, hγ, hstab, hlt⟩
  · rw [hmem] at hdrop
    cases hdrop

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


/-! # The explicit pairs: `fmperm` of an admitted generator

The pair recorded for an explicit generator reads validly through the
generator's forward powers: `fix` holds only fixed points, and a
vertex left out of `mcr` is not the least element of its cycle, so
some forward power carries it strictly down. The two loop
characterizations below are proven against structural mirrors of the
`fmperm` loops.
-/

/-- Forward iterates of a single array. -/
private def iter (perm : Array Nat) (k v : Nat) : Nat :=
  applyWord (List.replicate k perm) v

private theorem iter_add (perm : Array Nat) (a b v : Nat) :
    iter perm (a + b) v = iter perm b (iter perm a v) := by
  show applyWord _ _ = _
  rw [← List.replicate_append_replicate, applyWord_append]
  rfl

private theorem iter_cycle {perm : Array Nat} {m j : Nat}
    (hm : iter perm m j = j) :
    ∀ (q r : Nat), iter perm (q * m + r) j = iter perm r j
  | 0, r => by rw [Nat.zero_mul, Nat.zero_add]
  | q + 1, r => by
    rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm m r,
      ← Nat.add_assoc, iter_add, iter_cycle hm q r, ← iter_add,
      Nat.add_comm r m, iter_add, hm]

/-- Every vertex reaching `w` by iteration is itself an iterate of
`w`, over a bounded injective array. -/
private theorem iter_symm {perm : Array Nat} {nn : Nat}
    (hb : ∀ v, v < nn → perm[v]! < nn)
    (hinj : ∀ a b, a < nn → b < nn → perm[a]! = perm[b]! → a = b)
    {j w a : Nat} (hj : j < nn) (ha : iter perm a j = w) :
    ∃ c, iter perm c w = j := by
  obtain ⟨m, hm0, hmraw⟩ :=
    exists_applyWord_replicate_self (n := nn) hb hinj hj
  have hm : iter perm m j = j := hmraw
  have hcycle := iter_cycle (perm := perm) hm
  have hrw : iter perm (a % m) j = w := by
    have hthis := hcycle (a / m) (a % m)
    have hq : a / m * m + a % m = a := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod a m
    rw [hq] at hthis
    rw [← hthis]
    exact ha
  refine ⟨m - a % m, ?_⟩
  rw [← hrw, ← iter_add]
  have hsum : a % m + (m - a % m) = m := by
    have := Nat.mod_lt a hm0
    omega
  rw [hsum, hm]

/-- `v` is the least element of its forward orbit. -/
private def IsOrbMin (perm : Array Nat) (v : Nat) : Prop :=
  ∀ k, v ≤ iter perm k v

/-- The inner marking loop of `fmperm`, structurally. -/
private def markCycle (perm : Array Nat) (i : Nat) :
    List Nat → Array Bool → Nat → Array Bool × Nat
  | [], seen, l => (seen, l)
  | _ :: rest, seen, l =>
    let seen' := seen.set! l true
    if perm[l]! == i then (seen', perm[l]!)
    else markCycle perm i rest seen' perm[l]!

/-- The outer loop of `fmperm`, structurally, carrying the full
state. -/
private def fmpermGo (perm : Array Nat) (nn : Nat) :
    List Nat → Nat → Nat → Array Bool → Nat × Nat × Array Bool
  | [], fix, mcr, seen => (fix, mcr, seen)
  | i :: rest, fix, mcr, seen =>
    if perm[i]! == i then
      fmpermGo perm nn rest (insert fix i) (insert mcr i) seen
    else if seen[i]! then
      fmpermGo perm nn rest fix mcr seen
    else
      fmpermGo perm nn rest fix (insert mcr i)
        (markCycle perm i (List.range nn) seen i).1

/-- The inner loop body, pinned as a definition so branch analysis
happens on free variables. -/
private def innerF (perm : Array Nat) (i : Nat) :
    Nat → Array Bool × Nat → Id (ForInStep (Array Bool × Nat)) :=
  fun _ s =>
    have seen := s.fst
    have l := s.snd
    have seen := seen.set! l true
    have l := perm[l]!
    if (l == i) = true then pure (ForInStep.done (seen, l))
    else pure (ForInStep.yield (seen, l))

/-- The outer loop body, pinned as a definition. -/
private def outerF (perm : Array Nat) (nn : Nat) :
    Nat → Nat × Nat × Array Bool →
      Id (ForInStep (Nat × Nat × Array Bool)) :=
  fun i __s =>
    have fix := __s.fst
    have __s := __s.snd
    have mcr := __s.fst
    have seen := __s.snd
    if (perm[i]! == i) = true then
      have fix := insert fix i
      have mcr := insert mcr i
      pure (ForInStep.yield (fix, mcr, seen))
    else
      if ¬seen[i]! = true then
        have l := i
        do
        let __s ← forIn [:nn] (seen, l) (innerF perm i)
        have seen : Array Bool := __s.fst
        have mcr : Nat := insert mcr i
        pure (ForInStep.yield (fix, mcr, seen))
      else pure (ForInStep.yield (fix, mcr, seen))

private theorem forIn_range_eq {β : Type} (k : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [:k] init f : Id β) = forIn (List.range k) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [:k].start [:k].size [:k].step
      = List.range k := by simp [List.range_eq_range']
  rw [hrange]

/-- The pinned body is the elaborated body. -/
private theorem fmperm_pinned (perm : Array Nat) (nn : Nat) :
    fmperm perm nn =
      (do
        let s ← forIn [:nn]
          ((0 : Nat), (0 : Nat), Array.replicate nn false)
          (outerF perm nn)
        pure (s.fst, s.snd.fst) : Id (Nat × Nat)).run := rfl

/-- Branch readings of the pinned inner body. -/
private theorem innerF_done {perm : Array Nat} {i x cur : Nat}
    {seen : Array Bool} (hc : (perm[cur]! == i) = true) :
    innerF perm i x (seen, cur) =
      pure (ForInStep.done (seen.set! cur true, perm[cur]!)) := by
  show (if (perm[cur]! == i) = true then
      pure (ForInStep.done (seen.set! cur true, perm[cur]!))
    else pure (ForInStep.yield (seen.set! cur true, perm[cur]!))) = _
  rw [ite_eq_left hc]

private theorem innerF_step {perm : Array Nat} {i x cur : Nat}
    {seen : Array Bool} (hc : (perm[cur]! == i) = false) :
    innerF perm i x (seen, cur) =
      pure (ForInStep.yield (seen.set! cur true, perm[cur]!)) := by
  show (if (perm[cur]! == i) = true then
      pure (ForInStep.done (seen.set! cur true, perm[cur]!))
    else pure (ForInStep.yield (seen.set! cur true, perm[cur]!))) = _
  rw [ite_eq_right (by
    intro h
    rw [hc] at h
    exact Bool.noConfusion h)]

/-- The inner loop is `markCycle`. -/
private theorem forIn_innerF_eq (perm : Array Nat) (i : Nat) :
    ∀ (l : List Nat) (seen : Array Bool) (cur : Nat),
      (forIn l (seen, cur) (innerF perm i) :
        Id (Array Bool × Nat)) =
      markCycle perm i l seen cur
  | [], _, _ => rfl
  | x :: l, seen, cur => by
    rw [List.forIn_cons, markCycle]
    rcases hc : (perm[cur]! == i) with _ | _
    · rw [innerF_step (x := x) hc,
        ite_eq_right (fun h => Bool.noConfusion h)]
      exact forIn_innerF_eq perm i l _ _
    · rw [innerF_done (x := x) hc, ite_eq_left rfl]
      rfl

/-- Branch readings of the pinned outer body. -/
private theorem outerF_fixed {perm : Array Nat} {nn i fix mcr : Nat}
    {seen : Array Bool} (hc : (perm[i]! == i) = true) :
    outerF perm nn i (fix, mcr, seen) =
      pure (ForInStep.yield (insert fix i, insert mcr i, seen)) := by
  show (if (perm[i]! == i) = true then
      pure (ForInStep.yield (insert fix i, insert mcr i, seen))
    else _) = _
  rw [ite_eq_left hc]

private theorem outerF_seen {perm : Array Nat} {nn i fix mcr : Nat}
    {seen : Array Bool} (hc : (perm[i]! == i) = false)
    (hs : seen[i]! = true) :
    outerF perm nn i (fix, mcr, seen) =
      pure (ForInStep.yield (fix, mcr, seen)) := by
  show (if (perm[i]! == i) = true then
      pure (ForInStep.yield (insert fix i, insert mcr i, seen))
    else if ¬seen[i]! = true then _
    else pure (ForInStep.yield (fix, mcr, seen))) = _
  rw [ite_eq_right (by
      intro h
      rw [hc] at h
      exact Bool.noConfusion h),
    ite_eq_right (by
      intro hn
      exact hn (by rw [hs]))]

private theorem outerF_unseen {perm : Array Nat} {nn i fix mcr : Nat}
    {seen : Array Bool} (hc : (perm[i]! == i) = false)
    (hs : seen[i]! = false) :
    outerF perm nn i (fix, mcr, seen) =
      (do
        let s ← forIn [:nn] (seen, i) (innerF perm i)
        pure (ForInStep.yield (fix, insert mcr i, s.fst)) :
        Id (ForInStep (Nat × Nat × Array Bool))) := by
  show (if (perm[i]! == i) = true then
      pure (ForInStep.yield (insert fix i, insert mcr i, seen))
    else if ¬seen[i]! = true then
      (do
        let s ← forIn [:nn] (seen, i) (innerF perm i)
        pure (ForInStep.yield (fix, insert mcr i, s.fst)) :
        Id (ForInStep (Nat × Nat × Array Bool)))
    else pure (ForInStep.yield (fix, mcr, seen))) = _
  rw [ite_eq_right (by
      intro h
      rw [hc] at h
      exact Bool.noConfusion h),
    ite_eq_left (by
      intro h
      rw [hs] at h
      exact Bool.noConfusion h)]

/-- The outer loop is `fmpermGo`. -/
private theorem forIn_outerF_eq (perm : Array Nat) (nn : Nat) :
    ∀ (l : List Nat) (fix mcr : Nat) (seen : Array Bool),
      (forIn l (fix, mcr, seen) (outerF perm nn) :
        Id (Nat × Nat × Array Bool)) =
      fmpermGo perm nn l fix mcr seen
  | [], _, _, _ => rfl
  | i :: l, fix, mcr, seen => by
    rw [List.forIn_cons, fmpermGo]
    rcases hfx : (perm[i]! == i) with _ | _
    · rw [ite_eq_right (fun h => Bool.noConfusion h)]
      rcases hsn : seen[i]! with _ | _
      · rw [outerF_unseen hfx hsn,
          ite_eq_right (fun h => Bool.noConfusion h),
          forIn_range_eq, forIn_innerF_eq]
        exact forIn_outerF_eq perm nn l _ _ _
      · rw [outerF_seen hfx hsn, ite_eq_left rfl]
        exact forIn_outerF_eq perm nn l _ _ _
    · rw [outerF_fixed hfx, ite_eq_left rfl]
      exact forIn_outerF_eq perm nn l _ _ _

/-- `fmperm` computes its structural mirror. -/
private theorem fmperm_eq_go (perm : Array Nat) (nn : Nat) :
    fmperm perm nn =
      ((fmpermGo perm nn (List.range nn) 0 0
          (Array.replicate nn false)).1,
        (fmpermGo perm nn (List.range nn) 0 0
          (Array.replicate nn false)).2.1) := by
  rw [fmperm_pinned]
  show (let s := Id.run (forIn [:nn]
      ((0 : Nat), (0 : Nat), Array.replicate nn false)
      (outerF perm nn)); (s.fst, s.snd.fst)) = _
  rw [forIn_range_eq, forIn_outerF_eq]
  rfl


/-! # Invariants of the mirrors -/

private theorem iter_succ_right (perm : Array Nat) (a v : Nat) :
    iter perm (a + 1) v = perm[iter perm a v]! := by
  rw [iter_add]
  show applyWord (List.replicate 1 perm) _ = _
  rw [List.replicate_succ, List.replicate_zero, applyWord,
    List.foldl_cons, List.foldl_nil]

private theorem elem_insert_self (s w : Nat) :
    elem (insert s w) w = true := by
  show (insert s w).testBit w = true
  rw [testBit_insert]
  simp

private theorem elem_insert_mono {s u : Nat} (w : Nat)
    (hu : elem s u = true) : elem (insert s w) u = true := by
  show (insert s w).testBit u = true
  rw [testBit_insert]
  exact (Bool.or_eq_true _ _).mpr (Or.inl hu)

private theorem elem_insert_elim {s w u : Nat}
    (hu : elem (insert s w) u = true) :
    u = w ∨ elem s u = true := by
  have : (s.testBit u || w == u) = true := by
    rw [← testBit_insert]
    exact hu
  rcases (Bool.or_eq_true _ _).mp this with h | h
  · exact Or.inr h
  · exact Or.inl ((beq_iff_eq ..).mp h).symm

private theorem markCycle_size {perm : Array Nat} {i : Nat} :
    ∀ (l : List Nat) (seen : Array Bool) (cur : Nat),
      (markCycle perm i l seen cur).1.size = seen.size
  | [], _, _ => rfl
  | x :: l, seen, cur => by
    rw [markCycle]
    rcases hc : (perm[cur]! == i) with _ | _
    · rw [ite_eq_right (fun h => Bool.noConfusion h)]
      rw [markCycle_size l, Array.size_set!]
    · rw [ite_eq_left rfl, Array.size_set!]

/-- Marks added by the cycle walk lie on the forward orbit of `i`. -/
private theorem markCycle_spec {perm : Array Nat} {i : Nat} :
    ∀ (l : List Nat) (seen : Array Bool) (cur : Nat),
      (∃ a, iter perm a i = cur) →
      ∀ w, (markCycle perm i l seen cur).1[w]! = true →
        seen[w]! = true ∨ ∃ a, iter perm a i = w
  | [], _, _, _, _, hw => Or.inl hw
  | x :: l, seen, cur, ⟨a, ha⟩, w, hw => by
    rw [markCycle] at hw
    have hset : ∀ u, (seen.set! cur true)[u]! = true →
        seen[u]! = true ∨ ∃ b, iter perm b i = u := by
      intro u hu
      rcases Decidable.em (u = cur) with rfl | hne
      · exact Or.inr ⟨a, ha⟩
      · rw [Array.getElem!_set!_ne _ _ _ _
          (fun h => hne h.symm)] at hu
        exact Or.inl hu
    rcases hc : (perm[cur]! == i) with _ | _
    · rw [ite_eq_right (by
        intro h
        rw [hc] at h
        exact Bool.noConfusion h)] at hw
      have hnext : ∃ b, iter perm b i = perm[cur]! :=
        ⟨a + 1, by rw [iter_succ_right, ha]⟩
      rcases markCycle_spec l (seen.set! cur true) perm[cur]!
          hnext w hw with hin | horb
      · exact hset w hin
      · exact Or.inr horb
    · rw [ite_eq_left hc] at hw
      exact hset w hw

/-- The seen array only records unfixed starts and their orbits. -/
private def SeenInv (perm : Array Nat) (i : Nat)
    (seen : Array Bool) : Prop :=
  ∀ w, seen[w]! = true →
    ∃ j, j < i ∧ perm[j]! ≠ j ∧ ∃ a, iter perm a j = w

/-- The outer mirror's combined invariant: `fix` holds only fixed
points, and `mcr` holds every orbit minimum. -/
private theorem fmpermGo_spec {perm : Array Nat} {nn : Nat}
    (hb : ∀ v, v < nn → perm[v]! < nn)
    (hinj : ∀ a b, a < nn → b < nn → perm[a]! = perm[b]! → a = b) :
    ∀ (k i fix mcr : Nat) (seen : Array Bool),
      i + k = nn → seen.size = nn →
      SeenInv perm i seen →
      (∀ u, elem fix u = true → u < nn ∧ perm[u]! = u) →
      (∀ v, v < i → IsOrbMin perm v → elem mcr v = true) →
      (∀ u, elem (fmpermGo perm nn (List.range' i k)
          fix mcr seen).1 u = true → u < nn ∧ perm[u]! = u) ∧
      (∀ v, v < nn → IsOrbMin perm v →
        elem (fmpermGo perm nn (List.range' i k)
          fix mcr seen).2.1 v = true)
  | 0, i, fix, mcr, seen, hik, _, _, hfix, hmcr => by
    refine ⟨fun u hu => hfix u hu, fun v hv hmin => ?_⟩
    exact hmcr v (by omega) hmin
  | k + 1, i, fix, mcr, seen, hik, hsz, hseen, hfix, hmcr => by
    rw [List.range'_succ, fmpermGo]
    have hilt : i < nn := by omega
    rcases hfx : (perm[i]! == i) with _ | _
    · rw [ite_eq_right (fun h => Bool.noConfusion h)]
      have hne : perm[i]! ≠ i := by
        intro h
        rw [(beq_iff_eq ..).mpr h] at hfx
        exact Bool.noConfusion hfx
      rcases hsn : seen[i]! with _ | _
      · rw [ite_eq_right (fun h => Bool.noConfusion h)]
        refine fmpermGo_spec hb hinj k (i + 1) _ _ _
          (by omega)
          (by rw [markCycle_size, hsz])
          ?_ hfix ?_
        · intro w hw
          rcases markCycle_spec (List.range nn) seen i
              ⟨0, rfl⟩ w hw with hin | horb
          · obtain ⟨j, hj, hjne, hreach⟩ := hseen w hin
            exact ⟨j, by omega, hjne, hreach⟩
          · exact ⟨i, by omega, hne, horb⟩
        · intro v hv hmin
          rcases Decidable.em (v = i) with rfl | hvne
          · exact elem_insert_self ..
          · exact elem_insert_mono _ (hmcr v (by omega) hmin)
      · rw [ite_eq_left rfl]
        refine fmpermGo_spec hb hinj k (i + 1) _ _ _
          (by omega) hsz
          (fun w hw => by
            obtain ⟨j, hj, hjne, hreach⟩ := hseen w hw
            exact ⟨j, by omega, hjne, hreach⟩)
          hfix ?_
        intro v hv hmin
        rcases Decidable.em (v = i) with rfl | hvne
        · exfalso
          obtain ⟨j, hj, hjne, a, ha⟩ := hseen v hsn
          obtain ⟨c, hc⟩ := iter_symm hb hinj (by omega) ha
          have := hmin c
          rw [hc] at this
          omega
        · exact hmcr v (by omega) hmin
    · rw [ite_eq_left rfl]
      have heq : perm[i]! = i := (beq_iff_eq ..).mp hfx
      refine fmpermGo_spec hb hinj k (i + 1) _ _ _
        (by omega) hsz
        (fun w hw => by
          obtain ⟨j, hj, hjne, hreach⟩ := hseen w hw
          exact ⟨j, by omega, hjne, hreach⟩)
        ?_ ?_
      · intro u hu
        rcases elem_insert_elim hu with rfl | hold
        · exact ⟨hilt, heq⟩
        · exact hfix u hold
      · intro v hv hmin
        rcases Decidable.em (v = i) with rfl | hvne
        · exact elem_insert_self ..
        · exact elem_insert_mono _ (hmcr v (by omega) hmin)

private theorem applyWord_replicate_fixed {perm : Array Nat} {u : Nat}
    (hfixed : perm[u]! = u) :
    ∀ k, applyWord (List.replicate k perm) u = u
  | 0 => rfl
  | k + 1 => by
    rw [applyWord_replicate_succ, hfixed,
      applyWord_replicate_fixed hfixed k]

/-- The spec instance at the root call of `fmperm`. -/
private theorem fmpermGo_root {perm : Array Nat} {nn : Nat}
    (hb : ∀ v, v < nn → perm[v]! < nn)
    (hinj : ∀ a b, a < nn → b < nn → perm[a]! = perm[b]! → a = b) :
    (∀ u, elem (fmpermGo perm nn (List.range nn) 0 0
        (Array.replicate nn false)).1 u = true →
      u < nn ∧ perm[u]! = u) ∧
    (∀ v, v < nn → IsOrbMin perm v →
      elem (fmpermGo perm nn (List.range nn) 0 0
        (Array.replicate nn false)).2.1 v = true) := by
  have hseen0 : SeenInv perm 0 (Array.replicate nn false) := by
    intro w hw
    rcases Decidable.em (w < nn) with hlt | hge
    · rw [getElem!_pos _ _ (by simpa using hlt),
        Array.getElem_replicate] at hw
      exact Bool.noConfusion hw
    · rw [getElem!_neg _ _ (by simpa using hge)] at hw
      exact Bool.noConfusion hw
  have hspec := fmpermGo_spec hb hinj nn 0 0 0
    (Array.replicate nn false) (by omega) (by simp) hseen0
    (fun u hu => absurd hu (by simp [elem]))
    (fun v hv _ => absurd hv (by omega))
  rw [show List.range' 0 nn = List.range nn from
    List.range_eq_range'.symm] at hspec
  exact hspec

/-- `fix` of an `fmperm` pair holds only fixed points. -/
theorem fmperm_fix {perm : Array Nat} {nn : Nat}
    (hb : ∀ v, v < nn → perm[v]! < nn)
    (hinj : ∀ a b, a < nn → b < nn → perm[a]! = perm[b]! → a = b)
    {u : Nat} (hu : elem (fmperm perm nn).1 u = true) :
    u < nn ∧ perm[u]! = u := by
  rw [fmperm_eq_go] at hu
  exact (fmpermGo_root hb hinj).1 u hu

/-- A vertex left out of an `fmperm` pair's `mcr` is carried strictly
down by a forward power of the generator. -/
theorem fmperm_mcr {perm : Array Nat} {nn : Nat}
    (hb : ∀ v, v < nn → perm[v]! < nn)
    (hinj : ∀ a b, a < nn → b < nn → perm[a]! = perm[b]! → a = b)
    {v : Nat} (hv : v < nn)
    (hmcr : elem (fmperm perm nn).2 v = false) :
    ∃ k, applyWord (List.replicate k perm) v < v := by
  refine Classical.byContradiction fun hcon => ?_
  have hmin : IsOrbMin perm v := by
    intro k
    have h' : ¬ applyWord (List.replicate k perm) v < v :=
      fun hlt => hcon ⟨k, hlt⟩
    show v ≤ applyWord (List.replicate k perm) v
    omega
  have hmem := (fmpermGo_root hb hinj).2 v hv hmin
  rw [fmperm_eq_go] at hmcr
  have hmcr' : elem (fmpermGo perm nn (List.range nn) 0 0
      (Array.replicate nn false)).2.1 v = false := hmcr
  rw [hmem] at hmcr'
  exact Bool.noConfusion hmcr'

/-- The `fmperm` pair of a checked, cell-stabilizing generator reads
validly at the node: the realizers are the generator's forward
powers. -/
theorem pairOk_fmperm {g ptn lab perm : Array Nat} {level : Nat}
    (hbg : ∀ v, v < n → g[v]! < 2 ^ n)
    (hok : LabOk lab n) (hs : lab.size = n) (hsp : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hca : checkAutom g perm n = true)
    (hstab : CellStab ptn level lab perm) :
    PairOk g ptn lab level n (fmperm perm n).1 (fmperm perm n).2 := by
  have hbp : ∀ v, v < n → perm[v]! < n := checkAutom_bound hca
  have hinj : ∀ a b, a < n → b < n → perm[a]! = perm[b]! → a = b :=
    checkAutom_inj hca
  intro v hv hmcr
  obtain ⟨k, hk⟩ := fmperm_mcr hbp hinj hv hmcr
  obtain ⟨hcaw, hstabw, hact⟩ := wordPerm_spec hbg hok hsp hs hend
    (S := [perm])
    (fun γ hγ => by rw [List.mem_singleton.mp hγ]; exact hca)
    (fun γ hγ => by rw [List.mem_singleton.mp hγ]; exact hstab)
    (List.replicate k perm)
    (fun γ hγ => List.mem_singleton.mpr
      (List.eq_of_mem_replicate hγ))
  refine ⟨wordPerm n (List.replicate k perm), hcaw, ?_, hstabw, ?_⟩
  · intro u hu hfu
    have hfixed := (fmperm_fix hbp hinj hfu).2
    rw [hact u hu]
    exact applyWord_replicate_fixed hfixed k
  · rw [hact v hv]
    exact hk


/-! # The implicit pairs: `fmptn` of a cheapautom partition

The pair recorded without a scan describes the partition at the
cheapautom level: `fix` holds the singleton-cell vertices, and a
vertex left out of `mcr` has a strictly smaller cellmate. The
realizing automorphisms are the small-cell subtree theorem's, so
`pairOk_fmptn` takes them as a hypothesis in exactly that shape.
-/

/-- The inner minimum scan of `fmptn`, structurally. -/
private def minScan (lab : Array Nat) : List Nat → Nat → Nat
  | [], m => m
  | i :: rest, m =>
    if lab[i]! < m then minScan lab rest lab[i]!
    else minScan lab rest m

/-- The outer loop of `fmptn`, structurally. -/
private def fmptnGo (lab : Array Nat) (nn : Nat) :
    List (Nat × Nat) → Nat → Nat → Nat × Nat
  | [], fix, mcr => (fix, mcr)
  | (c1, c2) :: rest, fix, mcr =>
    if c1 == c2 then
      fmptnGo lab nn rest (insert fix lab[c1]!) (insert mcr lab[c1]!)
    else
      fmptnGo lab nn rest fix (insert mcr
        (minScan lab (List.range' (c1 + 1) (c2 + 1 - (c1 + 1)))
          lab[c1]!))

/-- The pinned inner body of `fmptn`. -/
private def minF (lab : Array Nat) :
    Nat → Nat → Id (ForInStep Nat) :=
  fun i __s =>
    have lmin := __s
    if lab[i]! < lmin then
      have lmin := lab[i]!
      pure (ForInStep.yield lmin)
    else pure (ForInStep.yield lmin)

/-- The pinned outer body of `fmptn`. -/
private def cellF (lab : Array Nat) :
    Nat × Nat → Nat × Nat → Id (ForInStep (Nat × Nat)) :=
  fun x __s =>
    have fix := __s.fst
    have mcr := __s.snd
    match x with
    | (c1, c2) =>
      if (c1 == c2) = true then
        have fix := insert fix lab[c1]!
        have mcr := insert mcr lab[c1]!
        pure (ForInStep.yield (fix, mcr))
      else
        have lmin := lab[c1]!
        do
        let __s ← forIn [c1 + 1 : c2 + 1] lmin (minF lab)
        have lmin : Nat := __s
        have mcr : Nat := insert mcr lmin
        pure (ForInStep.yield (fix, mcr))

private theorem fmptn_pinned (lab ptn : Array Nat) (level nn : Nat) :
    fmptn lab ptn level nn =
      (do
        let s ← forIn (cells ptn level nn) ((0 : Nat), (0 : Nat))
          (cellF lab)
        pure (s.fst, s.snd) : Id (Nat × Nat)).run := rfl

private theorem forIn_range_eq' {β : Type} (a b : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [a:b] init f : Id β) =
      forIn (List.range' a (b - a)) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [a:b].start [a:b].size [a:b].step
      = List.range' a (b - a) := by
    show List.range' a ((b - a + 1 - 1) / 1) 1 = _
    rw [Nat.add_sub_cancel, Nat.div_one]
  rw [hrange]

private theorem minF_lt {lab : Array Nat} {i m : Nat}
    (hc : lab[i]! < m) :
    minF lab i m = pure (ForInStep.yield lab[i]!) := by
  show (if lab[i]! < m then pure (ForInStep.yield lab[i]!)
    else pure (ForInStep.yield m)) = _
  rw [ite_eq_left hc]

private theorem minF_ge {lab : Array Nat} {i m : Nat}
    (hc : ¬ lab[i]! < m) :
    minF lab i m = pure (ForInStep.yield m) := by
  show (if lab[i]! < m then pure (ForInStep.yield lab[i]!)
    else pure (ForInStep.yield m)) = _
  rw [ite_eq_right hc]

/-- The inner loop is `minScan`. -/
private theorem forIn_minF_eq (lab : Array Nat) :
    ∀ (l : List Nat) (m : Nat),
      (forIn l m (minF lab) : Id Nat) = minScan lab l m
  | [], _ => rfl
  | i :: l, m => by
    rw [List.forIn_cons, minScan]
    rcases Decidable.em (lab[i]! < m) with hc | hc
    · rw [minF_lt hc, ite_eq_left hc]
      exact forIn_minF_eq lab l _
    · rw [minF_ge hc, ite_eq_right hc]
      exact forIn_minF_eq lab l _

private theorem cellF_single {lab : Array Nat} {c1 c2 fix mcr : Nat}
    (hc : (c1 == c2) = true) :
    cellF lab (c1, c2) (fix, mcr) =
      pure (ForInStep.yield
        (insert fix lab[c1]!, insert mcr lab[c1]!)) := by
  show (if (c1 == c2) = true then
      pure (ForInStep.yield
        (insert fix lab[c1]!, insert mcr lab[c1]!))
    else _) = _
  rw [ite_eq_left hc]

private theorem cellF_multi {lab : Array Nat} {c1 c2 fix mcr : Nat}
    (hc : (c1 == c2) = false) :
    cellF lab (c1, c2) (fix, mcr) =
      (do
        let s ← forIn [c1 + 1 : c2 + 1] lab[c1]! (minF lab)
        pure (ForInStep.yield (fix, insert mcr s)) :
        Id (ForInStep (Nat × Nat))) := by
  show (if (c1 == c2) = true then
      pure (ForInStep.yield
        (insert fix lab[c1]!, insert mcr lab[c1]!))
    else
      (do
        let s ← forIn [c1 + 1 : c2 + 1] lab[c1]! (minF lab)
        pure (ForInStep.yield (fix, insert mcr s)) :
        Id (ForInStep (Nat × Nat)))) = _
  rw [ite_eq_right (by
    intro h
    rw [hc] at h
    exact Bool.noConfusion h)]

/-- The outer loop is `fmptnGo`. -/
private theorem forIn_cellF_eq (lab : Array Nat) (nn : Nat) :
    ∀ (l : List (Nat × Nat)) (fix mcr : Nat),
      (forIn l (fix, mcr) (cellF lab) : Id (Nat × Nat)) =
      fmptnGo lab nn l fix mcr
  | [], _, _ => rfl
  | (c1, c2) :: l, fix, mcr => by
    rw [List.forIn_cons, fmptnGo]
    rcases hc : (c1 == c2) with _ | _
    · rw [cellF_multi hc, ite_eq_right (fun h => Bool.noConfusion h),
        forIn_range_eq', forIn_minF_eq]
      exact forIn_cellF_eq lab nn l _ _
    · rw [cellF_single hc, ite_eq_left rfl]
      exact forIn_cellF_eq lab nn l _ _

/-- `fmptn` computes its structural mirror. -/
private theorem fmptn_eq_go (lab ptn : Array Nat) (level nn : Nat) :
    fmptn lab ptn level nn =
      fmptnGo lab nn (cells ptn level nn) 0 0 := by
  rw [fmptn_pinned]
  show (let s := Id.run (forIn (cells ptn level nn)
      ((0 : Nat), (0 : Nat)) (cellF lab)); (s.fst, s.snd)) = _
  rw [forIn_cellF_eq lab nn]
  rfl

/-- The structural minimum scan is the ordinary fold over the values at
the listed positions. -/
private theorem minScan_eq_foldl (lab : Array Nat) :
    ∀ (l : List Nat) (m : Nat),
      minScan lab l m = (l.map fun i => lab[i]!).foldl Nat.min m
  | [], _ => rfl
  | i :: l, m => by
    rw [minScan, List.map_cons, List.foldl_cons]
    rcases Decidable.em (lab[i]! < m) with h | h
    · rw [ite_eq_left h, minScan_eq_foldl]
      rw [show m.min lab[i]! = lab[i]! by
        rw [Nat.min_eq_min]
        omega]
    · rw [ite_eq_right h, minScan_eq_foldl]
      rw [show m.min lab[i]! = m by
        rw [Nat.min_eq_min]
        omega]

/-- The minimum inserted for a cell is its permutation-invariant list
minimum. -/
private theorem minScan_cell {lab : Array Nat} {c1 len : Nat} :
    minScan lab (List.range' (c1 + 1) len) lab[c1]! =
      (segN lab c1 (len + 1)).foldl Nat.min
        ((segN lab c1 (len + 1)).headD 0) := by
  rw [segN_cons, minScan_eq_foldl]
  simp only [List.headD_cons, List.foldl_cons, Nat.min_self]
  congr 1
  rw [segN]
  simp only [List.range'_eq_map_range, List.map_map]
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply]

private theorem fmptnGo_cellsPerm {lab lab' ptn : Array Nat} {level nn : Nat}
    (hperm : cellsPerm ptn level lab lab') :
    ∀ (cs : List (Nat × Nat)) (fix mcr : Nat),
      (∀ p ∈ cs, IsCell ptn level p.1 (p.2 + 1 - p.1)) →
      fmptnGo lab nn cs fix mcr = fmptnGo lab' nn cs fix mcr
  | [], _, _, _ => rfl
  | (c1, c2) :: rest, fix, mcr, hcells => by
      rw [fmptnGo, fmptnGo]
      have hcell := hcells (c1, c2) (by simp)
      rcases hc : (c1 == c2) with _ | _
      · rw [ite_eq_right (fun h => Bool.noConfusion h),
          ite_eq_right (fun h => Bool.noConfusion h)]
        have hlen : c2 + 1 - c1 = (c2 - c1) + 1 := by
          have := hcell.1
          omega
        have hp := hperm c1 (c2 + 1 - c1) hcell
        rw [hlen] at hp
        have hmin := foldl_min_headD_perm hp
        rw [← minScan_cell, ← minScan_cell] at hmin
        have hrange : c2 + 1 - (c1 + 1) = c2 - c1 := by omega
        rw [hrange, hmin]
        exact fmptnGo_cellsPerm hperm rest fix _
          (fun p hp => hcells p (by simp [hp]))
      · rw [ite_eq_left rfl, ite_eq_left rfl]
        have heq : c1 = c2 := (beq_iff_eq ..).mp hc
        subst c2
        have hlab := cellsPerm_singleton hperm (by simpa using hcell)
        rw [hlab]
        exact fmptnGo_cellsPerm hperm rest _ _
          (fun p hp => hcells p (by simp [hp]))

/-- `fmptn` is unchanged when the two partitions list the same cells and
the two labellings have the same contents in each such cell. -/
theorem fmptn_congr {lab lab' ptn ptn' : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    (hcells : cells ptn level nn = cells ptn' level nn)
    (hperm : cellsPerm ptn level lab lab') :
    fmptn lab ptn level nn = fmptn lab' ptn' level nn := by
  rw [fmptn_eq_go, fmptn_eq_go]
  rw [← hcells]
  exact fmptnGo_cellsPerm hperm _ 0 0 (cells_isCell hnn hend)

/-- `fmptn` is unchanged when vertices are permuted within every cell
at the level it reads. -/
theorem fmptn_cellsPerm {lab lab' ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    (hperm : cellsPerm ptn level lab lab') :
    fmptn lab ptn level nn = fmptn lab' ptn level nn :=
  fmptn_congr hnn hend rfl hperm

/-- A quartet receipt preserves the implicit cheap-automorphism pair at
its frozen boundary. -/
theorem SearchOut.fmptn {G : Colored n k} {level nn : Nat}
    {st out : SearchSt} (h : SearchOut G level level st out)
    (hnn : nn ≤ st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    fmptn out.lab out.ptn level nn = fmptn st.lab st.ptn level nn :=
  (fmptn_congr hnn hend (cells_eq_of_low h.ptnSize h.low).symm h.perm).symm

/-- The minimum scan attains a window value at or below its seed. -/
private theorem minScan_spec {lab : Array Nat} :
    ∀ (l : List Nat) (m : Nat),
      (minScan lab l m = m ∨
        ∃ i ∈ l, lab[i]! = minScan lab l m) ∧
      minScan lab l m ≤ m ∧
      ∀ i ∈ l, minScan lab l m ≤ lab[i]!
  | [], m => ⟨Or.inl rfl, Nat.le_refl m, fun i hi => absurd hi (by simp)⟩
  | i :: l, m => by
    rw [minScan]
    rcases Decidable.em (lab[i]! < m) with hc | hc
    · rw [ite_eq_left hc]
      obtain ⟨hmem, hle, hall⟩ := minScan_spec (lab := lab) l lab[i]!
      refine ⟨?_, by omega, ?_⟩
      · rcases hmem with heq | ⟨j, hj, hjeq⟩
        · exact Or.inr ⟨i, List.mem_cons_self .., heq.symm⟩
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hjeq⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hjl
        · exact hle
        · exact hall j hjl
    · rw [ite_eq_right hc]
      obtain ⟨hmem, hle, hall⟩ := minScan_spec (lab := lab) l m
      refine ⟨?_, hle, ?_⟩
      · rcases hmem with heq | ⟨j, hj, hjeq⟩
        · exact Or.inl heq
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hjeq⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hjl
        · omega
        · exact hall j hjl

/-- `mcr` bits only accumulate through the outer mirror. -/
private theorem fmptnGo_mcr_mono {lab : Array Nat} {nn : Nat} :
    ∀ (l : List (Nat × Nat)) (fix mcr x : Nat),
      elem mcr x = true →
      elem (fmptnGo lab nn l fix mcr).2 x = true
  | [], _, _, _, hx => hx
  | (c1, c2) :: l, fix, mcr, x, hx => by
    rw [fmptnGo]
    rcases hc : (c1 == c2) with _ | _
    · rw [ite_eq_right (fun h => Bool.noConfusion h)]
      exact fmptnGo_mcr_mono l _ _ _ (elem_insert_mono _ hx)
    · rw [ite_eq_left rfl]
      exact fmptnGo_mcr_mono l _ _ _ (elem_insert_mono _ hx)

/-- `fix` bits of the outer mirror come from singleton cells. -/
private theorem fmptnGo_fix {lab : Array Nat} {nn : Nat} :
    ∀ (l : List (Nat × Nat)) (fix mcr u : Nat),
      elem (fmptnGo lab nn l fix mcr).1 u = true →
      elem fix u = true ∨ ∃ c, (c, c) ∈ l ∧ lab[c]! = u
  | [], _, _, _, hu => Or.inl hu
  | (c1, c2) :: l, fix, mcr, u, hu => by
    rw [fmptnGo] at hu
    rcases hc : (c1 == c2) with _ | _
    · rw [hc, ite_eq_right (fun h => Bool.noConfusion h)] at hu
      rcases fmptnGo_fix l _ _ _ hu with hold | ⟨c, hcl, hceq⟩
      · exact Or.inl hold
      · exact Or.inr ⟨c, List.mem_cons_of_mem _ hcl, hceq⟩
    · rw [hc, ite_eq_left rfl] at hu
      rcases fmptnGo_fix l _ _ _ hu with hold | ⟨c, hcl, hceq⟩
      · rcases elem_insert_elim hold with rfl | hfx
        · have heq12 : c1 = c2 := (beq_iff_eq ..).mp hc
          subst heq12
          exact Or.inr ⟨c1, List.mem_cons_self .., rfl⟩
        · exact Or.inl hfx
      · exact Or.inr ⟨c, List.mem_cons_of_mem _ hcl, hceq⟩

/-- Every cell of the list deposits its window minimum in `mcr`. -/
private theorem fmptnGo_cell {lab : Array Nat} {nn : Nat} :
    ∀ (l : List (Nat × Nat)) (fix mcr c1 c2 : Nat),
      (c1, c2) ∈ l → c1 ≤ c2 →
      ∃ m, elem (fmptnGo lab nn l fix mcr).2 m = true ∧
        (∃ q, c1 ≤ q ∧ q ≤ c2 ∧ lab[q]! = m) ∧
        (∀ q, c1 ≤ q → q ≤ c2 → m ≤ lab[q]!)
  | [], _, _, _, _, hmem, _ => absurd hmem (by simp)
  | (a1, a2) :: l, fix, mcr, c1, c2, hmem, hord => by
    rw [fmptnGo]
    rcases List.mem_cons.mp hmem with heq | htail
    · have ha1 : a1 = c1 := (congrArg Prod.fst heq).symm
      have ha2 : a2 = c2 := (congrArg Prod.snd heq).symm
      subst ha1
      subst ha2
      rcases hc : (a1 == a2) with _ | _
      · rw [ite_eq_right (fun h => Bool.noConfusion h)]
        obtain ⟨hmem', hle, hall⟩ :=
          minScan_spec (lab := lab)
            (List.range' (a1 + 1) (a2 + 1 - (a1 + 1))) lab[a1]!
        refine ⟨minScan lab
            (List.range' (a1 + 1) (a2 + 1 - (a1 + 1))) lab[a1]!,
          fmptnGo_mcr_mono l _ _ _ (elem_insert_self ..), ?_, ?_⟩
        · rcases hmem' with heq' | ⟨j, hj, hjeq⟩
          · exact ⟨a1, Nat.le_refl _, hord, heq'.symm⟩
          · have hjr := List.mem_range'_1.mp hj
            exact ⟨j, by omega, by omega, hjeq⟩
        · intro q hq1 hq2
          rcases Decidable.em (q = a1) with rfl | hne
          · exact hle
          · exact hall q (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      · rw [ite_eq_left rfl]
        refine ⟨lab[a1]!,
          fmptnGo_mcr_mono l _ _ _ (elem_insert_self ..),
          ⟨a1, Nat.le_refl _, hord, rfl⟩, ?_⟩
        intro q hq1 hq2
        have heq12 : a1 = a2 := (beq_iff_eq ..).mp hc
        have : q = a1 := by omega
        rw [this]
        exact Nat.le_refl _
    · rcases hc : (a1 == a2) with _ | _
      · rw [ite_eq_right (fun h => Bool.noConfusion h)]
        exact fmptnGo_cell l _ _ _ _ htail hord
      · rw [ite_eq_left rfl]
        exact fmptnGo_cell l _ _ _ _ htail hord

/-- `fix` of an `fmptn` pair holds only singleton-cell vertices. -/
theorem fmptn_fix {lab ptn : Array Nat} {level nn u : Nat}
    (hu : elem (fmptn lab ptn level nn).1 u = true) :
    ∃ c, (c, c) ∈ cells ptn level nn ∧ lab[c]! = u := by
  rw [fmptn_eq_go] at hu
  rcases fmptnGo_fix _ _ _ _ hu with h0 | h
  · exact absurd h0 (by simp [elem])
  · exact h

/-- A vertex left out of an `fmptn` pair's `mcr` has a strictly
smaller cellmate. -/
theorem fmptn_mcr {lab ptn : Array Nat} {level nn c1 c2 p v : Nat}
    (hcell : (c1, c2) ∈ cells ptn level nn)
    (hp1 : c1 ≤ p) (hp2 : p ≤ c2) (hpv : lab[p]! = v)
    (hmcr : elem (fmptn lab ptn level nn).2 v = false) :
    ∃ q, c1 ≤ q ∧ q ≤ c2 ∧ lab[q]! < v := by
  obtain ⟨m, hmem, ⟨q, hq1, hq2, hqm⟩, hall⟩ :=
    fmptnGo_cell (nn := nn) (lab := lab)
      (cells ptn level nn) 0 0 c1 c2 hcell
      (cells_le (c1, c2) hcell)
  rw [← fmptn_eq_go] at hmem
  have hmv : m ≤ v := by
    rw [← hpv]
    exact hall p hp1 hp2
  rcases Nat.lt_or_ge m v with hlt | hge
  · exact ⟨q, hq1, hq2, by omega⟩
  · have : m = v := by omega
    rw [this] at hmem
    rw [hmem] at hmcr
    exact Bool.noConfusion hmcr

/-- The `fmptn` pair reads validly given realizers for every
non-minimal cell member: the small-cell subtree theorem's interface.
`hreal` receives the vertex, its window, and a strictly smaller
cellmate, and returns an automorphism fixing the pair's `fix` set. -/
theorem pairOk_fmptn {g ptn lab labT ptnT : Array Nat}
    {level lvlT nn : Nat}
    (hcover : ∀ v, v < nn → ∃ p c1 c2,
      (c1, c2) ∈ cells ptnT lvlT nn ∧ c1 ≤ p ∧ p ≤ c2 ∧
        labT[p]! = v)
    (hreal : ∀ v c1 c2, v < nn →
      (c1, c2) ∈ cells ptnT lvlT nn →
      (∃ p, c1 ≤ p ∧ p ≤ c2 ∧ labT[p]! = v) →
      (∃ q, c1 ≤ q ∧ q ≤ c2 ∧ labT[q]! < v) →
      ∃ γ : Array Nat, checkAutom g γ nn = true ∧
        (∀ u, u < nn →
          elem (fmptn labT ptnT lvlT nn).1 u = true → γ[u]! = u) ∧
        CellStab ptn level lab γ ∧ γ[v]! < v) :
    PairOk g ptn lab level nn (fmptn labT ptnT lvlT nn).1
      (fmptn labT ptnT lvlT nn).2 := by
  intro v hv hmcr
  obtain ⟨p, c1, c2, hcell, hp1, hp2, hpv⟩ := hcover v hv
  obtain ⟨q, hq1, hq2, hqlt⟩ := fmptn_mcr hcell hp1 hp2 hpv hmcr
  exact hreal v c1 c2 hv hcell ⟨p, hp1, hp2, hpv⟩ ⟨q, hq1, hq2, hqlt⟩

end Hex.GraphIso.Nauty
