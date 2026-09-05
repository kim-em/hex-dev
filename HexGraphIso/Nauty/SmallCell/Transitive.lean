/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.FourCell
import all HexGraphIso.Nauty.Equitable.Basic
public import HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Step
public import HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.SmallCell.Leaves

public section

/-!
`stabilizer_transitive`: for an equitable partition satisfying
`cheapautom`, the cell stabilizer in the automorphism group acts
transitively on every cell. This is what justifies the `(fix, mcr)`
pair nauty reads off the partition at a `noncheaplevel` node
(`pairOk_fmptn_of_subtree` in `Correct/State/Ledger`).

A passing guard leaves the node in one of two shapes, and either one
yields the flip data a deviation consumes. `stabilizer_transitive`
reads a pair or triple target off the first-branch shape, and a target
of any size at most five off a defect of at most four, where the exotic
analogues apply. The all-leaves theorem `descPath_leafRows_all` then
states that every leaf below such a node realizes an automorphism with
the first leaf: the induction over a target-position path recurses on
equal choices and glues one deviation at a differing choice, and the
imperative descents below apply it. That is what admits a code-1 exit
with no `isautom` scan.

This module sits above the exotic layer because that is where the
defect-four flip data is proved. Everything else the induction needs
lives in `SmallCell/Leaves`.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # Flip data from the node shape -/

/-- Flip data at any cell of a node satisfying the invariant. The
first-branch shape names a pair or triple target; a defect of at most
four bounds every cell at five positions and hands the target to the
exotic analogues. -/
theorem stabilizer_transitive {st : RefineSt n} {level tc te oU oV : Nat}
    (hS : SubtreeOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : (tc, te) ∈ cells st.ptn level n) (hne : tc < te)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hone : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  rcases hS.shape with hsmall | hdef
  · rcases hsmall _ hcell with hsz2 | ⟨hsz3, huniq⟩
    · -- a pair target
      have hsz2' : te + 1 - tc ≤ 2 := hsz2
      have he : te = tc + 1 := by omega
      subst he
      have hOdd : ∀ q ∈ cells st.ptn level n,
          q.2 ≠ q.1 + 1 → (q.2 + 1 - q.1) % 2 = 1 := by
        intro q hq hqne
        have hqle := cells_le _ hq
        rcases hsmall _ hq with h2 | ⟨h3, -⟩
        · have h1 : q.2 + 1 - q.1 = 1 := by omega
          omega
        · omega
      exact pair_flip_data hS.it hgsz hsymm hloop hS.eqt
        hcell hOdd (by omega) (by omega) hone
    · -- the triple target
      have hsz3' : te + 1 - tc = 3 := hsz3
      have he : te = tc + 2 := by omega
      subst he
      have hsmall' : ∀ q ∈ cells st.ptn level n,
          q ≠ (tc, tc + 2) → q.2 + 1 - q.1 ≤ 2 := by
        intro q hq hqne
        rcases hsmall _ hq with h2 | ⟨h3, -⟩
        · exact h2
        · exact absurd (huniq q hq h3) hqne
      exact triple_flip_data hS.it hgsz hsymm hloop hS.eqt
        hcell hsmall' (by omega) (by omega) hone
  · -- the exotic shapes
    exact defect4_flip_data hS.it hgsz hsymm hloop hS.eqt hdef
      hcell hoU hoV hone

/-! # All leaves below a cheapautom node have equal rows -/

/-- Any two discrete descents below a first-branch node choosing the
same target cells have equal leaf rows: equal choices recurse, and a
differing choice is one pair or triple deviation glued to the
transported deeper path. -/
theorem descPath_leafRows_all
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (tcs : List Nat) :
    ∀ {level : Nat} {st : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
      {level₁ level₂ : Nat} {U V : RefineSt n},
      SubtreeOk ctx level st →
      DescPath ctx level st p₁ level₁ U →
      p₁.map Prod.fst = tcs →
      (∀ q, q < n → U.ptn[q]! ≤ level₁) →
      DescPath ctx level st p₂ level₂ V →
      p₂.map Prod.fst = tcs →
      (∀ q, q < n → V.ptn[q]! ≤ level₂) →
      level₂ = level₁ ∧ leafRows ctx V.lab = leafRows ctx U.lab := by
  induction tcs with
  | nil =>
    intro level st p₁ p₂ level₁ level₂ U V hS hU hp₁ hUd hV hp₂ hVd
    have h1 : p₁ = [] := by
      cases p₁ with
      | nil => rfl
      | cons a l => simp at hp₁
    have h2 : p₂ = [] := by
      cases p₂ with
      | nil => rfl
      | cons a l => simp at hp₂
    subst h1
    subst h2
    obtain ⟨hl₁, hU'⟩ := descPath_nil hU
    obtain ⟨hl₂, hV'⟩ := descPath_nil hV
    subst hU'
    subst hV'
    exact ⟨by omega, rfl⟩
  | cons tc tcs' ih =>
    intro level st p₁ p₂ level₁ level₂ U V hS hU hp₁ hUd hV hp₂ hVd
    cases p₁ with
    | nil => exact absurd hp₁ (by simp)
    | cons h₁ tl₁ =>
    cases p₂ with
    | nil => exact absurd hp₂ (by simp)
    | cons h₂ tl₂ =>
    obtain ⟨a₁, o₁⟩ := h₁
    obtain ⟨a₂, o₂⟩ := h₂
    rw [List.map_cons] at hp₁ hp₂
    injection hp₁ with hh₁ ht₁
    injection hp₂ with hh₂ ht₂
    have ha₁ : tc = a₁ := hh₁.symm
    subst ha₁
    have ha₂ : tc = a₂ := hh₂.symm
    subst ha₂
    cases hU with
    | step _ e₁ _ hlvl hcell₁ hne₁ ho₁ htail₁ =>
    cases hV with
    | step _ e₂ _ hlvl₂ hcell₂ hne₂ ho₂ htail₂ =>
    have hpsz := hS.it.ok.ptnSize
    have hend := hS.it.ok.ptnEnd
    have hee : e₁ = e₂ := cells_eq_of_start (by omega) hend
      hcell₁ hcell₂
    subst hee
    rcases Decidable.em (st.lab[tc + o₁]! = st.lab[tc + o₂]!) with
      hval | hval
    · -- the same child: recurse directly
      rw [← hval] at htail₂
      exact ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₁)
        htail₁ ht₁ hUd htail₂ ht₂ hVd
    · -- a deviation at this level, by the target's size
      have hflip := stabilizer_transitive hS hgsz hsymm hloop
        hcell₁ hne₁ ho₁ ho₂ (fun h => hval (by rw [h]))
      obtain ⟨σ, hgm, hspσ, hvv⟩ := hflip
      obtain ⟨W, qW, hdescW, hqW, hlrW, hptnW⟩ :=
        descPath_deviation_self hS.it hlvl hgm hspσ hcell₁ hne₁
          ho₁ ho₂ hvv htail₁ hUd
      have hWd : ∀ q, q < n → W.ptn[q]! ≤ level₁ := by
        intro q hq
        rw [hptnW]
        exact hUd q hq
      obtain ⟨hlev, hlr₂⟩ :=
        ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₂)
          hdescW (by rw [hqW, ht₁]) hWd htail₂ ht₂ hVd
      exact ⟨hlev, hlr₂.trans hlrW⟩

end Hex.GraphIso.Nauty

/-!
The imperative tie and the code-1 assembly.

The search's child loops perform `breakout` at the parent and then the
child node's `refine`. That composite is exactly `childSt`
(`childSt_eq_search_step`), and each surviving target-cell vertex is a
window member of the target cell (`maketargetcell_mem`), so an
imperative descent below a node is a `DescPath` step by step. Both
children of one imperative node use the same `maketargetcell` result,
so the first-path leaf and a code-1-tested leaf below the greatest
common ancestor are same-target descents, and
`descPath_leafRows_all` gives them equal leaf rows
(`leafRows_eq_of_descPaths`). The admitted scatter then passes
`checkAutom` through `checkAutom_scatter_of_leafRows_eq`
(`checkAutom_scatter_of_descPaths`).

`subtreeOk_of_cheapautom` establishes the node invariant at the
ancestor from the guard alone, with no residual hypothesis: the two
branches of `cheapautom_iff` are exactly the two disjuncts of
`NodeShape` (`cheapautom_shape_or_exotic`). The second branch, a
defect of at most four with a cell of size four or five or with two
triples, keeps its own shape rather than being forced into the first,
which it need not have. `stabilizer_transitive` proves that case
from the defect-four flip analogues (`SmallCell/FourCell`).

These theorems consume four run-level facts: the two descents from the
ancestor with equal target paths, equitability at the ancestor, the
boundary count at the ancestor, and the guard having held there. They
are exactly the bookkeeping the domination induction carries
(`gcaFirst`, `eqlevFirst`, `firsttc`, `noncheaplevel`), which
discharges them at `processnode`'s admission event.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # The imperative step is `childSt` -/

/-- The search's child loops perform `breakout` at the parent and then
the child node's `refine` on the returned labelling, split partition,
and singleton active set. That composite is `childSt` of the parent's
post-refine state. -/
theorem childSt_eq_search_step (r : RefineSt n) (level tc tv : Nat) :
    refine ctx (level + 1)
      (breakout n r.lab r.ptn (level + 1) tc tv).1
      (breakout n r.lab r.ptn (level + 1) tc tv).2.1
      (breakout n r.lab r.ptn (level + 1) tc tv).2.2
      (r.numcells + 1) =
    childSt ctx level r tc tv := rfl

/-- A surviving target-cell vertex is a window member: any vertex of
the cell set `maketargetcell` returns sits at some offset of the
target cell, in the shape a `DescPath` step consumes. -/
theorem maketargetcell_mem {r : RefineSt n} {level tcLevel : Nat}
    {hint : Int} {tcPos size tv : Nat} {cellSet : VSet n}
    (hn1 : 1 ≤ level) (hsz : r.ptn.size = n)
    (hend : r.ptn[r.ptn.size - 1]! ≤ level)
    (hlive : bcount r.ptn level n < n)
    (hmk : maketargetcell ctx r.lab r.ptn level tcLevel hint =
      (tcPos, cellSet, size))
    (htv : cellSet.mem tv = true) :
    ∃ e o, (tcPos, e) ∈ cells r.ptn level n ∧ tcPos < e ∧
      o ≤ e - tcPos ∧ r.lab[tcPos + o]! = tv := by
  obtain ⟨tc, len, hmk', hic, hlen2, hbd⟩ :=
    maketargetcell_open (lab := r.lab) (tcLevel := tcLevel)
      (hint := hint) hn1 hsz hend hlive
  rw [hmk] at hmk'
  injection hmk' with h1 h23
  injection h23 with h2 h3
  subst h1
  subst h2
  subst h3
  have hmem : tv ∈ segN r.lab tcPos (tcPos + size - 1 + 1 - tcPos) :=
    (mem_worksetOf_iff.mp htv).2
  obtain ⟨o, ho, hov⟩ := mem_segN_iff.mp hmem
  refine ⟨tcPos + size - 1, o,
    mem_cells_of_isCell (by omega) hend hic (by omega) (by omega),
    by omega, by omega, hov⟩

/-! # The node shape from the guard -/

/-- A passing guard gives the first-branch shape or the exotic
defect-at-most-four configuration: a cell of size four or five, or two
triples. The defect-four flip analogues discharge the second
disjunct. -/
theorem cheapautom_shape_or_exotic {ptn : Array Nat} {level : Nat}
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hch : cheapautom ptn level n = true) :
    SmallShape n level ptn ∨
      n - (cells ptn level n).length ≤ 4 := by
  rcases (cheapautom_iff hps hend).mp hch with hb1 | hb4
  · refine Or.inl fun q hq => ?_
    rcases cells_shape_of_defect_le hps hend hb1 q hq with
      h1 | h2 | h3
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr h3
  · exact Or.inr hb4

/-- The node invariant at a guard-passing node. The guard's two
branches are exactly the invariant's two shapes, so nothing is left
over: a defect-four node keeps its own shape rather than being forced
into the first-branch one, which it need not have. -/
theorem subtreeOk_of_cheapautom {r : RefineSt n} {level : Nat}
    (hIt : IterOk ctx level r)
    (heqt : Equitable ctx level r.lab r.ptn)
    (hacc : bcount r.ptn level n = r.numcells)
    (hch : cheapautom r.ptn level n = true) :
    SubtreeOk ctx level r :=
  ⟨hIt, heqt, hacc,
    cheapautom_shape_or_exotic hIt.ok.ptnSize hIt.ok.ptnEnd hch⟩

/-! # The assembly: rows equality and `checkAutom` for the code-1
scatter -/

/-- The tie's central consequence: two discrete same-target descents
below a first-branch node end with equal leaf rows. The run-level
bookkeeping (`gcaFirst`, `eqlevFirst`, `firsttc`) supplies the two
descents with the same target path; this theorem turns them into the
rows equality the admission exits consume. -/
theorem leafRows_eq_of_descPaths
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {r : RefineSt n} {level : Nat} (hS : SubtreeOk ctx level r)
    {p₁ p₂ : List (Nat × Nat)} {level₁ level₂ : Nat} {U V : RefineSt n}
    (hU : DescPath ctx level r p₁ level₁ U)
    (hV : DescPath ctx level r p₂ level₂ V)
    (htcs : p₂.map Prod.fst = p₁.map Prod.fst)
    (hUd : ∀ q, q < n → U.ptn[q]! ≤ level₁)
    (hVd : ∀ q, q < n → V.ptn[q]! ≤ level₂) :
    leafRows ctx V.lab = leafRows ctx U.lab :=
  (descPath_leafRows_all hgsz hsymm hloop (p₁.map Prod.fst)
    hS hU rfl hUd hV htcs hVd).2

/-- The code-1 admission is a checked automorphism: the scatter
of the second descent's leaf labelling over the first's passes
`checkAutom`, with no `isautom` scan. -/
theorem checkAutom_scatter_of_descPaths
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {r : RefineSt n} {level : Nat} (hS : SubtreeOk ctx level r)
    {p₁ p₂ : List (Nat × Nat)} {level₁ level₂ : Nat} {U V : RefineSt n}
    (hU : DescPath ctx level r p₁ level₁ U)
    (hV : DescPath ctx level r p₂ level₂ V)
    (htcs : p₂.map Prod.fst = p₁.map Prod.fst)
    (hUd : ∀ q, q < n → U.ptn[q]! ≤ level₁)
    (hVd : ∀ q, q < n → V.ptn[q]! ≤ level₂)
    {γ : Array Nat} (hγsz : γ.size = n)
    (hsc : ∀ i, i < n → γ[U.lab[i]!]! = V.lab[i]!) :
    checkAutom ctx.g γ = true := by
  have hUok := descends_iterOk hU.descends hS.it
  have hVok := descends_iterOk hV.descends hS.it
  exact checkAutom_scatter_of_leafRows_eq hγsz hUok.ok.labSize
    (labInj_perm_range hUok.ok.labSize hUok.ok.labOk hUok.inj)
    hVok.ok.labSize
    (labInj_perm_range hVok.ok.labSize hVok.ok.labOk hVok.inj)
    hsc
    (leafRows_eq_of_descPaths hgsz hsymm hloop hS hU hV htcs
      hUd hVd).symm

end Hex.GraphIso.Nauty
