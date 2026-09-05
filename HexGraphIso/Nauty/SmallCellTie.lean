/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellAll
import all HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
import all HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.SmallCellLeaves
import all HexGraphIso.Nauty.SmallCellAll

public section

/-!
The imperative tie and the code-1 assembly (SPEC § Verified search
refinement, the code-1 arm of the store-validity obligation).

The search's child loops perform `breakout` at the parent and then the
child node's `refine`; that composite is exactly `childSt`
(`childSt_eq_search_step`), and each surviving target-cell vertex is a
window member of the target cell (`maketargetcell_mem`), so an
imperative descent below a node is a `DescPath` step by step. Both
children of one imperative node use the same `maketargetcell` result,
so the first-path leaf and a code-1-tested leaf below the greatest
common ancestor are same-target descents, and
`descPath_leafRows_all` gives them equal leaf rows
(`leafRows_eq_of_descPaths`); the admitted scatter then passes
`checkAutom` through `checkAutom_scatter_of_leafRows_eq`
(`checkAutom_scatter_of_descPaths`).

`subtreeOk_of_cheapautom` establishes the node invariant at the
ancestor from the guard alone, with no residual hypothesis: the two
branches of `cheapautom_iff` are exactly the two disjuncts of
`NodeShape` (`cheapautom_shape_or_exotic`). The second branch, a
defect of at most four with a cell of size four or five or with two
triples, keeps its own shape rather than being forced into the first,
which it need not have; `flipData_of_subtreeOk` hands it to the
defect-four flip analogues (`SmallCellExotic3`).

The run-level facts these theorems consume — the two descents from
the ancestor with equal target paths, equitability and the boundary
count at the ancestor, and the guard having held there — are exactly
the bookkeeping the domination induction carries (`gcaFirst`,
`eqlevFirst`, `firsttc`, `noncheaplevel`); it discharges them when
threading `processnode`'s admission event.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # The imperative step is `childSt` -/

/-- The composite the search's child loops perform — `breakout` at the
parent, then the child node's `refine` on the returned labelling,
split partition, and singleton active set — is `childSt` of the
parent's post-refine state. -/
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
defect-at-most-four configuration. The second disjunct is the
explicitly surfaced exotic arm: a cell of size four or five, or two
triples, conformance-reachable per the probe, discharged by the
defect-four flip analogues. -/
theorem cheapautom_shape_or_exotic {ptn : Array Nat} {level : Nat}
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hch : cheapautom ptn level n = true) :
    SmallShape ctx level ptn ∨
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

/-! # Permutation labellings -/

private theorem countP_range_one {p : Nat → Bool} {n i₀ : Nat}
    (hi₀ : i₀ < n) (hp : p i₀ = true)
    (huniq : ∀ j, j < n → p j = true → j = i₀) :
    (List.range n).countP p = 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.countP_append]
    rcases Decidable.em (i₀ = m) with heq | hne
    · have h0 : (List.range m).countP p = 0 :=
        List.countP_eq_zero.mpr fun a ha hpa => by
          have han := List.mem_range.mp ha
          have := huniq a (by omega) hpa
          omega
      have hpm : p m = true := heq ▸ hp
      rw [h0, List.countP_cons, List.countP_nil, hpm]
      simp
    · have him : i₀ < m := by omega
      have h1 : (List.range m).countP p = 1 :=
        ih him (fun j hj hpj => huniq j (by omega) hpj)
      have h0 : ([m].countP p) = 0 :=
        List.countP_eq_zero.mpr fun a ha hpa => by
          have ham : a = m := by simpa using ha
          have := huniq a (by omega) hpa
          omega
      omega

private theorem toList_eq_map_range {lab : Array Nat} {n : Nat}
    (hsz : lab.size = n) :
    ((List.range n).map fun i => lab[i]!) = lab.toList := by
  refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos lab i (by simpa using h2)]
  simp

/-- An injective bounded labelling of full size is a permutation of
`[0, n)`: the side condition of the `checkAutom` scatter exits,
discharged from the node invariant the descents carry. -/
theorem labInj_perm_range {lab : Array Nat} {n : Nat}
    (hsz : lab.size = n) (hlab : LabOk lab n) (hinj : LabInj lab n) :
    lab.toList.Perm (List.range n) := by
  rw [List.perm_iff_count]
  intro a
  rw [← toList_eq_map_range hsz, List.count_eq_countP,
    List.count_eq_countP, List.countP_map]
  simp only [Function.comp_def]
  rcases Decidable.em (a < n) with ha | ha
  · obtain ⟨i₀, hi₀, hv⟩ := labInj_surj (by omega) hlab hinj a ha
    rw [countP_range_one (p := fun i => lab[i]! == a) hi₀
        (by simp [hv])
        (fun j hj hpj => hinj j i₀ hj hi₀ (by
          have : lab[j]! = a := by simpa using hpj
          rw [this, hv])),
      countP_range_one (p := fun i => i == a) ha (by simp)
        (fun j _ hpj => by simpa using hpj)]
  · rw [List.countP_eq_zero.mpr fun j hj hpj => by
        have hjn := List.mem_range.mp hj
        have : lab[j]! = a := by simpa using hpj
        have := hlab j (by omega)
        omega,
      List.countP_eq_zero.mpr fun j hj hpj => by
        have hjn := List.mem_range.mp hj
        have : j = a := by simpa using hpj
        omega]

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

/-- The code-1 gate admission is a checked automorphism: the scatter
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

/-! # Store validity, assembled per admission event -/

/-- If `processnode` records a generator, the same generator is both
checked and identified as the scatter from the first or incumbent leaf
onto the current leaf. -/
theorem processnode_carrier {level numcells : Nat} {st : SearchSt n}
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsz₁ : st.firstlab.size = n)
    (hok₁ : LabOk st.firstlab n) (hinj₁ : LabInj st.firstlab n)
    (hszL : st.lab.size = n)
    (hokL : LabOk st.lab n) (hinjL : LabInj st.lab n)
    (hsz₂ : st.canonlab.size = n)
    (hok₂ : LabOk st.canonlab n) (hinj₂ : LabInj st.canonlab n)
    (harm3 : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 =
        0 → leafRows ctx st.canonlab = leafRows ctx st.lab) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace ∨
    ∃ γ, (processnode ctx level numcells st).2.genTrace =
        st.genTrace.push γ ∧ checkAutom ctx.g γ = true ∧
      ((∀ i, i < n → γ[st.firstlab[i]!]! = st.lab[i]!) ∨
       (∀ i, i < n → γ[st.canonlab[i]!]! = st.lab[i]!)) := by
  have hp₁ := labInj_perm_range hsz₁ hok₁ hinj₁
  have hpL := labInj_perm_range hszL hokL hinjL
  have hp₂ := labInj_perm_range hsz₂ hok₂ hinj₂
  have hb₁ : ∀ i, i < n → st.firstlab[i]! < n :=
    fun i hi => hok₁ i (by omega)
  have hb₂ : ∀ i, i < n → st.canonlab[i]! < n :=
    fun i hi => hok₂ i (by omega)
  rcases processnode_genTrace (level := level) (numcells := numcells)
      (fun a b ha hb he => hinj₁ a b ha hb he)
      hb₁ (fun a b ha hb he => hinj₂ a b ha hb he) hb₂ with
    h | ⟨γ, hpush, hγsz, harm⟩
  · exact Or.inl h
  · rcases harm with ⟨hsc, -, haut⟩ | ⟨hsc, -, -, htceq⟩
    · refine Or.inr ⟨γ, hpush, ?_, Or.inl hsc⟩
      exact checkAutom_scatter_of_isautom hγsz hsz₁ hp₁ hszL hpL
        hsc hsymm hloop haut
    · exact Or.inr ⟨γ, hpush,
        checkAutom_scatter_of_leafRows_eq hγsz hsz₂ hp₂ hszL hpL
          hsc (harm3 htceq), Or.inr hsc⟩

/-- Every generator `processnode` admits passes `checkAutom`, given
the run-level facts per arm: permutation facts for the three
labellings (the run invariant carries them); the code-1 arm's mandatory
`isautom` scan; and the code-2 arm's rows equality (`harm3`, discharged from the
incumbent-store account: `updatecan_inv` completes `canong` to the
incumbent's leaf rows and `testcanlab_fst` reads the tie as row
equality). -/
theorem processnode_checkAutom {level numcells : Nat} {st : SearchSt n}
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsz₁ : st.firstlab.size = n)
    (hok₁ : LabOk st.firstlab n) (hinj₁ : LabInj st.firstlab n)
    (hszL : st.lab.size = n)
    (hokL : LabOk st.lab n) (hinjL : LabInj st.lab n)
    (hsz₂ : st.canonlab.size = n)
    (hok₂ : LabOk st.canonlab n) (hinj₂ : LabInj st.canonlab n)
    (harm3 : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 =
        0 →
      leafRows ctx st.canonlab = leafRows ctx st.lab) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace ∨
    ∃ γ, (processnode ctx level numcells st).2.genTrace =
        st.genTrace.push γ ∧ checkAutom ctx.g γ = true := by
  rcases processnode_carrier hsymm hloop hsz₁ hok₁ hinj₁ hszL
      hokL hinjL hsz₂ hok₂ hinj₂ harm3 with
    h | ⟨γ, hpush, hcheck, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨γ, hpush, hcheck⟩

/-! # The store-validity invariant -/

/-- Every generator the run has recorded is a checked automorphism.
This is the store-validity invariant, in the form the domination
induction threads: `processnode` is the only primitive that writes
`genTrace`, so every other event preserves it by its frame. -/
def GenTraceOk (ctx : Ctx n) (st : SearchSt n) : Prop :=
  ∀ γ ∈ st.genTrace, checkAutom ctx.g γ = true

/-- Read one checked-generator fact from the run-side store invariant. -/
theorem GenTraceOk.check {ctx : Ctx n} {st : SearchSt n}
    (h : GenTraceOk ctx st) {γ : Array Nat} (η : γ ∈ st.genTrace.toList) :
    checkAutom ctx.g γ = true :=
  h γ (Array.mem_toList_iff.mp η)

/-- The invariant survives the admission event. The only row clause is
the incumbent tie behind the `testcanlab` arm; code 1 is scanned. -/
theorem genTraceOk_processnode {level numcells : Nat} {st : SearchSt n}
    (hprev : GenTraceOk ctx st)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsz₁ : st.firstlab.size = n)
    (hok₁ : LabOk st.firstlab n) (hinj₁ : LabInj st.firstlab n)
    (hszL : st.lab.size = n)
    (hokL : LabOk st.lab n) (hinjL : LabInj st.lab n)
    (hsz₂ : st.canonlab.size = n)
    (hok₂ : LabOk st.canonlab n) (hinj₂ : LabInj st.canonlab n)
    (harm3 : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 =
        0 →
      leafRows ctx st.canonlab = leafRows ctx st.lab) :
    GenTraceOk ctx (processnode ctx level numcells st).2 := by
  intro γ hγ
  rcases processnode_checkAutom hsymm hloop hsz₁ hok₁ hinj₁ hszL
      hokL hinjL hsz₂ hok₂ hinj₂ harm3 with heq | ⟨δ, hpush, hδ⟩
  · rw [heq] at hγ
    exact hprev γ hγ
  · rw [hpush] at hγ
    rcases Array.mem_push.mp hγ with hmem | rfl
    · exact hprev γ hmem
    · exact hδ

end Hex.GraphIso.Nauty
