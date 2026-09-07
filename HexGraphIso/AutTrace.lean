/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.AutGroup
import all HexGraphIso.Perm
import all HexGraphIso.Nauty.Cert.Cert
import all HexGraphIso.Nauty.Invariant.Trace
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso

variable {n k : Nat}

/-- The checked constructor accepts any correctly sized array representing
a permutation, including the empty permutation. -/
theorem Perm.ofNatArray?_eq {γ : Array Nat} {p : Perm n}
    (hsize : γ.size = n) (hval : ∀ i : Fin n, (p.get i).val = γ[i.val]!) :
    Perm.ofNatArray? n γ = some p := by
  have hvalid : γ.size = n ∧ ∀ i, (hi : i < γ.size) → γ[i] < n := by
    refine ⟨hsize, fun i hi => ?_⟩
    have hv := hval ⟨i, by omega⟩
    rw [getElem!_pos γ i hi] at hv
    exact hv ▸ (p.get ⟨i, by omega⟩).isLt
  rw [Perm.ofNatArray?, dite_eq_left hvalid]
  have heq : (Hex.Vector.ofFn' fun i : Fin n =>
      (⟨γ[i.val]'(hvalid.1.symm ▸ i.isLt),
        hvalid.2 i.val (hvalid.1.symm ▸ i.isLt)⟩ : Fin n)) = p.vec := by
    apply Vector.ext
    intro i hi
    apply Fin.ext
    simp only [Hex.Vector.getElem_ofFn']
    have hv := hval ⟨i, hi⟩
    rw [getElem!_pos γ i (by omega)] at hv
    exact hv.symm
  rw [heq, Perm.ofVector?, dite_eq_left ⟨p.nodup, p.complete⟩]

/-- A valid automorphism array passes the public admission filter. -/
theorem autom?_eq {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (hsize : γ.size = n) (hval : ∀ i : Fin n, (p.get i).val = γ[i.val]!)
    (hp : IsIso G G p) : autom? G γ = some p := by
  simp only [autom?, Perm.ofNatArray?_eq hsize hval, (checkIso_iff G G p).mpr hp,
    ↓reduceIte]

namespace Aut

open Nauty

/-- The row checker supplies a typed permutation with exactly the array's
entries. Colour preservation is a separate obligation. -/
theorem checked_perm {G : Colored n k} {γ : Array Nat}
    (h : checkAutom (rowsOf G) γ = true) :
    ∃ p : Perm n, (∀ i : Fin n, (p.get i).val = γ[i.val]!) ∧
      (∀ i j, G.graph.adj (p.get i) (p.get j) = G.graph.adj i j) := by
  have hb := checkAutom_bound h
  have hi := checkAutom_inj h
  have hperm : ((List.range n).map fun i => γ[i]!).Perm (List.range n) := by
    have hh := h
    rw [checkAutom] at hh
    simp only [Bool.and_eq_true] at hh
    exact List.isPerm_iff.mp hh.1.2
  let f (i : Fin n) : Fin n := ⟨γ[i.val]!, hb i.val i.isLt⟩
  have hinj : ∀ i j, f i = f j → i = j := by
    intro i j heq
    exact Fin.ext (hi i.val j.val i.isLt j.isLt (congrArg Fin.val heq))
  have hsurj : ∀ i, ∃ j, f j = i := by
    intro i
    have hm := hperm.mem_iff.mpr (List.mem_range.mpr i.isLt)
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hm
    exact ⟨⟨j, List.mem_range.mp hj⟩, Fin.ext heq⟩
  let p := Perm.ofFn f hinj hsurj
  have hval : ∀ i : Fin n, (p.get i).val = γ[i.val]! := by
    intro i
    simp [p, f]
  refine ⟨p, hval, fun i j => ?_⟩
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound (size_rowsOf G) h
  have hσp : ∀ i : Fin n, σ i.val = (p.get i).val :=
    fun i => (hσ i.val i.isLt).trans (hval i).symm
  have heq := congrArg (fun row : VSet n => row.mem (σ j.val)) (hrows.2.2 i.val i.isLt)
  rw [VSet.mem_image_apply σ _ j.isLt, hσp i, hσp j,
    getElem!_rowsOf G (p.get i).isLt, getElem!_rowsOf G i.isLt,
    mem_rowOf_lt G (p.get i).isLt (p.get j).isLt,
    mem_rowOf_lt G i.isLt j.isLt] at heq
  exact heq

/-- A row-checked array preserving the initial colours passes the public
admission filter. -/
theorem admit {G : Colored n k} {γ : Array Nat}
    (hcheck : checkAutom (rowsOf G) γ = true) (hcolor : ColorMap G γ) :
    ∃ p, autom? G γ = some p := by
  obtain ⟨p, hval, hadj⟩ := checked_perm hcheck
  have hsize : γ.size = n := by
    have hh := hcheck
    rw [checkAutom] at hh
    simp only [Bool.and_eq_true] at hh
    exact beq_iff_eq.mp hh.1.1.1
  refine ⟨p, autom?_eq hsize hval (IsIso.mk ?_ hadj)⟩
  intro v
  obtain ⟨hv, hc⟩ := hcolor v
  have he : p.get v = (⟨γ[v.val]!, hv⟩ : Fin n) := Fin.ext (hval v)
  change G.coloring.cells.get (p.get v) = G.coloring.cells.get v
  rw [he]
  exact hc

/-- A scatter between two reached labellings preserves the initial
colouring, so its row-check certificate passes the public filter. -/
theorem admit_scatter {G : Colored n k} {γ ref cur : Array Nat}
    (hn : 0 < n) (hrefSize : ref.size = n)
    (href : CellsReach G ref) (hcur : CellsReach G cur)
    (hcheck : checkAutom (rowsOf G) γ = true)
    (hmap : ∀ i, i < n → γ[ref[i]!]! = cur[i]!) :
    ∃ p, autom? G γ = some p :=
  admit hcheck (ColorMap.scatter hn hrefSize href hcur hmap)

/-- A root-ledger carrier preserves colours because it stabilizes every
initial colour cell. This includes carriers of implicit pruning pairs. -/
theorem admit_root {G : Colored n k} {γ : Array Nat}
    (hcheck : checkAutom (rowsOf G) γ = true)
    (hstab : CellStab (initPtn n (n + 2) (initialPartition G).2) 1
      (initialPartition G).1 γ) : ∃ p, autom? G γ = some p := by
  apply admit hcheck
  intro v
  have hn : 0 < n := by have := v.isLt; omega
  exact ColorMap.scatter hn (initial_nodeOk G hn).labSize
    (cellsReach_initial G) hstab
    (fun i hi => (getElem!_map_of_lt (fun w => γ[w]!) _
      (by rw [(initial_nodeOk G hn).labSize]; exact hi)).symm) v

/-- Every array in the executable trace is admitted, including redundant
code-two automorphisms. The proof uses the search invariant; it adds no
work to the traversal. -/
theorem trace_admitted (G : Colored n k) :
    ∀ γ ∈ trace G, ∃ p, autom? G γ = some p := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    simp [trace, runColoredTraced, runTraced]
  · obtain ⟨fs, outBest, eventTrail, hrun, -⟩ :=
      (totalAll G { g := rowsOf G } (n + 2) 100 (n + 2)).2
        n 1 (initialPartition G).2.length []
        (rootSt n (initialPartition G).1 (initialPartition G).2)
        FrameTrail.empty rfl rfl hn (Nat.le_refl 1) rfl (by omega)
        (by omega) (Nat.le_refl 1)
        (CheapDesc.same { g := rowsOf G } 1 _)
        (orbSound_orbConn_init _) (FirstInv.root hn) PathOk.root
    have hevent := hrun.proof.node.outcome.event
    have hinv : GenTraceOk { g := rowsOf G }
        (rootOut n (rowsOf G) (initialPartition G).1 (initialPartition G).2)
        (ColorMap G) := by
      cases hevent with
      | intro _ _ _ event _ _ _ _ _ _ => exact event.genTraceOk
    intro γ hγ
    have hm : γ ∈ (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2).genTrace.toList := by
      simpa only [trace, runColoredTraced, runTraced, beq_iff_eq,
        Nat.ne_of_gt hn, ite_false, Id.run_pure, rootOut, rootSt] using hγ
    exact admit (hinv.check hm) (hinv.colors hm)

/-- The public filter retains the whole trace, in its original order. -/
theorem raw_eq_trace (G : Colored n k) : raw G = trace G := by
  have h : ∀ xs : List (Array Nat), (∀ γ ∈ xs, ∃ p, autom? G γ = some p) →
      (xs.filterMap fun γ => (autom? G γ).map fun p => (γ, p)).map Prod.fst = xs := by
    intro xs hx
    induction xs with
    | nil => rfl
    | cons γ xs ih =>
        obtain ⟨p, hp⟩ := hx γ (by simp)
        simp only [List.filterMap_cons, hp, Option.map_some, List.map_cons]
        congr 1
        exact ih (fun δ hδ => hx δ (by simp [hδ]))
  exact h (trace G) (trace_admitted G)

/-- A checked automorphism recorded in the raw trace belongs to the public
generator list. This also admits code-two generators that leave the orbit
partition unchanged. -/
theorem mem_gens {G : Colored n k} {γ : Array Nat} {p : Perm n}
    (htrace : γ ∈ trace G) (hcheck : autom? G γ = some p) : p ∈ gens G := by
  apply List.mem_map.mpr
  refine ⟨(γ, p), ?_, rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨γ, htrace, by simp [hcheck]⟩

/-- A recorded leaf carrier supplies a generated permutation with the
same pointwise action on the entire reference labelling. -/
theorem generated_carrier {G : Colored n k} {ctx : Ctx n}
    {ref cur : Array Nat} {store : Array (Array Nat)}
    (h : LabelCarrier ctx ref cur store)
    (hstore : ∀ γ ∈ store, γ ∈ trace G)
    (href : LabOk ref n) (hsize : ref.size = n) :
    ∃ p, Perm.Generated (gens G) p ∧
      ∀ i, (hi : i < n) → (p.get ⟨ref[i]!, href i (by omega)⟩).val = cur[i]! := by
  obtain ⟨γ, hmem, _, hmap⟩ := h
  have hraw : γ ∈ raw G := by rw [raw_eq_trace]; exact hstore γ hmem
  obtain ⟨p, hp, hval⟩ := raw_mem hraw
  exact ⟨p, .mem hp, fun i hi => (hval ⟨ref[i]!, href i (by omega)⟩).trans (hmap i hi)⟩

/-- Agreement on a reference permutation labelling identifies the whole
permutation. No orbit-count inference is needed for this final step. -/
theorem generated_of_reference {G : Colored n k} {p q : Perm n}
    {ref : Array Nat} (hsize : ref.size = n)
    (href : ref.toList.Perm (List.range n))
    (hq : Perm.Generated (gens G) q)
    (heq : ∀ i, (hi : i < n) → ∀ hv : ref[i]! < n,
      q.get ⟨ref[i]!, hv⟩ = p.get ⟨ref[i]!, hv⟩) :
    Perm.Generated (gens G) p := by
  have hpq : q = p := by
    apply Perm.ext
    intro v
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp
      (href.mem_iff.mpr (List.mem_range.mpr v.isLt))
    have hin : i < n := by simpa [hsize] using hi
    have hv : ref[i]! = v.val := by
      rw [getElem!_pos ref i (by omega)]
      exact hiv
    have h := heq i hin (by omega)
    have hv' : (⟨ref[i]!, by omega⟩ : Fin n) = v := Fin.ext hv
    rwa [hv'] at h
  rwa [← hpq]

end Aut

namespace Nauty.Generation

/-- Every recorded array passes the public colour-preserving checker. -/
def TraceOk (G : Colored n k) (st : SearchSt n) : Prop :=
  ∀ γ ∈ st.genTrace, ∃ p, autom? G γ = some p

theorem TraceOk.ofFields {G : Colored n k} {st out : SearchSt n}
    (h : TraceOk G st) (he : out.genTrace = st.genTrace) : TraceOk G out := by
  intro γ hγ
  rw [he] at hγ
  exact h γ hγ

/-- Admitting a generator preserves the complete public admission check:
its scatter endpoints are both reached from the initial colour partition. -/
theorem TraceOk.processnode {G : Colored n k} {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n}
    (hg : ctx.g = rowsOf G) (hn : 0 < n)
    (hok : SearchOk G level numcells st) (hrefs : LeafRefsOk G st)
    (hcanong : CanongInv ctx st.canong st.canonlab st.samerows)
    (h : TraceOk G st) : TraceOk G (processnode ctx level numcells st).2 := by
  obtain hsame | ⟨γ, hpush, hcheck, hmap⟩ := processnode_carrier
    (by rw [hg]; exact rowsOf_symm G) (by rw [hg]; exact rowsOf_loopless G)
    hrefs.firstSize (labOk_of_reach hrefs.firstSize hrefs.firstReach)
    (labInj_of_reach hrefs.firstSize hn hrefs.firstReach)
    hok.labSize (labOk_of_reach hok.labSize hok.reach)
    (labInj_of_reach hok.labSize hn hok.reach)
    hrefs.canonSize (labOk_of_reach hrefs.canonSize hrefs.canonReach)
    (labInj_of_reach hrefs.canonSize hn hrefs.canonReach)
    (fun htie => rows_eq_of_testcanlab_tie hcanong htie)
  · exact h.ofFields hsame
  · intro δ hδ
    rw [hpush] at hδ
    rcases Array.mem_push.mp hδ with hδ | rfl
    · exact h δ hδ
    · rw [hg] at hcheck
      rcases hmap with hfirst | hcanon
      · exact Aut.admit_scatter hn hrefs.firstSize hrefs.firstReach hok.reach hcheck hfirst
      · exact Aut.admit_scatter hn hrefs.canonSize hrefs.canonReach hok.reach hcheck hcanon

end Nauty.Generation

end Hex.GraphIso
