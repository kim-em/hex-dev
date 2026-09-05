/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert.CertAutom
public import HexGraphIso.Nauty.Cert.Translator
public import HexGraphIso.Nauty.Spec.Achieved
public import HexGraphIso.Nauty.Spec.SpecIso
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.Refine

public section

/-!
The orbit bookkeeping: the orbit-partition pruning discipline and
its key-repetition consequence, and soundness of the union-find
store the search joins every admitted generator into.
-/

/-!
The orbit-partition (`fmptn`) discipline: `orbPruned` skips a child
whose target vertex reaches an earlier sibling's under forward closure
of the generator store, exhibiting no single carrying generator.
`childKey_of_orbPruned` shows the skipped subtree's key repeats the
earlier sibling's: the orbit path composes to a checked automorphism
(`wordPerm_spec`, on `checkAutom_range` and `checkAutom_compose`;
forward words suffice because permutations of a finite set generate a
group under composition alone) that still fixes every cell of the
node's partition setwise (`CellStab`, closed under composition by
`cellStab_comp`), and such a composite carries one breakout labelling
to the other cell by cell (`cellsPerm_set!` on the split partition), so
`specNode_autom` transports the key.

The cell-stabilization hypothesis is per node. It holds for the
generators nauty's bookkeeping admits at a node, since automorphisms
found below fix the node's cells setwise. Propagating it through
`refine` and descent, and filtering the store as the individualized
base grows, is transcription-side accounting, so no recursive
orbit-pruned evaluator is defined here.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Cell stabilization

The orbit (`fmptn`) prune drops a child whose target vertex lies in
the store-generated orbit of an earlier sibling's, without exhibiting
a single carrying generator. Its justification composes stored
generators along the orbit path, so it needs the property that
survives composition: each generator fixes every cell of the current
partition setwise. -/

/-- `γ` fixes each cell's content set: the labelling mapped through
`γ` is cell-wise a permutation of itself. -/
@[expose] def CellStab (ptn : Array Nat) (level : Nat)
    (lab γ : Array Nat) : Prop :=
  cellsPerm ptn level lab (lab.map fun w => γ[w]!)

theorem cellStab_range {ptn lab : Array Nat} {level : Nat}
    (hok : LabOk lab n) : CellStab ptn level lab (Array.range n) := by
  show cellsPerm ptn level lab (lab.map fun w => (Array.range n)[w]!)
  have hmap : (lab.map fun w => (Array.range n)[w]!) = lab := by
    have h1 : (lab.map fun w => (Array.range n)[w]!) =
        lab.map fun w => w :=
      map_congr_of_labOk hok fun w hw => by
        rw [getElem!_pos _ _ (by simpa using hw), Array.getElem_range]
    rw [h1]
    refine Array.ext (by rw [Array.size_map]) fun i hi hi' => ?_
    rw [Array.getElem_map]
  rw [hmap]
  exact cellsPerm_refl _ _ _

theorem cellStab_comp {ptn lab f π : Array Nat} {level : Nat}
    (hok : LabOk lab n) (hsp : ptn.size = n) (hs : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hf : CellStab ptn level lab f) (hπ : CellStab ptn level lab π) :
    CellStab ptn level lab (composePerm f π n) := by
  show cellsPerm ptn level lab
    (lab.map fun w => (composePerm f π n)[w]!)
  have hcomp : (lab.map fun w => (composePerm f π n)[w]!) =
      (lab.map fun w => π[w]!).map fun u => f[u]! := by
    rw [Array.map_map]
    exact map_congr_of_labOk hok fun w hw =>
      composePerm_getElem! f π hw
  rw [hcomp]
  refine cellsPerm_of_forall_cells hsp hs
    (by rw [Array.size_map, Array.size_map, hs]) hend ?_
  intro p hpm
  have hple := cells_le p hpm
  have hpb := cells_bound (Nat.le_of_eq hsp.symm) hend p hpm
  have hic := cells_isCell (Nat.le_of_eq hsp.symm) hend p hpm
  have hbnd : p.1 + (p.2 + 1 - p.1) ≤ n := by
    rw [hsp] at hpb
    omega
  have hπc := hπ p.1 (p.2 + 1 - p.1) hic
  have hfc := hf p.1 (p.2 + 1 - p.1) hic
  have h1 : segN ((lab.map fun w => π[w]!).map fun u => f[u]!) p.1
      (p.2 + 1 - p.1) =
      (segN (lab.map fun w => π[w]!) p.1 (p.2 + 1 - p.1)).map
        fun u => f[u]! :=
    segN_map_of_le _ _ _ _ (by rw [Array.size_map, hs]; exact hbnd)
  have h2 : segN (lab.map fun u => f[u]!) p.1 (p.2 + 1 - p.1) =
      (segN lab p.1 (p.2 + 1 - p.1)).map fun u => f[u]! :=
    segN_map_of_le _ _ _ _ (by rw [hs]; exact hbnd)
  rw [h1]
  rw [h2] at hfc
  exact hfc.trans (hπc.map _)

/-! # Words of generators and their composite -/

/-- Bound extraction from a checked automorphism. -/
theorem checkAutom_bound {g : Array (VSet n)} {γ : Array Nat}
    (h : checkAutom g γ = true) : ∀ v, v < n → γ[v]! < n := by
  rw [checkAutom] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hbound⟩, _⟩, _⟩ := h
  intro v hv
  simpa using List.all_eq_true.mp hbound v (List.mem_range.mpr hv)

/-- Apply a word of generators, leftmost first. -/
@[expose] def applyWord (w : List (Array Nat)) (v : Nat) : Nat :=
  w.foldl (fun v γ => γ[v]!) v

/-- The composite permutation array carried by a word. -/
@[expose] def wordPerm (nn : Nat) : List (Array Nat) → Array Nat
  | [] => Array.range nn
  | γ :: w => composePerm (wordPerm nn w) γ nn

/-- A word of stored generators composes to a checked automorphism
that still stabilizes the cells and acts as the word does. -/
theorem wordPerm_spec {g : Array (VSet n)} {ptn lab : Array Nat} {level : Nat}
    (hok : LabOk lab n)
    (hsp : ptn.size = n) (hs : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    {S : List (Array Nat)}
    (hv : ∀ γ ∈ S, checkAutom g γ = true)
    (hstab : ∀ γ ∈ S, CellStab ptn level lab γ) :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ S) →
      checkAutom g (wordPerm n w) = true ∧
      CellStab ptn level lab (wordPerm n w) ∧
      ∀ v, v < n → (wordPerm n w)[v]! = applyWord w v
  | [], _ =>
    ⟨checkAutom_range, cellStab_range hok, fun v hv' => by
      rw [wordPerm, applyWord, List.foldl_nil,
        getElem!_pos _ _ (by simpa using hv'), Array.getElem_range]⟩
  | γ :: w, hmem => by
    obtain ⟨h1, h2, h3⟩ := wordPerm_spec hok hsp hs hend hv hstab
      w (fun γ' hγ' => hmem γ' (List.mem_cons_of_mem _ hγ'))
    have hγS := hmem γ (List.mem_cons_self ..)
    have hγA := hv γ hγS
    refine ⟨checkAutom_compose h1 hγA,
      cellStab_comp hok hsp hs hend h2 (hstab γ hγS),
      fun v hv' => ?_⟩
    rw [wordPerm, composePerm_getElem! _ _ hv',
      h3 _ (checkAutom_bound hγA v hv')]
    rfl

/-! # The executable orbit closure and its soundness -/

theorem foldl_invariant {α β : Type} {P : α → Prop}
    {step : α → β → α} :
    ∀ (l : List β) (s : α), P s →
      (∀ a b, b ∈ l → P a → P (step a b)) → P (l.foldl step s)
  | [], _, hs, _ => hs
  | b :: l, s, hs, hstep =>
    foldl_invariant l (step s b)
      (hstep s b (List.mem_cons_self ..) hs)
      (fun a b' hb' => hstep a b' (List.mem_cons_of_mem _ hb'))

/-- One round of forward generator images over a vertex set. -/
@[expose] def orbitStepSet (nn : Nat) (gens : List (Array Nat))
    (s : VSet nn) : VSet nn :=
  gens.foldl (fun acc γ =>
    (List.range nn).foldl (fun acc w =>
      if s.mem w then acc.insert γ[w]! else acc) acc) s

/-- Iterated forward closure of a vertex set under the store. Any
fuel is sound; `nn` rounds saturate. -/
@[expose] def orbitClose (nn : Nat) (gens : List (Array Nat)) :
    Nat → VSet nn → VSet nn
  | 0, s => s
  | fuel + 1, s => orbitClose nn gens fuel (orbitStepSet nn gens s)

theorem orbitStepSet_sound {nn : Nat} {gens : List (Array Nat)}
    {s : VSet nn} :
    ∀ x, (orbitStepSet nn gens s).mem x = true →
      s.mem x = true ∨
        ∃ γ ∈ gens, ∃ u, s.mem u = true ∧ γ[u]! = x := by
  refine foldl_invariant (P := fun acc => ∀ x,
      acc.mem x = true → s.mem x = true ∨
        ∃ γ ∈ gens, ∃ u, s.mem u = true ∧ γ[u]! = x)
    gens s (fun x hx => Or.inl hx) ?_
  intro acc γ hγ hacc
  refine foldl_invariant (P := fun acc => ∀ x,
      acc.mem x = true → s.mem x = true ∨
        ∃ γ ∈ gens, ∃ u, s.mem u = true ∧ γ[u]! = x)
    (List.range nn) acc hacc ?_
  intro a w hw ha x hx
  split at hx
  · next hcond =>
    rw [VSet.mem_insert, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hx
    rcases hx with h | h
    · exact ha x h
    · exact Or.inr ⟨γ, hγ, w, hcond, h.1⟩
  · exact ha x hx

theorem orbitClose_sound {nn : Nat} {gens : List (Array Nat)} :
    ∀ (fuel : Nat) (s : VSet nn) (x : Nat),
      (orbitClose nn gens fuel s).mem x = true →
      ∃ u w, s.mem u = true ∧ (∀ γ ∈ w, γ ∈ gens) ∧
        applyWord w u = x
  | 0, s, x, hx => ⟨x, [], hx, by simp, rfl⟩
  | fuel + 1, s, x, hx => by
    rw [orbitClose] at hx
    obtain ⟨u', w', hu', hw', happ⟩ :=
      orbitClose_sound fuel (orbitStepSet nn gens s) x hx
    rcases orbitStepSet_sound u' hu' with h | ⟨γ, hγ, u, hu, hγu⟩
    · exact ⟨u', w', h, hw', happ⟩
    · refine ⟨u, γ :: w', hu, ?_, ?_⟩
      · intro γ' hγ'
        rcases List.mem_cons.mp hγ' with rfl | h'
        · exact hγ
        · exact hw' γ' h'
      · show applyWord w' γ[u]! = x
        rw [hγu]
        exact happ

/-! # Cells across one level step -/

theorem isCell_succ {ptn : Array Nat} {level a len : Nat}
    (hvals : ∀ q : Nat, ptn[q]! ≤ level ∨ ptn[q]! = n + 2)
    (hlev : level + 1 < n + 2) (hic : IsCell ptn level a len) :
    IsCell ptn (level + 1) a len := by
  obtain ⟨h1, h2, h3, h4⟩ := hic
  refine ⟨h1, ?_, ?_, by omega⟩
  · rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · intro i hi hi2
    have := h3 i hi hi2
    rcases hvals i with h | h
    · omega
    · omega

theorem isCell_pred {ptn : Array Nat} {level a len : Nat}
    (hvals : ∀ q : Nat, ptn[q]! ≤ level ∨ ptn[q]! = n + 2)
    (hlev : level + 1 < n + 2) (hic : IsCell ptn (level + 1) a len) :
    IsCell ptn level a len := by
  obtain ⟨h1, h2, h3, h4⟩ := hic
  refine ⟨h1, ?_, ?_, ?_⟩
  · rcases h2 with h | h
    · exact Or.inl h
    · rcases hvals (a - 1) with h' | h'
      · exact Or.inr h'
      · omega
  · intro i hi hi2
    have := h3 i hi hi2
    omega
  · rcases hvals (a + len - 1) with h' | h'
    · exact h'
    · omega

/-! # The orbit prune covers a dropped child by an earlier sibling -/

/-- The `fmptn`-style skip: child `o` is dropped when its target
vertex reaches an earlier sibling's under forward closure of the
store. No single carrying generator is exhibited. -/
@[expose] def orbPruned (nn : Nat) (gens : List (Array Nat))
    (rsLab : Array Nat) (tc o : Nat) : Bool :=
  (List.range o).any fun o' =>
    (orbitClose nn gens nn (VSet.empty.insert rsLab[tc + o]!)).mem
      rsLab[tc + o']!

/-- An orbit-pruned position's key repeats an earlier sibling's: the
orbit path composes to a checked, cell-stabilizing automorphism
carrying one breakout n labelling to the other, and `specNode_autom`
transports the subtree key. This is the justification of the
`fmptn` discipline at one node. -/
theorem childKey_of_orbPruned {ctx : Ctx n}
    (hgsz : ctx.g.size = n)
    {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o : Nat}
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (hlf : level + 1 + fuel ≤ n + 1)
    (hpr : orbPruned n gens rsLab tc o = true) :
    ∃ o', o' < o ∧
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' =
        childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o := by
  rw [orbPruned] at hpr
  obtain ⟨o', ho'm, hbit⟩ := List.any_eq_true.mp hpr
  have ho'o := List.mem_range.mp ho'm
  -- the orbit path composes to a carrying automorphism
  obtain ⟨u, wγ, hu, hwmem, happ⟩ := orbitClose_sound _ _ _ hbit
  have huv : u = rsLab[tc + o]! := by
    rw [VSet.mem_insert, VSet.mem_empty, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hu
    exact hu.1.symm
  rw [huv] at happ
  have hv' : ∀ γ ∈ gens, checkAutom ctx.g γ = true := by
    intro γ hγ
    exact hv γ hγ
  obtain ⟨hAutC, hstabC, hpointC⟩ := wordPerm_spec hok hsp hs hend
    hv' hstab wγ hwmem
  have hvO : rsLab[tc + o]! < n := hok _ (by omega)
  have hvO' : rsLab[tc + o']! < n := hok _ (by omega)
  obtain ⟨σ, hσeq, hσrows⟩ := checkAutom_sound hgsz hAutC
  have hσvO : σ.toFun rsLab[tc + o]! = rsLab[tc + o']! := by
    rw [hσeq _ hvO, hpointC _ hvO, happ]
  obtain ⟨L, rfl⟩ : ∃ L, lenT = L + 1 := ⟨lenT - 1, by omega⟩
  -- breakout n heads and tails on the target cell
  have hbsz : (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o]!).1.size = n := by
    show (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
      rsLab[tc + o]!).size = n
    rw [breakout_go_size, hs]
  have hsegO : segN (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o]!).1 tc (L + 1) =
      rsLab[tc + o]! :: (segN rsLab tc (L + 1)).erase rsLab[tc + o]! := by
    show segN (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
      rsLab[tc + o]!) tc (L + 1) = _
    exact breakout_go_seg (rsLab.size + 1) (L + 1) rsLab tc
      rsLab[tc + o]! ⟨tc + o, by omega, by omega, by omega, rfl⟩
      (by omega) (by omega)
  have hsegO' : segN (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o']!).1 tc (L + 1) =
      rsLab[tc + o']! ::
        (segN rsLab tc (L + 1)).erase rsLab[tc + o']! := by
    show segN (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
      rsLab[tc + o']!) tc (L + 1) = _
    exact breakout_go_seg (rsLab.size + 1) (L + 1) rsLab tc
      rsLab[tc + o']! ⟨tc + o', by omega, by omega, by omega, rfl⟩
      (by omega) (by omega)
  rw [segN_cons] at hsegO
  rw [segN_cons] at hsegO'
  injection hsegO with hheadO htailO
  injection hsegO' with hheadO' htailO'
  -- the composite stabilizes each cell, transported through σ
  have hstabSeg : ∀ (a l : Nat), IsCell rsPtn level a l → a + l ≤ n →
      (segN rsLab a l).Perm ((segN rsLab a l).map σ.toFun) := by
    intro a l hicl hbnd
    have h := hstabC a l hicl
    rw [segN_map_of_le _ _ _ _ (by omega)] at h
    have hcg : (segN rsLab a l).map
        (fun w => (wordPerm n wγ)[w]!) =
        (segN rsLab a l).map σ.toFun := by
      refine List.map_congr_left fun x hx => ?_
      rw [segN] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hilt := List.mem_range.mp hi
      exact (hσeq _ (hok _ (by omega))).symm
    rw [hcg] at h
    exact h
  -- the split-partition cell equivalence between the two breakouts
  have hicS : IsCell rsPtn (level + 1) tc (L + 1) :=
    isCell_succ hvals (by omega) hic
  have hend' : rsPtn[n - 1]! ≤ level := by
    have h := hend
    rwa [hsp] at h
  have hcp : cellsPerm (rsPtn.set! tc (level + 1)) (level + 1)
      (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1
      ((breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1.map
        σ.toFun) := by
    refine cellsPerm_set! hicS (by omega) (Nat.le_refl tc)
      (by omega) ?_ ?_ ?_
    · -- the individualized singletons agree under σ
      rw [show tc + 1 - tc = 1 by omega, segN_cons, segN_zero,
        segN_cons, segN_zero, hheadO',
        getElem!_map_of_lt σ.toFun _ (by rw [hbsz]; omega), hheadO,
        hσvO]
    · -- the remainder cells the.erase two vertices and transport
      rw [show tc + (L + 1) - (tc + 1) = L by omega, htailO',
        segN_map_of_le _ _ _ _ (by rw [hbsz]; omega), htailO]
      have hCstab := hstabSeg tc (L + 1) hic hrange
      have hvoC : rsLab[tc + o]! ∈ segN rsLab tc (L + 1) := by
        rw [segN]
        exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩
      have hvo'C : rsLab[tc + o']! ∈ segN rsLab tc (L + 1) := by
        rw [segN]
        exact List.mem_map.mpr ⟨o', List.mem_range.mpr (by omega),
          rfl⟩
      have h5 : ((segN rsLab tc (L + 1)).map σ.toFun).Perm
          (rsLab[tc + o']! ::
            ((segN rsLab tc (L + 1)).erase rsLab[tc + o]!).map
              σ.toFun) := by
        have h := (List.perm_cons_erase hvoC).map σ.toFun
        rw [List.map_cons, hσvO] at h
        exact h
      exact ((List.perm_cons_erase hvo'C).symm.trans
        (hCstab.trans h5)).cons_inv
    · -- untouched cells: both breakouts restrict to `rsLab`
      intro a l hicA hdisj
      have hlabO'eq : segN (breakout n rsLab rsPtn (level + 1) tc
          rsLab[tc + o']!).1 a l = segN rsLab a l := by
        refine segN_congr fun q hq => ?_
        show (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
          rsLab[tc + o']!)[a + q]! = rsLab[a + q]!
        rcases hdisj with hd | hd
        · exact breakout_go_outside _ _ _ _ _ (by omega)
        · exact breakout_go_outside_right _ (L + 1) _ _ _
            ⟨tc + o', by omega, by omega, by omega, rfl⟩ _ (by omega)
      have hlabOeq : segN (breakout n rsLab rsPtn (level + 1) tc
          rsLab[tc + o]!).1 a l = segN rsLab a l := by
        refine segN_congr fun q hq => ?_
        show (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
          rsLab[tc + o]!)[a + q]! = rsLab[a + q]!
        rcases hdisj with hd | hd
        · exact breakout_go_outside _ _ _ _ _ (by omega)
        · exact breakout_go_outside_right _ (L + 1) _ _ _
            ⟨tc + o, by omega, by omega, by omega, rfl⟩ _ (by omega)
      rcases Nat.lt_or_ge a n with han | han
      · -- in-range block: bound it, then transport by stability
        have hbnd : a + l ≤ n := by
          rcases Nat.lt_or_ge (a + l) (n + 1) with h1 | h1
          · omega
          · exfalso
            have hi := hicA.2.2.1 (n - 1) (by omega) (by omega)
            omega
        have hicL : IsCell rsPtn level a l :=
          isCell_pred hvals (by omega) hicA
        rw [hlabO'eq,
          segN_map_of_le _ _ _ _ (by rw [hbsz]; exact hbnd),
          hlabOeq]
        exact hstabSeg a l hicL hbnd
      · -- degenerate out-of-range block: a lone default entry
        have hl1 : l = 1 := by
          rcases Nat.lt_or_ge l 2 with h2 | h2
          · have := hicA.1
            omega
          · exfalso
            have hi := hicA.2.2.1 a (Nat.le_refl a) (by omega)
            rw [getElem!_neg _ _ (by omega)] at hi
            have hd : (default : Nat) = 0 := rfl
            omega
        subst hl1
        rw [hlabO'eq, segN_cons, segN_zero, segN_cons, segN_zero,
          getElem!_neg rsLab a (by omega),
          getElem!_neg ((breakout n rsLab rsPtn (level + 1) tc
              rsLab[tc + o]!).1.map σ.toFun) a
            (by rw [Array.size_map, hbsz]; omega)]
  -- transport the subtree key along the composite automorphism
  have hokc := childNodeOk hs hok hsp hend hvals hic hrange ho
  have hokc' := childNodeOk hs hok hsp hend hvals hic hrange
    (show o' < (L + 1) by omega)
  have hkeyeq : childKey ctx tcLevel fuel level rsLab rsPtn tc
      numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' :=
    specNode_autom hσrows tcLevel fuel (level + 1)
      (lab₁ := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1)
      (lab₂ := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1)
      (ptn := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1)
      (active := (breakout n rsLab rsPtn (level + 1) tc
        rsLab[tc + o]!).2.2)
      (numcells := numcells + 1) hcp hokc'.labSize hokc.labSize
      hokc'.labOk hokc.labOk hokc.ptnSize hokc.ptnEnd
      hokc.starts hokc.vals (by omega)
  exact ⟨o', ho'o, hkeyeq.symm⟩

end Hex.GraphIso.Nauty

/-!
Soundness of the transcription's orbit bookkeeping. The search keeps
one global union-find array `st.orbits`, joined with every admitted
generator through `orbjoin`; prune sites consult its parent pointers
directly. The lemmas below prove that every parent pointer is justified by
a forward word of joined generators: `WordConn` is the connectivity
relation (a word over the store carrying one vertex to the other),
and `OrbSound` states that each pointer strictly descends and is
`WordConn`-connected to its vertex. `orbjoin_orbSound` shows one
`orbjoin` call preserves `OrbSound` when the joining map is itself
word-connected pointwise, and `orbSound_init` seeds the identity
array, so the run-level invariant threads through the search with no
other touch points.

Symmetry of `WordConn` is where the group theory lives: the chase
loops inside `orbjoin` link roots found from both ends of a
generator edge, so the pointer being justified can point against the
direction of the discovered word. Forward words still suffice —
a bounded injective array has finite order pointwise
(`exists_applyWord_replicate_self`, by pigeonhole on the trajectory),
so the inverse of a generator is one of its forward powers
(`wordConn_symm`). No inverse arrays are ever materialized, matching
`orbitClose_sound`'s forward-only discipline on the model side.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Connectivity by a forward word over a generator store: some list
of stored arrays, applied leftmost first, carries `u` to `v`. -/
def WordConn (gens : List (Array Nat)) (u v : Nat) : Prop :=
  ∃ w : List (Array Nat), (∀ γ ∈ w, γ ∈ gens) ∧ applyWord w u = v

theorem wordConn_refl (gens : List (Array Nat)) (u : Nat) :
    WordConn gens u u :=
  ⟨[], by simp, rfl⟩

theorem applyWord_append (w₁ w₂ : List (Array Nat)) (u : Nat) :
    applyWord (w₁ ++ w₂) u = applyWord w₂ (applyWord w₁ u) :=
  List.foldl_append

theorem wordConn_trans {gens : List (Array Nat)} {u v x : Nat}
    (h₁ : WordConn gens u v) (h₂ : WordConn gens v x) :
    WordConn gens u x := by
  obtain ⟨w₁, hw₁, ha₁⟩ := h₁
  obtain ⟨w₂, hw₂, ha₂⟩ := h₂
  refine ⟨w₁ ++ w₂, fun γ hγ => ?_, ?_⟩
  · rcases List.mem_append.mp hγ with h | h
    · exact hw₁ γ h
    · exact hw₂ γ h
  · rw [applyWord_append, ha₁, ha₂]

theorem wordConn_step {gens : List (Array Nat)} {γ : Array Nat}
    (hγ : γ ∈ gens) (u : Nat) : WordConn gens u γ[u]! :=
  ⟨[γ], fun γ' hγ' => by rw [List.mem_singleton.mp hγ']; exact hγ, rfl⟩

theorem wordConn_mono {gens gens' : List (Array Nat)} {u v : Nat}
    (hsub : ∀ γ ∈ gens, γ ∈ gens')
    (h : WordConn gens u v) : WordConn gens' u v := by
  obtain ⟨w, hw, ha⟩ := h
  exact ⟨w, fun γ hγ => hsub γ (hw γ hγ), ha⟩

/-! # Pointwise finite order of a bounded injective array -/

theorem applyWord_replicate_succ (γ : Array Nat) (k u : Nat) :
    applyWord (List.replicate (k + 1) γ) u =
      applyWord (List.replicate k γ) γ[u]! := by
  rw [List.replicate_succ, applyWord, List.foldl_cons]
  rfl

theorem applyWord_replicate_lt {γ : Array Nat}
    (hb : ∀ v, v < n → γ[v]! < n) :
    ∀ (k : Nat) {u : Nat}, u < n →
      applyWord (List.replicate k γ) u < n
  | 0, _, hu => hu
  | k + 1, u, hu => by
    rw [applyWord_replicate_succ]
    exact applyWord_replicate_lt hb k (hb u hu)

theorem applyWord_replicate_inj {γ : Array Nat}
    (hb : ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b) :
    ∀ (k : Nat) {a b : Nat}, a < n → b < n →
      applyWord (List.replicate k γ) a =
        applyWord (List.replicate k γ) b → a = b
  | 0, _, _, _, _, h => h
  | k + 1, a, b, ha, hb', h => by
    rw [applyWord_replicate_succ, applyWord_replicate_succ] at h
    exact hinj a b ha hb'
      (applyWord_replicate_inj hb hinj k (hb a ha) (hb b hb') h)

/-- Pigeonhole on a trajectory: `n + 1` values below `n` repeat. -/
private theorem exists_repeat :
    ∀ (n : Nat) (s : Nat → Nat), (∀ j, j ≤ n → s j < n) →
      ∃ a b, a < b ∧ b ≤ n ∧ s a = s b
  | 0, s, hs => absurd (hs 0 (Nat.le_refl 0)) (by omega)
  | n + 1, s, hs => by
    rcases Classical.em (∃ j, j ≤ n ∧ s j = s (n + 1)) with h | h
    · obtain ⟨j, hj, heq⟩ := h
      exact ⟨j, n + 1, by omega, Nat.le_refl _, heq⟩
    · have hne : ∀ j, j ≤ n → s j ≠ s (n + 1) := by
        intro j hj hcontra
        exact h ⟨j, hj, hcontra⟩
      have hlast : s (n + 1) < n + 1 := hs (n + 1) (Nat.le_refl _)
      obtain ⟨a, b, hab, hbn, heq⟩ := exists_repeat n
        (fun j => if s j = n then s (n + 1) else s j)
        (fun j hj => by
          rcases Decidable.em (s j = n) with hc | hc
          · rw [ite_eq_left hc]
            have := hne j hj
            omega
          · rw [ite_eq_right hc]
            have := hs j (by omega)
            omega)
      refine ⟨a, b, hab, by omega, ?_⟩
      rcases Decidable.em (s a = n) with ha | ha <;>
        rcases Decidable.em (s b = n) with hb | hb
      · rw [ha, hb]
      · rw [ite_eq_left ha, ite_eq_right hb] at heq
        exact absurd heq.symm (hne b (by omega))
      · rw [ite_eq_right ha, ite_eq_left hb] at heq
        exact absurd heq (hne a (by omega))
      · rw [ite_eq_right ha, ite_eq_right hb] at heq
        exact heq

/-- A bounded injective array returns every vertex to itself under
some positive number of forward applications. -/
theorem exists_applyWord_replicate_self {γ : Array Nat}
    (hb : ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b)
    {u : Nat} (hu : u < n) :
    ∃ k, 0 < k ∧ applyWord (List.replicate k γ) u = u := by
  obtain ⟨a, b, hab, hbn, heq⟩ := exists_repeat n
    (fun j => applyWord (List.replicate j γ) u)
    (fun j _ => applyWord_replicate_lt hb j hu)
  refine ⟨b - a, by omega, ?_⟩
  have hsplit : applyWord (List.replicate a γ)
      (applyWord (List.replicate (b - a) γ) u) =
      applyWord (List.replicate a γ) u := by
    rw [← applyWord_append, List.replicate_append_replicate]
    have : b - a + a = b := by omega
    rw [this]
    exact heq.symm
  exact applyWord_replicate_inj hb hinj a
    (applyWord_replicate_lt hb _ hu) hu hsplit

/-- Symmetry of forward-word connectivity over bounded injective
generators: the inverse of each letter is one of its forward
powers. -/
theorem wordConn_symm {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b) :
    ∀ (w : List (Array Nat)) {u v : Nat}, u < n →
      (∀ γ ∈ w, γ ∈ gens) → applyWord w u = v →
      WordConn gens v u
  | [], u, v, _, _, happ => happ ▸ wordConn_refl gens u
  | γ :: w, u, v, hu, hmem, happ => by
    have hγ := hmem γ (List.mem_cons_self ..)
    have hγu : γ[u]! < n := hb γ hγ u hu
    have happ' : applyWord w γ[u]! = v := happ
    have htail := wordConn_symm hb hinj w hγu
      (fun γ' hγ' => hmem γ' (List.mem_cons_of_mem _ hγ')) happ'
    obtain ⟨k, hk, hret⟩ :=
      exists_applyWord_replicate_self (hb γ hγ) (hinj γ hγ) hu
    refine wordConn_trans htail ⟨List.replicate (k - 1) γ,
      fun γ' hγ' => (List.eq_of_mem_replicate hγ') ▸ hγ, ?_⟩
    have : applyWord (List.replicate k γ) u =
        applyWord (List.replicate (k - 1) γ) γ[u]! := by
      have hks : k - 1 + 1 = k := by omega
      rw [← hks, applyWord_replicate_succ, hks]
    rw [← this, hret]

/-! # The union-find layer -/

/-- Soundness of an orbit-pointer array: every parent pointer
descends weakly and is `R`-connected to its vertex. Descent keeps
every pointer below `n` and makes the chase loops terminate within
their fuel, but soundness never needs the latter fact. -/
def OrbSound (R : Nat → Nat → Prop) (orbits : Array Nat) (n : Nat) :
    Prop :=
  orbits.size = n ∧ ∀ v, v < n → orbits[v]! ≤ v ∧ R v orbits[v]!

/-- The consumption form at prune sites: a consulted parent pointer
is justified by `R`. -/
theorem orbSound_ptr {R : Nat → Nat → Prop} {orbits : Array Nat}
    (h : OrbSound R orbits n) {v : Nat} (hv : v < n) :
    R v orbits[v]! :=
  (h.2 v hv).2

/-- The `k`-fold iterated parent pointer, as any chase computes it. -/
def ptrIter (orbits : Array Nat) (v : Nat) : Nat → Nat
  | 0 => v
  | k + 1 => orbits[ptrIter orbits v k]!

/-- Any pointer chase from a sound array descends and stays
`R`-connected. -/
theorem orbSound_iter {R : Nat → Nat → Prop} {orbits : Array Nat}
    (hrefl : ∀ v, R v v)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (h : OrbSound R orbits n) :
    ∀ (k : Nat) {v : Nat}, v < n →
      ptrIter orbits v k ≤ v ∧ R v (ptrIter orbits v k)
  | 0, v, _ => ⟨Nat.le_refl v, hrefl v⟩
  | k + 1, v, hv => by
    obtain ⟨hle, hR⟩ := orbSound_iter hrefl htrans h k hv
    have hlt : ptrIter orbits v k < n := by omega
    obtain ⟨hle', hR'⟩ := h.2 _ hlt
    exact ⟨by rw [ptrIter]; omega, htrans _ _ _ hR (by rw [ptrIter]; exact hR')⟩

theorem orbSound_init (R : Nat → Nat → Prop)
    (hrefl : ∀ v, v < n → R v v) :
    OrbSound R (Array.ofFn (n := n) fun i => i.val) n := by
  refine ⟨by simp, fun v hv => ?_⟩
  have hv' : (Array.ofFn (n := n) fun i => i.val)[v]! = v := by
    rw [getElem!_pos _ _ (by simpa using hv)]
    simp
  rw [hv']
  exact ⟨Nat.le_refl v, hrefl v hv⟩

theorem orbSound_set {R : Nat → Nat → Prop} {orbits : Array Nat}
    (h : OrbSound R orbits n) {p q : Nat} (hq : q < n) (hpq : p ≤ q)
    (hR : R q p) : OrbSound R (orbits.set! q p) n := by
  refine ⟨by rw [Array.size_set!]; exact h.1, fun v hv => ?_⟩
  rcases Decidable.em (q = v) with rfl | hne
  · rw [Array.getElem!_set!_self _ _ _ (by rw [h.1]; exact hq)]
    exact ⟨hpq, hR⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ hne]
    exact h.2 v hv

theorem orbSound_mono {R R' : Nat → Nat → Prop} {orbits : Array Nat}
    (himp : ∀ a b, R a b → R' a b)
    (h : OrbSound R orbits n) : OrbSound R' orbits n :=
  ⟨h.1, fun v hv => ⟨(h.2 v hv).1, himp _ _ (h.2 v hv).2⟩⟩

/-- The state a `ForInStep` hands to the rest of the loop. -/
private def stepVal {β : Type} : ForInStep β → β
  | ForInStep.yield b => b
  | ForInStep.done b => b

private theorem stepVal_yield {β : Type} (b : β) :
    stepVal (ForInStep.yield b) = b := rfl

private theorem stepVal_done {β : Type} (b : β) :
    stepVal (ForInStep.done b) = b := rfl

/-- Invariant preservation through a `forIn` loop in `Id`: `break`
and normal exit both preserve `P`. -/
private theorem forIn_list_invariant {β : Type} {P : β → Prop} :
    ∀ (l : List Nat) (init : β) (f : Nat → β → Id (ForInStep β)),
      P init →
      (∀ i b, i ∈ l → P b → P (stepVal (Id.run (f i b)))) →
      P (forIn l init f : Id β)
  | [], _, _, hinit, _ => hinit
  | i :: l, init, f, hinit, hstep => by
    rw [List.forIn_cons]
    have hs := hstep i init (List.mem_cons_self ..) hinit
    match hf : f i init with
    | .yield b =>
      rw [show Id.run (f i init) = ForInStep.yield b from hf] at hs
      exact forIn_list_invariant l b f hs
        (fun i' b' hi' => hstep i' b' (List.mem_cons_of_mem _ hi'))
    | .done b =>
      rw [show Id.run (f i init) = ForInStep.done b from hf] at hs
      exact hs

private theorem forIn_range_eq₀ {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [:n].start [:n].size [:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

/-- The chase loop as a structural recursion: follow parent pointers
until a fixpoint or the fuel list runs out. -/
private def chaseList (orbits : Array Nat) : List Nat → Nat → Nat
  | [], j => j
  | _ :: l, j =>
    if orbits[j]! == j then j else chaseList orbits l orbits[j]!

private theorem forIn_chase_eq {orbits : Array Nat} :
    ∀ (l : List Nat) (j : Nat),
      (forIn l j (fun _ j =>
        if orbits[j]! == j then pure (ForInStep.done j)
        else pure (ForInStep.yield orbits[j]!)) : Id Nat) =
      chaseList orbits l j
  | [], _ => rfl
  | _ :: l, j => by
    rw [List.forIn_cons, chaseList]
    rcases Decidable.em ((orbits[j]! == j) = true) with hc | hc
    · rw [ite_eq_left hc, ite_eq_left hc]
      rfl
    · rw [ite_eq_right hc, ite_eq_right hc]
      exact forIn_chase_eq l _

private theorem run_chase_eq {orbits : Array Nat}
    (l : List Nat) (j : Nat) :
    Id.run (forIn l j (fun _ j =>
      if orbits[j]! == j then pure (ForInStep.done j)
      else pure (ForInStep.yield orbits[j]!))) =
    chaseList orbits l j :=
  forIn_chase_eq l j

private theorem chaseList_sound {R : Nat → Nat → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c)
    {orbits : Array Nat} (h : OrbSound R orbits n) :
    ∀ (l : List Nat) (x j : Nat), j < n → R x j →
      chaseList orbits l j < n ∧ R x (chaseList orbits l j) := by
  intro l
  induction l with
  | nil => exact fun x j hj hR => ⟨hj, hR⟩
  | cons head tail ih =>
    intro x j hj hR
    rw [chaseList]
    rcases Decidable.em ((orbits[j]! == j) = true) with hc | hc
    · rw [ite_eq_left hc]
      exact ⟨hj, hR⟩
    · rw [ite_eq_right hc]
      obtain ⟨hle, hstep⟩ := h.2 j hj
      exact ih x orbits[j]! (Nat.lt_of_le_of_lt hle hj)
        (htrans _ _ _ hR hstep)

private theorem bind_invariant {β γ : Type} {P : β → Prop}
    {Q : γ → Prop} (x : Id β) (f : β → Id γ)
    (hx : P x) (hf : ∀ b, P b → Q (f b)) : Q (x >>= f) := hf x hx

theorem orbjoin_orbSound {R : Nat → Nat → Prop}
    (hsymm : ∀ a b, R a b → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    {orbits map : Array Nat}
    (h : OrbSound R orbits n)
    (hmap : ∀ i, i < n → map[i]! < n ∧ R i map[i]!) :
    OrbSound R (orbjoin orbits map n).1 n := by
  rw [orbjoin]
  refine bind_invariant (P := fun o : Array Nat => OrbSound R o n)
    (Q := fun oc : Array Nat × Nat => OrbSound R oc.1 n) _ _ ?_ ?_
  · -- pass 1: each join step preserves soundness
    rw [forIn_range_eq₀]
    refine forIn_list_invariant (P := fun o => OrbSound R o n) _ _ _ h ?_
    intro i b hi hb
    have hi' : i < n := List.mem_range.mp hi
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite stepVal, stepVal_yield,
      forIn_range_eq₀, run_chase_eq]
    rcases Decidable.em ((map[i]! != i) = true) with hg | hg
    · rw [ite_eq_left hg]
      obtain ⟨hp1, hR1⟩ := hb.2 i hi'
      obtain ⟨hm, hRm⟩ := hmap i hi'
      obtain ⟨hp2, hR2⟩ := hb.2 map[i]! hm
      obtain ⟨hj1, hRj1⟩ :=
        chaseList_sound htrans hb (List.range n) i b[i]!
          (Nat.lt_of_le_of_lt hp1 hi') hR1
      obtain ⟨hj2, hRj2⟩ :=
        chaseList_sound htrans hb (List.range n) map[i]! b[map[i]!]!
          (Nat.lt_of_le_of_lt hp2 hm) hR2
      have hR12 : R (chaseList b (List.range n) b[map[i]!]!)
          (chaseList b (List.range n) b[i]!) :=
        htrans _ _ _ (hsymm _ _ hRj2)
          (htrans _ _ _ (hsymm _ _ hRm) hRj1)
      rcases Decidable.em (chaseList b (List.range n) b[i]! <
          chaseList b (List.range n) b[map[i]!]!) with hlt | hlt
      · rw [ite_eq_left hlt]
        exact orbSound_set hb hj2 (by omega) hR12
      · rw [ite_eq_right hlt]
        rcases Decidable.em (chaseList b (List.range n) b[i]! >
            chaseList b (List.range n) b[map[i]!]!) with hgt | hgt
        · rw [ite_eq_left hgt]
          exact orbSound_set hb hj1 (by omega) (hsymm _ _ hR12)
        · rw [ite_eq_right hgt]
          exact hb
    · rw [ite_eq_right hg]
      exact hb
  · -- pass 2: path halving preserves soundness pointwise
    intro b hbsound
    refine bind_invariant
      (P := fun s : Array Nat × Nat => OrbSound R s.1 n)
      (Q := fun p : Array Nat × Nat => OrbSound R p.1 n) _ _ ?_ ?_
    · rw [forIn_range_eq₀]
      refine forIn_list_invariant
        (P := fun s : Array Nat × Nat => OrbSound R s.1 n)
        _ _ _ hbsound ?_
      intro i s hi hs
      have hi' : i < n := List.mem_range.mp hi
      simp only [Id.run_pure, apply_ite Id.run,
        apply_ite stepVal, stepVal_yield]
      obtain ⟨hp, hRp⟩ := hs.2 i hi'
      obtain ⟨hq, hRq⟩ := hs.2 s.fst[i]! (Nat.lt_of_le_of_lt hp hi')
      have hset : OrbSound R (s.fst.set! i s.fst[s.fst[i]!]!) n :=
        orbSound_set hs hi' (Nat.le_trans hq hp)
          (htrans _ _ _ hRp hRq)
      rcases Decidable.em
          (((s.fst.set! i s.fst[s.fst[i]!]!)[i]! == i) = true) with
        hc | hc
      · rw [ite_eq_left hc]
        exact hset
      · rw [ite_eq_right hc]
        exact hset
    · intro s hs
      exact hs

/-! # Instantiation: pointers justified by generator words -/

/-- The connectivity relation the search's orbit array maintains:
both vertices in range, joined by a forward word over the store. -/
def OrbConn (gens : List (Array Nat)) (n : Nat) (a b : Nat) : Prop :=
  a < n ∧ b < n ∧ WordConn gens a b

theorem orbConn_symm {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b) :
    ∀ a b, OrbConn gens n a b → OrbConn gens n b a := by
  intro a b ⟨ha, hb', ⟨w, hw, happ⟩⟩
  exact ⟨hb', ha, wordConn_symm hb hinj w ha hw happ⟩

theorem orbConn_trans (gens : List (Array Nat)) :
    ∀ a b c, OrbConn gens n a b → OrbConn gens n b c →
      OrbConn gens n a c := by
  intro a b c ⟨ha, hb', hab⟩ ⟨_, hc, hbc⟩
  exact ⟨ha, hc, wordConn_trans hab hbc⟩

theorem orbConn_mono {gens gens' : List (Array Nat)}
    (hsub : ∀ γ ∈ gens, γ ∈ gens') :
    ∀ a b, OrbConn gens n a b → OrbConn gens' n a b := by
  intro a b ⟨ha, hb', hab⟩
  exact ⟨ha, hb', wordConn_mono hsub hab⟩

/-- Injectivity on `[0, n)` extracted from a checked automorphism's
permutation conjunct. -/
theorem checkAutom_inj {g : Array (VSet n)} {γ : Array Nat}
    (h : checkAutom g γ = true) :
    ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
  rw [checkAutom] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, hperm⟩, -⟩ := h
  intro a b ha hb heq
  have hnd : (((List.range n).map fun v => γ[v]!)).Nodup :=
    ((List.isPerm_iff.mp hperm).symm.nodup List.nodup_range)
  have hga : (((List.range n).map fun v => γ[v]!))[a]'(by
      simpa using ha) = γ[a]! := by
    rw [List.getElem_map, List.getElem_range]
  have hgb : (((List.range n).map fun v => γ[v]!))[b]'(by
      simpa using hb) = γ[b]! := by
    rw [List.getElem_map, List.getElem_range]
  exact hnd.eq_of_getElem_eq (by simpa using ha) (by simpa using hb)
    (by rw [hga, hgb, heq])

/-- The identity orbit array is sound for any store. -/
theorem orbSound_orbConn_init (gens : List (Array Nat)) :
    OrbSound (OrbConn gens n)
      (Array.ofFn (n := n) fun i => i.val) n :=
  orbSound_init _ fun v hv => ⟨hv, hv, wordConn_refl gens v⟩

/-- `orbjoin` with a stored generator keeps every pointer justified:
the run-level per-admission step. `hγ` names the workperm's
membership in the store the pointers are read against, so joining
with a newly admitted generator instantiates `gens` to the store
after admission (earlier pointers transport by `orbSound_orbConn_mono`). -/
theorem orbjoin_orbConn {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b)
    {orbits γ : Array Nat} (hγ : γ ∈ gens)
    (h : OrbSound (OrbConn gens n) orbits n) :
    OrbSound (OrbConn gens n) (orbjoin orbits γ n).1 n :=
  orbjoin_orbSound (orbConn_symm hb hinj) (orbConn_trans gens) h
    (fun i hi => ⟨hb γ hγ i hi,
      ⟨hi, hb γ hγ i hi, wordConn_step hγ i⟩⟩)

/-- Store growth transports pointer soundness. -/
theorem orbSound_orbConn_mono {gens gens' : List (Array Nat)}
    (hsub : ∀ γ ∈ gens, γ ∈ gens') {orbits : Array Nat}
    (h : OrbSound (OrbConn gens n) orbits n) :
    OrbSound (OrbConn gens' n) orbits n :=
  orbSound_mono (orbConn_mono hsub) h

/-- The consumption form at the transcription's prune sites: a
consulted parent pointer is a forward word of stored generators,
with both endpoints in range. -/
theorem orbConn_of_ptr {gens : List (Array Nat)} {orbits : Array Nat}
    (h : OrbSound (OrbConn gens n) orbits n) {v : Nat} (hv : v < n) :
    orbits[v]! < n ∧ WordConn gens v orbits[v]! := by
  obtain ⟨-, h1, h2⟩ := orbSound_ptr h hv
  exact ⟨h1, h2⟩

end Hex.GraphIso.Nauty
