/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CertAutom
public import HexGraphIso.Nauty.Translator
public import HexGraphIso.Nauty.Achieved
public import HexGraphIso.Nauty.SpecIso

public section

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
