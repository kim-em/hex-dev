/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchModel

public section

/-!
The automorphism-pruned model search: `searchNodeA` extends the
code-pruned branch-and-bound of `searchNode` with the generator skip
the transcription performs and the certificate replays as `.autom`
records — a child position is dropped when a stored generator carries
its labelling, cell by cell, onto an earlier sibling's. For a store
of checked automorphisms (`checkAutom`), the skipped subtree's key
equals the earlier sibling's by `specNode_autom`, so the prune is
lossless: `searchNodeA_eq` shows the doubly-pruned recursion still
computes `incMax inc (specNode …)`, and `searchCanonA_key` packages
the root call as a verified pruned evaluator of `canonSpecKey`.

The store is a per-call parameter used at every node of the subtree.
Mid-sweep growth — a generator discovered under one child pruning a
later sibling of the same sweep, as the transcription's store does —
threads store state through the fold accumulator alongside the
incumbent; that refinement belongs with the orbit-partition (`fmptn`)
discipline, which additionally prunes every later member of a known
orbit rather than testing generators pairwise.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Pairwise generator skip for child `o` of a sweep: some stored
generator carries this child's labelling to an earlier sibling's,
cell by cell — the executable mirror of the `.autom` replay
condition. -/
@[expose] def autPruned (nn : Nat) (gens : List (Array Nat))
    (rsLab rsPtn : Array Nat) (level tc o : Nat) : Bool :=
  (List.range o).any fun o' =>
    gens.any fun γ =>
      checkCellsPerm
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1
        ((breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1.map
          fun w => γ[w]!)
        (level + 1) nn

mutual

/-- One node of the automorphism-and-code-pruned model search at an
already-refined state: leaf comparison when discrete, otherwise the
child sweep skipping generator-pruned positions. -/
@[expose] def stepA (ctx : Ctx) (tcLevel : Nat)
    (gens : List (Array Nat)) (fuel level : Nat) (rs : RefineSt)
    (tail0 : Option Key) : Key :=
  if discreteAt rs.ptn level ctx.n then
    let t' := incMax tail0 ⟨[codeSentinel], leafRows ctx rs.lab⟩
    ⟨rs.longcode :: t'.codes, t'.rows⟩
  else
    let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
    let t := ((List.range tcr.2.2).filter fun o =>
        !autPruned ctx.n gens rs.lab rs.ptn level tcr.1 o).foldl
      (fun (acc : Option Key) o =>
        let br := breakout rs.lab rs.ptn (level + 1) tcr.1
          rs.lab[tcr.1 + o]!
        some (searchNodeA ctx tcLevel gens fuel (level + 1) br.1
          br.2.1 br.2.2 (rs.numcells + 1) acc))
      tail0
    match t with
    | none => ⟨[], []⟩
    | some t => ⟨rs.longcode :: t.codes, t.rows⟩
  termination_by (fuel, 1)

/-- Branch-and-bound with both prunes: the incumbent's code prunes a
subtree exactly as in `searchNode`, and stored generators prune
sibling positions inside each sweep. Untrusted as an evaluator; the
theorem `searchNodeA_eq` verifies it against `specNode`. -/
@[expose] def searchNodeA (ctx : Ctx) (tcLevel : Nat)
    (gens : List (Array Nat)) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → Option Key → Key
  | 0, _, _, _, _, _, inc => inc.getD ⟨[], []⟩
  | fuel + 1, level, lab, ptn, active, numcells, none =>
    stepA ctx tcLevel gens fuel level
      (refine ctx level lab ptn active numcells) none
  | fuel + 1, level, lab, ptn, active, numcells, some b =>
    let rs := refine ctx level lab ptn active numcells
    match b.codes with
    | [] => stepA ctx tcLevel gens fuel level rs none
    | bc :: brest =>
      match compare rs.longcode bc with
      | .lt => b
      | .gt => stepA ctx tcLevel gens fuel level rs none
      | .eq => stepA ctx tcLevel gens fuel level rs
          (some ⟨brest, b.rows⟩)
  termination_by fuel _ _ _ _ _ _ => (fuel, 0)

end

/-! # Absorbing a common leading code into the incumbent maximum -/

theorem incMax_cons (lc : Nat) (tail0 : Option Key) (cs rws : List Nat) :
    incMax (tail0.map fun t => (⟨lc :: t.codes, t.rows⟩ : Key))
        ⟨lc :: cs, rws⟩ =
      ⟨lc :: (incMax tail0 ⟨cs, rws⟩).codes,
        (incMax tail0 ⟨cs, rws⟩).rows⟩ := by
  rcases tail0 with _ | t
  · rfl
  · show keyMax ⟨lc :: t.codes, t.rows⟩ ⟨lc :: cs, rws⟩ = _
    rw [keyMax_cons, key_eta]
    rfl

/-! # Folds whose steps compute the incumbent maximum -/

theorem foldl_incMax {f : Option Key → Nat → Option Key}
    {key : Nat → Key} :
    ∀ (os : List Nat),
      (∀ (acc : Option Key), ∀ o ∈ os,
        f acc o = some (incMax acc (key o))) →
      ∀ t : Key, os.foldl f (some t) = some (keysMax t (os.map key))
  | [], _, _ => rfl
  | o :: os, h, t => by
    rw [List.foldl_cons, h (some t) o (List.mem_cons_self ..),
      List.map_cons, keysMax]
    exact foldl_incMax os
      (fun acc o' ho' => h acc o' (List.mem_cons_of_mem _ ho')) _

theorem foldl_incMax_cons {f : Option Key → Nat → Option Key}
    {key : Nat → Key} {o : Nat} {os : List Nat}
    (h : ∀ (acc : Option Key), ∀ x ∈ o :: os,
      f acc x = some (incMax acc (key x)))
    (tail0 : Option Key) :
    (o :: os).foldl f tail0 =
      some (incMax tail0 (keysMax (key o) (os.map key))) := by
  rw [List.foldl_cons, h tail0 o (List.mem_cons_self ..)]
  have hrec := foldl_incMax os
    (fun acc x hx => h acc x (List.mem_cons_of_mem _ hx))
  rcases tail0 with _ | t
  · rw [show incMax none (key o) = key o from rfl, hrec]
    rfl
  · rw [show incMax (some t) (key o) = keyMax t (key o) from rfl, hrec,
      keysMax_keyMax]
    rfl

/-! # Dropping covered positions preserves the sweep maximum -/

theorem surviving_key {p : Nat → Bool} {key : Nat → Key} {m : Nat}
    (hcov : ∀ o, o < m → p o = false → ∃ o', o' < o ∧ key o' = key o) :
    ∀ (fuel o : Nat), o ≤ fuel → o < m →
      ∃ o'', o'' ≤ o ∧ p o'' = true ∧ key o'' = key o
  | fuel, o, hof, hom => by
    rcases hp : p o with _ | _
    · obtain ⟨o', ho', hk⟩ := hcov o hom hp
      rcases fuel with _ | fuel
      · omega
      · obtain ⟨o'', h1, h2, h3⟩ := surviving_key hcov fuel o'
          (by omega) (by omega)
        exact ⟨o'', by omega, h2, h3.trans hk⟩
    · exact ⟨o, Nat.le_refl o, hp, rfl⟩

theorem keysMax_head_filter {key : Nat → Key} {p : Nat → Bool} {m : Nat}
    (hcov : ∀ o, o < m + 1 → p o = false →
      ∃ o', o' < o ∧ key o' = key o) :
    keysMax (key 0) ((((List.range m).map (· + 1)).filter p).map key) =
      keysMax (key 0) (((List.range m).map (· + 1)).map key) := by
  refine keyLe_antisym
    (keysMax_le (keyLe_keysMax (Or.inl rfl)) fun y hy => ?_)
    (keysMax_le (keyLe_keysMax (Or.inl rfl)) fun y hy => ?_)
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy
    exact keyLe_keysMax (Or.inr
      (List.mem_map.mpr ⟨o, (List.mem_filter.mp ho).1, rfl⟩))
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ho
    have hjm := List.mem_range.mp hj
    obtain ⟨o'', ho''le, hps, hk⟩ := surviving_key hcov (j + 1) (j + 1)
      (Nat.le_refl _) (by omega)
    rw [← hk]
    rcases Nat.eq_zero_or_pos o'' with rfl | hpos
    · exact keyLe_keysMax (Or.inl rfl)
    · refine keyLe_keysMax (Or.inr (List.mem_map.mpr
        ⟨o'', List.mem_filter.mpr ⟨?_, hps⟩, rfl⟩))
      exact List.mem_map.mpr
        ⟨o'' - 1, List.mem_range.mpr (by omega), by omega⟩

/-! # A pruned position's key repeats an earlier sibling's -/

theorem childKey_of_autPruned {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ ctx.n = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o : Nat}
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (hlf : level + 1 + fuel ≤ n + 1)
    (hpr : autPruned ctx.n gens rsLab rsPtn level tc o = true) :
    ∃ o', o' < o ∧
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' =
        childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o := by
  rw [autPruned] at hpr
  obtain ⟨o', ho'm, h2⟩ := List.any_eq_true.mp hpr
  have ho'o := List.mem_range.mp ho'm
  obtain ⟨γ, hγm, hCells⟩ := List.any_eq_true.mp h2
  have hAut := hv γ hγm
  rw [hn] at hAut hCells
  obtain ⟨σ, hσeq, hσrows⟩ := checkAutom_sound hgsz hAut
  have hokc := childNodeOk hs hok hsp hend hvals hic hrange ho
  have hokc' := childNodeOk hs hok hsp hend hvals hic hrange
    (show o' < lenT by omega)
  have hmapeq : ((breakout rsLab rsPtn (level + 1) tc
        rsLab[tc + o]!).1.map fun w => γ[w]!) =
      (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1.map
        σ.toFun :=
    map_congr_of_labOk hokc.labOk (fun w hw => (hσeq w hw).symm)
  rw [hmapeq] at hCells
  have hcp := checkCellsPerm_sound
    (ptn := (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1)
    (lab₁ := (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1)
    (lab₂' := (breakout rsLab rsPtn (level + 1) tc
      rsLab[tc + o]!).1.map σ.toFun)
    (level := level + 1)
    hokc.ptnSize hokc'.labSize
    (by rw [Array.size_map]; exact hokc.labSize)
    hokc.ptnEnd hCells
  have hkeyeq : childKey ctx tcLevel fuel level rsLab rsPtn tc
      numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' :=
    specNode_autom hn hσrows tcLevel fuel (level + 1)
      (lab₁ := (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1)
      (lab₂ := (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1)
      (ptn := (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1)
      (active := (breakout rsLab rsPtn (level + 1) tc
        rsLab[tc + o]!).2.2)
      (numcells := numcells + 1) hcp hokc'.labSize hokc.labSize
      hokc'.labOk hokc.labOk hokc.ptnSize hokc.act hokc.ptnEnd
      hokc.starts hokc.vals (by omega)
  exact ⟨o', ho'o, hkeyeq.symm⟩

/-! # Both prunes are lossless -/

mutual

/-- One pruned step at a refined state computes the incumbent maximum
against the unpruned node key, the node's leading code absorbed on
both sides. -/
theorem stepA_eq {ctx : Ctx} (hn : ctx.n = n) (hgsz : ctx.g.size = n)
    {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ ctx.n = true) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (tail0 : Option Key),
      NodeOk n level lab ptn active → level + (fuel + 1) ≤ n + 1 →
      stepA ctx tcLevel gens fuel level
          (refine ctx level lab ptn active numcells) tail0 =
        incMax (tail0.map fun t =>
            (⟨(refine ctx level lab ptn active numcells).longcode ::
              t.codes, t.rows⟩ : Key))
          (specNode ctx tcLevel (fuel + 1) level lab ptn active
            numcells)
  | fuel, level, lab, ptn, active, numcells, tail0 => by
    intro hok hlf
    rcases hdisc : discreteAt
        (refine ctx level lab ptn active numcells).ptn level ctx.n
      with _ | _
    · -- live node: sweep the target cell, skipping pruned positions
      have hstR := refine_stOk (ctx := ctx) hn (level := level)
        (numcells := numcells) hok.labSize hok.labOk hok.ptnSize
        hok.act hok.ptnEnd
      have hRvals : ∀ q : Nat,
          (refine ctx level lab ptn active numcells).ptn[q]! ≤ level ∨
          (refine ctx level lab ptn active numcells).ptn[q]! =
            n + 2 := by
        intro q
        rcases ptn_refine_vals ctx level lab ptn active numcells q
          with he | he
        · rw [he]
          exact hok.vals q
        · rw [he]
          exact Or.inl (Nat.le_refl level)
      obtain ⟨p, hptc, hp12, hpb, hicp, hce⟩ := targetcell_facts hn
        (tcLevel := tcLevel)
        (refine ctx level lab ptn active numcells).lab hstR.ptnSize
        hstR.ptnEnd hdisc
      have hM1 : (specMaketargetcell ctx
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn level
            tcLevel).1 = p.1 := hptc
      have hM22 : (specMaketargetcell ctx
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn level
            tcLevel).2.2 = p.2 + 1 - p.1 := by
        show cellEnd (refine ctx level lab ptn active numcells).ptn
          level (specTargetcell ctx
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn level
              tcLevel + 1) -
          specTargetcell ctx
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn level
              tcLevel + 1 =
          p.2 + 1 - p.1
        rw [hptc, hce]
        omega
      obtain ⟨m, hm⟩ : ∃ m, p.2 + 1 - p.1 = m + 1 :=
        ⟨p.2 - p.1, by omega⟩
      rw [stepA]
      simp only [hdisc, Bool.false_eq_true, ite_false]
      rw [hM1, hM22, hm, List.range_succ_eq_map,
        List.filter_cons_of_pos (by simp [autPruned])]
      have hpt : ∀ (acc : Option Key), ∀ x ∈ (0 : Nat) ::
          ((List.range m).map (· + 1)).filter (fun o =>
            !autPruned ctx.n gens
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
              p.1 o),
          (fun (acc : Option Key) o =>
            some (searchNodeA ctx tcLevel gens fuel (level + 1)
              (breakout (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn
                (level + 1) p.1
                (refine ctx level lab ptn active
                  numcells).lab[p.1 + o]!).1
              (breakout (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn
                (level + 1) p.1
                (refine ctx level lab ptn active
                  numcells).lab[p.1 + o]!).2.1
              (breakout (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn
                (level + 1) p.1
                (refine ctx level lab ptn active
                  numcells).lab[p.1 + o]!).2.2
              ((refine ctx level lab ptn active numcells).numcells + 1)
              acc)) acc x =
          some (incMax acc (childKey ctx tcLevel fuel level
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn p.1
            (refine ctx level lab ptn active numcells).numcells x)) := by
        intro acc x hx
        have hxlt : x < m + 1 := by
          rcases List.mem_cons.mp hx with rfl | hx'
          · omega
          · obtain ⟨j, hj, rfl⟩ :=
              List.mem_map.mp (List.mem_filter.mp hx').1
            have := List.mem_range.mp hj
            omega
        have hokc := childNodeOk hstR.labSize hstR.labOk hstR.ptnSize
          hstR.ptnEnd hRvals hicp (by omega)
          (show x < p.2 + 1 - p.1 by omega)
        exact congrArg some (searchNodeA_eq hn hgsz hv tcLevel fuel
          (level + 1) _ _ _ _ acc hokc (by omega))
      rw [foldl_incMax_cons hpt tail0]
      have hcov : ∀ o, o < m + 1 →
          (fun o => !autPruned ctx.n gens
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn level
            p.1 o) o = false →
          ∃ o', o' < o ∧
            childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells o' =
            childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells o := by
        intro o hom hpf
        have hpf' : (!autPruned ctx.n gens
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn level
            p.1 o) = false := hpf
        have hpr : autPruned ctx.n gens
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn level
            p.1 o = true := by
          rcases hb : autPruned ctx.n gens
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn level
              p.1 o with _ | _
          · rw [hb] at hpf'
            cases hpf'
          · rfl
        exact childKey_of_autPruned hn hgsz hv tcLevel fuel level
          hstR.labSize hstR.labOk hstR.ptnSize hstR.ptnEnd hRvals hicp
          (by omega) (by omega) (by omega) hpr
      rw [keysMax_head_filter hcov]
      have hspec : specNode ctx tcLevel (fuel + 1) level lab ptn
          active numcells =
          ⟨(refine ctx level lab ptn active numcells).longcode ::
            (keysMax (childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells 0)
              (((List.range m).map (· + 1)).map fun o =>
                childKey ctx tcLevel fuel level
                  (refine ctx level lab ptn active numcells).lab
                  (refine ctx level lab ptn active numcells).ptn p.1
                  (refine ctx level lab ptn active numcells).numcells
                  o)).codes,
            (keysMax (childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells 0)
              (((List.range m).map (· + 1)).map fun o =>
                childKey ctx tcLevel fuel level
                  (refine ctx level lab ptn active numcells).lab
                  (refine ctx level lab ptn active numcells).ptn p.1
                  (refine ctx level lab ptn active numcells).numcells
                  o)).rows⟩ := by
        rw [specNode]
        simp only [hdisc, Bool.false_eq_true, ite_false]
        rw [hM1, hM22, hm, List.range_succ_eq_map, List.map_cons]
      rw [hspec, incMax_cons, key_eta]
    · -- discrete node: leaf comparison
      rw [stepA]
      simp only [hdisc, ite_true]
      have hspec : specNode ctx tcLevel (fuel + 1) level lab ptn
          active numcells =
          ⟨(refine ctx level lab ptn active numcells).longcode ::
            [codeSentinel],
            leafRows ctx (refine ctx level lab ptn active
              numcells).lab⟩ := by
        rw [specNode]
        simp only [hdisc, ite_true]
      rw [hspec, incMax_cons]
  termination_by fuel _ _ _ _ _ _ => (fuel, 1)

/-- The doubly-pruned branch-and-bound computes exactly the maximum of
the incumbent and the unpruned subtree key, for any store of checked
automorphisms of the rows. -/
theorem searchNodeA_eq {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ ctx.n = true) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (inc : Option Key),
      NodeOk n level lab ptn active → level + fuel ≤ n + 1 →
      searchNodeA ctx tcLevel gens fuel level lab ptn active numcells
          inc =
        incMax inc
          (specNode ctx tcLevel fuel level lab ptn active numcells)
  | 0, level, lab, ptn, active, numcells, none => by
    intro _ _
    rw [searchNodeA, specNode]
    rfl
  | 0, level, lab, ptn, active, numcells, some b => by
    intro _ _
    rw [searchNodeA, specNode, incMax, keyMax_bot_right]
    rfl
  | fuel + 1, level, lab, ptn, active, numcells, none => by
    intro hok hlf
    rw [searchNodeA,
      stepA_eq hn hgsz hv tcLevel fuel level lab ptn active numcells
        none hok hlf]
    rfl
  | fuel + 1, level, lab, ptn, active, numcells,
      some ⟨[], brows⟩ => by
    intro hok hlf
    rw [searchNodeA]
    simp only []
    rw [stepA_eq hn hgsz hv tcLevel fuel level lab ptn active numcells
      none hok hlf]
    obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel fuel
      level lab ptn active numcells
    refine (keyMax_eq_right (keyCmp_lt_of_nil rfl ?_)).symm
    show (specNode ctx tcLevel (fuel + 1) level lab ptn active
      numcells).codes ≠ []
    rw [hrest]
    simp
  | fuel + 1, level, lab, ptn, active, numcells,
      some ⟨bc :: brest, brows⟩ => by
    intro hok hlf
    rcases hcmp : compare (refine ctx level lab ptn active
        numcells).longcode bc with _ | _ | _
    · -- code prune: the whole subtree is dominated
      rw [searchNodeA]
      simp only []
      simp only [hcmp]
      rw [incMax,
        keyMax_eq_left (specNode_keyLe_of_code_lt tcLevel fuel
          brest brows (Nat.compare_eq_lt.mp hcmp))]
    · -- equal codes: descend, threading the incumbent's tail
      have hbc : (refine ctx level lab ptn active
          numcells).longcode = bc := Nat.compare_eq_eq.mp hcmp
      rw [searchNodeA]
      simp only []
      simp only [hcmp]
      rw [stepA_eq hn hgsz hv tcLevel fuel level lab ptn active
        numcells (some ⟨brest, brows⟩) hok hlf]
      rw [incMax, ← hbc]
      rfl
    · -- incumbent's code is smaller: descend unpruned, subtree wins
      rw [searchNodeA]
      simp only []
      simp only [hcmp]
      rw [stepA_eq hn hgsz hv tcLevel fuel level lab ptn active
        numcells none hok hlf]
      obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel fuel
        level lab ptn active numcells
      have hkey : specNode ctx tcLevel (fuel + 1) level lab ptn
          active numcells =
          ⟨(refine ctx level lab ptn active numcells).longcode ::
            rest,
          (specNode ctx tcLevel (fuel + 1) level lab ptn active
            numcells).rows⟩ := by
        rw [← hrest]
      rw [hkey]
      exact (keyMax_eq_right (keyCmp_cons_lt
        (Nat.compare_eq_gt.mp hcmp) brest rest brows _)).symm
  termination_by fuel _ _ _ _ _ _ => (fuel, 0)

end

/-! # The verified doubly-pruned evaluator at the root -/

/-- The doubly-pruned search from an empty incumbent and a generator
store: skips code-dominated subtrees and generator-repeated sibling
positions. -/
@[expose] def searchCanonA (n : Nat) (gens : List (Array Nat))
    (g lab0 : Array Nat) (cellEnds : List Nat) : Key :=
  if n == 0 then
    ⟨[], []⟩
  else
    searchNodeA { n, g } 100 gens n 1 lab0 (initPtn n (n + 2) cellEnds)
      (initActive cellEnds) cellEnds.length none

/-- For any store of checked automorphisms of the rows, the
doubly-pruned search computes the nauty-semantic canonical key. -/
theorem searchCanonA_key (G : Colored n k) {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom (rowsOf G) γ n = true) :
    searchCanonA n gens (rowsOf G) (initialPartition G).1
      (initialPartition G).2 = canonSpecKey G := by
  rw [searchCanonA, canonSpecKey, canonSpec]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [ite_eq_left (by rfl), ite_eq_left (by rfl)]
  · rw [ite_eq_right (by simp; omega), ite_eq_right (by simp; omega)]
    exact searchNodeA_eq (ctx := { n := n, g := rowsOf G }) rfl
      (size_rowsOf G) hv 100 n 1 (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length none (initial_nodeOk G hn0)
      (by show 1 + n ≤ n + 1; omega)

end Hex.GraphIso.Nauty
