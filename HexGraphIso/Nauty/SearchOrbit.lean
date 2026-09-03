/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchAutom

public section

/-!
The growing-store refinement of the automorphism-pruned model search:
where `searchNodeA` prunes against a fixed generator store,
`searchNodeG` threads the store through the recursion so a generator
admitted at a leaf prunes later siblings of every sweep on the path
back up — including later siblings of the sweep that discovered it,
as the transcription's store does. Admission is abstract: an oracle
`adm` proposes generators from each discrete leaf's labelling and the
incumbent, and every theorem holds for any oracle whose proposals
pass `checkAutom`. `searchNodeG_eq` shows the recursion still
computes `incMax inc (specNode …)` and that store validity is an
invariant; `searchCanonG_key` packages the root call as a verified
evaluator of `canonSpecKey`.

The orbit-partition (`fmptn`) discipline — skipping every later
member of a known orbit rather than testing stored generators
pairwise, justified by a composite of generators rather than a single
one — refines the prune test itself and builds on the store threading
here.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Every stored generator passes the executable automorphism check
against the context's rows. -/
@[expose] def ValidStore (ctx : Ctx) (S : List (Array Nat)) : Prop :=
  ∀ γ ∈ S, checkAutom ctx.g γ ctx.n = true

theorem validStore_append {ctx : Ctx} {S T : List (Array Nat)}
    (hS : ValidStore ctx S) (hT : ValidStore ctx T) :
    ValidStore ctx (S ++ T) := by
  intro γ hγ
  rcases List.mem_append.mp hγ with h | h
  · exact hS γ h
  · exact hT γ h

/-! # The search with a threaded, growing store -/

mutual

/-- The child sweep with a growing store: each unpruned child is
searched with the store as it stands, and the store it returns —
possibly grown at leaves below — is what later siblings are pruned
against. -/
@[expose] def sweepG (ctx : Ctx) (tcLevel : Nat)
    (adm : Array Nat → Option Key → List (Array Nat))
    (fuel level : Nat) (rsLab rsPtn : Array Nat)
    (tc numcells : Nat) :
    List Nat → Key × List (Array Nat) → Key × List (Array Nat)
  | [], acc => acc
  | o :: os, acc =>
    if autPruned ctx.n acc.2 rsLab rsPtn level tc o then
      sweepG ctx tcLevel adm fuel level rsLab rsPtn tc numcells os acc
    else
      let br := breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!
      let r := searchNodeG ctx tcLevel adm fuel (level + 1) br.1
        br.2.1 br.2.2 (numcells + 1) (some acc.1) acc.2
      sweepG ctx tcLevel adm fuel level rsLab rsPtn tc numcells os r
  termination_by os _ => (fuel, 1, os.length)

/-- One node step at a refined state: at a discrete leaf the oracle's
proposals join the store; at a live node the first child absorbs the
incumbent and the sweep threads the store across the rest. -/
@[expose] def stepG (ctx : Ctx) (tcLevel : Nat)
    (adm : Array Nat → Option Key → List (Array Nat))
    (fuel level : Nat) (rs : RefineSt) (tail0 : Option Key)
    (S : List (Array Nat)) : Key × List (Array Nat) :=
  if discreteAt rs.ptn level ctx.n then
    let t' := incMax tail0 ⟨[codeSentinel], leafRows ctx rs.lab⟩
    (⟨rs.longcode :: t'.codes, t'.rows⟩, S ++ adm rs.lab tail0)
  else
    let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
    let br := breakout rs.lab rs.ptn (level + 1) tcr.1
      rs.lab[tcr.1 + 0]!
    let r0 := searchNodeG ctx tcLevel adm fuel (level + 1) br.1
      br.2.1 br.2.2 (rs.numcells + 1) tail0 S
    let r := sweepG ctx tcLevel adm fuel level rs.lab rs.ptn tcr.1
      rs.numcells (List.range' 1 (tcr.2.2 - 1)) r0
    (⟨rs.longcode :: r.1.codes, r.1.rows⟩, r.2)
  termination_by (fuel, 2, 0)

/-- Branch-and-bound with code prune, generator prune, and a store
that grows at leaves and travels forward through the search order. -/
@[expose] def searchNodeG (ctx : Ctx) (tcLevel : Nat)
    (adm : Array Nat → Option Key → List (Array Nat)) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → Option Key →
      List (Array Nat) → Key × List (Array Nat)
  | 0, _, _, _, _, _, inc, S => (inc.getD ⟨[], []⟩, S)
  | fuel + 1, level, lab, ptn, active, numcells, none, S =>
    stepG ctx tcLevel adm fuel level
      (refine ctx level lab ptn active numcells) none S
  | fuel + 1, level, lab, ptn, active, numcells, some b, S =>
    let rs := refine ctx level lab ptn active numcells
    match b.codes with
    | [] => stepG ctx tcLevel adm fuel level rs none S
    | bc :: brest =>
      match compare rs.longcode bc with
      | .lt => (b, S)
      | .gt => stepG ctx tcLevel adm fuel level rs none S
      | .eq => stepG ctx tcLevel adm fuel level rs
          (some ⟨brest, b.rows⟩) S
  termination_by fuel _ _ _ _ _ _ _ => (fuel, 0, 0)

end

/-! # Key-maximum bookkeeping for the interleaved sweep -/

theorem keysMax_concat (k y : Key) : ∀ (l : List Key),
    keysMax k (l ++ [y]) = keyMax (keysMax k l) y
  | [] => rfl
  | c :: l => by
    rw [List.cons_append, keysMax, keysMax, keysMax_concat]

theorem incMax_keyMax (tail0 : Option Key) (m y : Key) :
    keyMax (incMax tail0 m) y = incMax tail0 (keyMax m y) := by
  rcases tail0 with _ | b
  · rfl
  · exact keyMax_assoc b m y

/-- The maximum over child positions `0..j` collapses to the maximum
over `0..j-1` when position `j`'s key repeats an earlier one. -/
theorem keysMax_range'_covered {key : Nat → Key} {j : Nat}
    (hj : 1 ≤ j) (hcov : ∃ o', o' < j ∧ key o' = key j) :
    keysMax (key 0) ((List.range' 1 j).map key) =
      keysMax (key 0) ((List.range' 1 (j - 1)).map key) := by
  obtain ⟨o', ho', hk⟩ := hcov
  have hsplit : List.range' 1 j = List.range' 1 (j - 1) ++ [j] := by
    have h := List.range'_1_concat (s := 1) (n := j - 1)
    rw [show j - 1 + 1 = j from by omega,
      show 1 + (j - 1) = j from by omega] at h
    exact h
  rw [hsplit, List.map_append, List.map_cons, List.map_nil,
    keysMax_concat]
  refine keyMax_eq_left ?_
  rw [← hk]
  rcases Nat.eq_zero_or_pos o' with rfl | hpos
  · exact keyLe_keysMax (Or.inl rfl)
  · exact keyLe_keysMax (Or.inr (List.mem_map.mpr
      ⟨o', List.mem_range'_1.mpr ⟨hpos, by omega⟩, rfl⟩))

/-- Child positions `1..m` as a shifted range. -/
theorem map_range'_one {α : Type} (f : Nat → α) (m : Nat) :
    (List.range' 1 m).map f = ((List.range m).map (· + 1)).map f := by
  rw [List.range'_eq_map_range, List.map_map, List.map_map]
  exact List.map_congr_left (fun a _ => by
    show f (1 + a) = f (a + 1)
    rw [Nat.add_comm])

/-- Extending the maximum over `0..j-1` by position `j`'s key gives
the maximum over `0..j`. -/
theorem keysMax_range'_snoc {key : Nat → Key} {j : Nat} (hj : 1 ≤ j) :
    keyMax (keysMax (key 0) ((List.range' 1 (j - 1)).map key))
        (key j) =
      keysMax (key 0) ((List.range' 1 j).map key) := by
  have hsplit : List.range' 1 j = List.range' 1 (j - 1) ++ [j] := by
    have h := List.range'_1_concat (s := 1) (n := j - 1)
    rw [show j - 1 + 1 = j from by omega,
      show 1 + (j - 1) = j from by omega] at h
    exact h
  rw [hsplit, List.map_append, List.map_cons, List.map_nil,
    keysMax_concat]

/-! # Both prunes stay lossless with a growing store -/

mutual

/-- The sweep from position `j` with a valid store computes the full
sweep maximum: pruned positions are covered by earlier keys via the
store valid at the moment of the test, and the store stays valid as
it grows through the children. -/
theorem sweepG_eq {ctx : Ctx} (hn : ctx.n = n) (hgsz : ctx.g.size = n)
    {adm : Array Nat → Option Key → List (Array Nat)}
    (hadm : ∀ lab inc, ValidStore ctx (adm lab inc)) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (rsLab rsPtn : Array Nat)
      (tc m numcells : Nat) (tail0 : Option Key) (c j : Nat)
      (acc : Key × List (Array Nat)),
      rsLab.size = n → LabOk rsLab n → rsPtn.size = n →
      rsPtn[rsPtn.size - 1]! ≤ level →
      (∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2) →
      IsCell rsPtn level tc (m + 1) → tc + (m + 1) ≤ n →
      level + 1 + fuel ≤ n + 1 →
      j + c = m + 1 → 1 ≤ j → ValidStore ctx acc.2 →
      acc.1 = incMax tail0 (keysMax
        (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells 0)
        ((List.range' 1 (j - 1)).map
          (childKey ctx tcLevel fuel level rsLab rsPtn tc
            numcells))) →
      (sweepG ctx tcLevel adm fuel level rsLab rsPtn tc numcells
          (List.range' j c) acc).1 =
        incMax tail0 (keysMax
          (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells 0)
          ((List.range' 1 m).map
            (childKey ctx tcLevel fuel level rsLab rsPtn tc
              numcells))) ∧
      ValidStore ctx (sweepG ctx tcLevel adm fuel level rsLab rsPtn
        tc numcells (List.range' j c) acc).2
  | fuel, level, rsLab, rsPtn, tc, m, numcells, tail0, 0, j, acc => by
    intro hs hok hsp hend hvals hic hrange hlf hjc hj hS ht
    rw [List.range'_zero, sweepG]
    have hjm : j - 1 = m := by omega
    rw [hjm] at ht
    exact ⟨ht, hS⟩
  | fuel, level, rsLab, rsPtn, tc, m, numcells, tail0, c + 1, j,
      acc => by
    intro hs hok hsp hend hvals hic hrange hlf hjc hj hS ht
    rw [List.range'_succ, sweepG]
    rcases hpr : autPruned ctx.n acc.2 rsLab rsPtn level tc j
      with _ | _
    · -- unpruned: search the child with the current store
      simp only [Bool.false_eq_true, ite_false]
      have hokc := childNodeOk hs hok hsp hend hvals hic hrange
        (show j < m + 1 by omega)
      obtain ⟨hr1, hr2⟩ := searchNodeG_eq hn hgsz hadm tcLevel fuel
        (level + 1)
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + j]!).1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + j]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + j]!).2.2
        (numcells + 1) (some acc.1) acc.2 hokc (by omega) hS
      refine sweepG_eq hn hgsz hadm tcLevel fuel level rsLab rsPtn tc
        m numcells tail0 c (j + 1) _ hs hok hsp hend hvals hic
        hrange hlf (by omega) (by omega) hr2 ?_
      rw [hr1]
      show keyMax acc.1 (childKey ctx tcLevel fuel level rsLab rsPtn
        tc numcells j) = _
      rw [ht, incMax_keyMax, keysMax_range'_snoc hj,
        Nat.add_sub_cancel]
    · -- pruned: the skipped key repeats an earlier sibling's
      simp only [ite_true]
      have hcov := childKey_of_autPruned (numcells := numcells) hn
        hgsz hS tcLevel fuel level hs hok hsp hend hvals hic hrange
        (show j < m + 1 by omega) (by omega) hpr
      refine sweepG_eq hn hgsz hadm tcLevel fuel level rsLab rsPtn tc
        m numcells tail0 c (j + 1) acc hs hok hsp hend hvals hic
        hrange hlf (by omega) (by omega) hS ?_
      rw [ht, Nat.add_sub_cancel, keysMax_range'_covered hj hcov]
  termination_by fuel _ _ _ _ _ _ _ c => (fuel, 1, c + 1)

/-- One growing-store step at a refined state computes the incumbent
maximum against the unpruned node key. -/
theorem stepG_eq {ctx : Ctx} (hn : ctx.n = n) (hgsz : ctx.g.size = n)
    {adm : Array Nat → Option Key → List (Array Nat)}
    (hadm : ∀ lab inc, ValidStore ctx (adm lab inc)) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (tail0 : Option Key)
      (S : List (Array Nat)),
      NodeOk n level lab ptn active → level + (fuel + 1) ≤ n + 1 →
      ValidStore ctx S →
      (stepG ctx tcLevel adm fuel level
          (refine ctx level lab ptn active numcells) tail0 S).1 =
        incMax (tail0.map fun t =>
            (⟨(refine ctx level lab ptn active numcells).longcode ::
              t.codes, t.rows⟩ : Key))
          (specNode ctx tcLevel (fuel + 1) level lab ptn active
            numcells) ∧
      ValidStore ctx (stepG ctx tcLevel adm fuel level
        (refine ctx level lab ptn active numcells) tail0 S).2
  | fuel, level, lab, ptn, active, numcells, tail0, S => by
    intro hok hlf hS
    rcases hdisc : discreteAt
        (refine ctx level lab ptn active numcells).ptn level ctx.n
      with _ | _
    · -- live node: first child, then the threaded sweep
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
      rw [hm] at hicp
      rw [stepG]
      simp only [hdisc, Bool.false_eq_true, ite_false]
      rw [hM1, hM22, hm, Nat.add_sub_cancel]
      have hokc0 := childNodeOk hstR.labSize hstR.labOk hstR.ptnSize
        hstR.ptnEnd hRvals hicp (by omega)
        (show 0 < m + 1 by omega)
      obtain ⟨h01, h02⟩ := searchNodeG_eq hn hgsz hadm tcLevel fuel
        (level + 1)
        (breakout (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn (level + 1)
          p.1 (refine ctx level lab ptn active
            numcells).lab[p.1 + 0]!).1
        (breakout (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn (level + 1)
          p.1 (refine ctx level lab ptn active
            numcells).lab[p.1 + 0]!).2.1
        (breakout (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn (level + 1)
          p.1 (refine ctx level lab ptn active
            numcells).lab[p.1 + 0]!).2.2
        ((refine ctx level lab ptn active numcells).numcells + 1)
        tail0 S hokc0 (by omega) hS
      obtain ⟨hs1, hs2⟩ := sweepG_eq hn hgsz hadm tcLevel fuel level
        (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn p.1 m
        (refine ctx level lab ptn active numcells).numcells tail0
        m 1
        (searchNodeG ctx tcLevel adm fuel (level + 1)
          (breakout (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            p.1 (refine ctx level lab ptn active
              numcells).lab[p.1 + 0]!).1
          (breakout (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            p.1 (refine ctx level lab ptn active
              numcells).lab[p.1 + 0]!).2.1
          (breakout (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn (level + 1)
            p.1 (refine ctx level lab ptn active
              numcells).lab[p.1 + 0]!).2.2
          ((refine ctx level lab ptn active numcells).numcells + 1)
          tail0 S)
        hstR.labSize hstR.labOk hstR.ptnSize
        hstR.ptnEnd hRvals hicp (by omega) (by omega) (by omega)
        (Nat.le_refl 1) h02 (by rw [h01]; rfl)
      constructor
      · rw [hs1]
        have hspec : specNode ctx tcLevel (fuel + 1) level lab ptn
            active numcells =
            ⟨(refine ctx level lab ptn active numcells).longcode ::
              (keysMax (childKey ctx tcLevel fuel level
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn p.1
                (refine ctx level lab ptn active numcells).numcells 0)
                ((List.range' 1 m).map fun o =>
                  childKey ctx tcLevel fuel level
                    (refine ctx level lab ptn active numcells).lab
                    (refine ctx level lab ptn active numcells).ptn p.1
                    (refine ctx level lab ptn active
                      numcells).numcells o)).codes,
              (keysMax (childKey ctx tcLevel fuel level
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn p.1
                (refine ctx level lab ptn active numcells).numcells 0)
                ((List.range' 1 m).map fun o =>
                  childKey ctx tcLevel fuel level
                    (refine ctx level lab ptn active numcells).lab
                    (refine ctx level lab ptn active numcells).ptn p.1
                    (refine ctx level lab ptn active
                      numcells).numcells o)).rows⟩ := by
          rw [specNode]
          simp only [hdisc, Bool.false_eq_true, ite_false]
          rw [hM1, hM22, hm, List.range_succ_eq_map, List.map_cons,
            map_range'_one]
        rw [hspec, incMax_cons, key_eta]
      · exact hs2
    · -- discrete leaf: compare, and admit the oracle's proposals
      rw [stepG]
      simp only [hdisc, ite_true]
      refine ⟨?_, validStore_append hS (hadm _ _)⟩
      have hspec : specNode ctx tcLevel (fuel + 1) level lab ptn
          active numcells =
          ⟨(refine ctx level lab ptn active numcells).longcode ::
            [codeSentinel],
            leafRows ctx (refine ctx level lab ptn active
              numcells).lab⟩ := by
        rw [specNode]
        simp only [hdisc, ite_true]
      rw [hspec, incMax_cons]
  termination_by fuel _ _ _ _ _ _ _ => (fuel, 2, 0)

/-- The growing-store branch-and-bound computes exactly the maximum
of the incumbent and the unpruned subtree key, and returns a valid
store, for any valid initial store and any oracle proposing only
checked automorphisms. -/
theorem searchNodeG_eq {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n)
    {adm : Array Nat → Option Key → List (Array Nat)}
    (hadm : ∀ lab inc, ValidStore ctx (adm lab inc)) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (inc : Option Key)
      (S : List (Array Nat)),
      NodeOk n level lab ptn active → level + fuel ≤ n + 1 →
      ValidStore ctx S →
      (searchNodeG ctx tcLevel adm fuel level lab ptn active numcells
          inc S).1 =
        incMax inc
          (specNode ctx tcLevel fuel level lab ptn active numcells) ∧
      ValidStore ctx (searchNodeG ctx tcLevel adm fuel level lab ptn
        active numcells inc S).2
  | 0, level, lab, ptn, active, numcells, none, S => by
    intro _ _ hS
    rw [searchNodeG, specNode]
    exact ⟨rfl, hS⟩
  | 0, level, lab, ptn, active, numcells, some b, S => by
    intro _ _ hS
    rw [searchNodeG, specNode]
    refine ⟨?_, hS⟩
    rw [incMax, keyMax_bot_right]
    rfl
  | fuel + 1, level, lab, ptn, active, numcells, none, S => by
    intro hok hlf hS
    rw [searchNodeG]
    obtain ⟨h1, h2⟩ := stepG_eq hn hgsz hadm tcLevel fuel level lab
      ptn active numcells none S hok hlf hS
    exact ⟨h1, h2⟩
  | fuel + 1, level, lab, ptn, active, numcells,
      some ⟨[], brows⟩, S => by
    intro hok hlf hS
    rw [searchNodeG]
    simp only []
    obtain ⟨h1, h2⟩ := stepG_eq hn hgsz hadm tcLevel fuel level lab
      ptn active numcells none S hok hlf hS
    refine ⟨?_, h2⟩
    rw [h1]
    obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel fuel
      level lab ptn active numcells
    refine (keyMax_eq_right (keyCmp_lt_of_nil rfl ?_)).symm
    show (specNode ctx tcLevel (fuel + 1) level lab ptn active
      numcells).codes ≠ []
    rw [hrest]
    simp
  | fuel + 1, level, lab, ptn, active, numcells,
      some ⟨bc :: brest, brows⟩, S => by
    intro hok hlf hS
    rcases hcmp : compare (refine ctx level lab ptn active
        numcells).longcode bc with _ | _ | _
    · -- code prune: the whole subtree is dominated
      rw [searchNodeG]
      simp only []
      simp only [hcmp]
      refine ⟨?_, hS⟩
      rw [incMax,
        keyMax_eq_left (specNode_keyLe_of_code_lt tcLevel fuel
          brest brows (Nat.compare_eq_lt.mp hcmp))]
    · -- equal codes: descend, threading the incumbent's tail
      have hbc : (refine ctx level lab ptn active
          numcells).longcode = bc := Nat.compare_eq_eq.mp hcmp
      rw [searchNodeG]
      simp only []
      simp only [hcmp]
      obtain ⟨h1, h2⟩ := stepG_eq hn hgsz hadm tcLevel fuel level lab
        ptn active numcells (some ⟨brest, brows⟩) S hok hlf hS
      refine ⟨?_, h2⟩
      rw [h1, incMax, ← hbc]
      rfl
    · -- incumbent's code is smaller: descend unpruned, subtree wins
      rw [searchNodeG]
      simp only []
      simp only [hcmp]
      obtain ⟨h1, h2⟩ := stepG_eq hn hgsz hadm tcLevel fuel level lab
        ptn active numcells none S hok hlf hS
      refine ⟨?_, h2⟩
      rw [h1]
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
  termination_by fuel _ _ _ _ _ _ _ => (fuel, 0, 0)

end

/-! # The verified growing-store evaluator at the root -/

/-- The growing-store search from an empty incumbent: code prune,
generator prune, and a store seeded with `gens0` that grows at leaves
by the oracle's proposals. -/
@[expose] def searchCanonG (n : Nat)
    (adm : Array Nat → Option Key → List (Array Nat))
    (gens0 : List (Array Nat)) (g lab0 : Array Nat)
    (cellEnds : List Nat) : Key :=
  if n == 0 then
    ⟨[], []⟩
  else
    (searchNodeG { n, g } 100 adm n 1 lab0
      (initPtn n (n + 2) cellEnds) (initActive cellEnds)
      cellEnds.length none gens0).1

/-- For any valid seed store and any oracle proposing only checked
automorphisms, the growing-store search computes the nauty-semantic
canonical key. -/
theorem searchCanonG_key (G : Colored n k)
    {adm : Array Nat → Option Key → List (Array Nat)}
    (hadm : ∀ lab inc,
      ValidStore { n := n, g := rowsOf G } (adm lab inc))
    {gens0 : List (Array Nat)}
    (hv : ValidStore { n := n, g := rowsOf G } gens0) :
    searchCanonG n adm gens0 (rowsOf G) (initialPartition G).1
      (initialPartition G).2 = canonSpecKey G := by
  rw [searchCanonG, canonSpecKey, canonSpec]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [ite_eq_left (by rfl), ite_eq_left (by rfl)]
  · rw [ite_eq_right (by simp; omega), ite_eq_right (by simp; omega)]
    exact (searchNodeG_eq (ctx := { n := n, g := rowsOf G }) rfl
      (size_rowsOf G) hadm 100 n 1 (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length none gens0 (initial_nodeOk G hn0)
      (by show 1 + n ≤ n + 1; omega) hv).1

end Hex.GraphIso.Nauty
