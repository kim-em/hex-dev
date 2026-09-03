/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchAutom
public import HexGraphIso.Nauty.Translator
public import HexGraphIso.Nauty.Achieved
public import HexGraphIso.Nauty.SpecIso

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

The second half of the file justifies the orbit-partition (`fmptn`)
discipline: `orbPruned` skips a child whose target vertex reaches an
earlier sibling's under forward closure of the store, exhibiting no
single carrying generator. `childKey_of_orbPruned` shows the skipped
subtree's key repeats the earlier sibling's: the orbit path composes
to a checked automorphism (`wordPerm_spec`, on `checkAutom_range` and
`checkAutom_compose`; forward words suffice because permutations of a
finite set generate a group under composition alone) that still fixes
every cell of the node's partition setwise (`CellStab`, closed under
composition by `cellStab_comp`), and such a composite carries one
breakout labelling to the other cell by cell (`cellsPerm_set!` on the
split partition), so `specNode_autom` transports the key.

The cell-stabilization hypothesis is per node: it holds for the
generators nauty's bookkeeping admits at a node (automorphisms found
below fix the node's cells setwise), but propagating it through
`refine` and descent — and filtering the store as the individualized
base grows — is the transcription-side accounting that belongs to the
B2 simulation, so no recursive orbit-pruned evaluator is wired here.
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
theorem checkAutom_bound {g γ : Array Nat}
    (h : checkAutom g γ n = true) : ∀ v, v < n → γ[v]! < n := by
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
theorem wordPerm_spec {g ptn lab : Array Nat} {level : Nat}
    (hb : ∀ v, v < n → g[v]! < 2 ^ n) (hok : LabOk lab n)
    (hsp : ptn.size = n) (hs : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    {S : List (Array Nat)}
    (hv : ∀ γ ∈ S, checkAutom g γ n = true)
    (hstab : ∀ γ ∈ S, CellStab ptn level lab γ) :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ S) →
      checkAutom g (wordPerm n w) n = true ∧
      CellStab ptn level lab (wordPerm n w) ∧
      ∀ v, v < n → (wordPerm n w)[v]! = applyWord w v
  | [], _ =>
    ⟨checkAutom_range hb, cellStab_range hok, fun v hv' => by
      rw [wordPerm, applyWord, List.foldl_nil,
        getElem!_pos _ _ (by simpa using hv'), Array.getElem_range]⟩
  | γ :: w, hmem => by
    obtain ⟨h1, h2, h3⟩ := wordPerm_spec hb hok hsp hs hend hv hstab
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
    (s : Nat) : Nat :=
  gens.foldl (fun acc γ =>
    (List.range nn).foldl (fun acc w =>
      if s.testBit w then insert acc γ[w]! else acc) acc) s

/-- Iterated forward closure of a vertex set under the store. Any
fuel is sound; `nn` rounds saturate. -/
@[expose] def orbitClose (nn : Nat) (gens : List (Array Nat)) :
    Nat → Nat → Nat
  | 0, s => s
  | fuel + 1, s => orbitClose nn gens fuel (orbitStepSet nn gens s)

theorem orbitStepSet_sound {nn : Nat} {gens : List (Array Nat)}
    {s : Nat} :
    ∀ x, (orbitStepSet nn gens s).testBit x = true →
      s.testBit x = true ∨
        ∃ γ ∈ gens, ∃ u, s.testBit u = true ∧ γ[u]! = x := by
  refine foldl_invariant (P := fun acc => ∀ x,
      acc.testBit x = true → s.testBit x = true ∨
        ∃ γ ∈ gens, ∃ u, s.testBit u = true ∧ γ[u]! = x)
    gens s (fun x hx => Or.inl hx) ?_
  intro acc γ hγ hacc
  refine foldl_invariant (P := fun acc => ∀ x,
      acc.testBit x = true → s.testBit x = true ∨
        ∃ γ ∈ gens, ∃ u, s.testBit u = true ∧ γ[u]! = x)
    (List.range nn) acc hacc ?_
  intro a w hw ha x hx
  split at hx
  · next hcond =>
    rw [testBit_insert] at hx
    simp only [Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with h | h
    · exact ha x h
    · exact Or.inr ⟨γ, hγ, w, hcond, h⟩
  · exact ha x hx

theorem orbitClose_sound {nn : Nat} {gens : List (Array Nat)} :
    ∀ (fuel s x : Nat),
      (orbitClose nn gens fuel s).testBit x = true →
      ∃ u w, s.testBit u = true ∧ (∀ γ ∈ w, γ ∈ gens) ∧
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
    (orbitClose nn gens nn (insert 0 rsLab[tc + o]!)).testBit
      rsLab[tc + o']!

/-- An orbit-pruned position's key repeats an earlier sibling's: the
orbit path composes to a checked, cell-stabilizing automorphism
carrying one breakout labelling to the other, and `specNode_autom`
transports the subtree key. This is the justification of the
`fmptn` discipline at one node. -/
theorem childKey_of_orbPruned {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) (hb : ∀ v, v < n → ctx.g[v]! < 2 ^ n)
    {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ ctx.n = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o : Nat}
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (hlf : level + 1 + fuel ≤ n + 1)
    (hpr : orbPruned ctx.n gens rsLab tc o = true) :
    ∃ o', o' < o ∧
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' =
        childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o := by
  rw [orbPruned, hn] at hpr
  obtain ⟨o', ho'm, hbit⟩ := List.any_eq_true.mp hpr
  have ho'o := List.mem_range.mp ho'm
  -- the orbit path composes to a carrying automorphism
  obtain ⟨u, wγ, hu, hwmem, happ⟩ := orbitClose_sound _ _ _ hbit
  have huv : u = rsLab[tc + o]! := by
    rw [testBit_insert] at hu
    simp only [Nat.zero_testBit, Bool.false_or, beq_iff_eq] at hu
    exact hu.symm
  rw [huv] at happ
  have hv' : ∀ γ ∈ gens, checkAutom ctx.g γ n = true := by
    intro γ hγ
    have := hv γ hγ
    rwa [hn] at this
  obtain ⟨hAutC, hstabC, hpointC⟩ := wordPerm_spec hb hok hsp hs hend
    hv' hstab wγ hwmem
  have hvO : rsLab[tc + o]! < n := hok _ (by omega)
  have hvO' : rsLab[tc + o']! < n := hok _ (by omega)
  obtain ⟨σ, hσeq, hσrows⟩ := checkAutom_sound hgsz hAutC
  have hσvO : σ.toFun rsLab[tc + o]! = rsLab[tc + o']! := by
    rw [hσeq _ hvO, hpointC _ hvO, happ]
  obtain ⟨L, rfl⟩ : ∃ L, lenT = L + 1 := ⟨lenT - 1, by omega⟩
  -- breakout heads and tails on the target cell
  have hbsz : (breakout rsLab rsPtn (level + 1) tc
      rsLab[tc + o]!).1.size = n := by
    show (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
      rsLab[tc + o]!).size = n
    rw [breakout_go_size, hs]
  have hsegO : segN (breakout rsLab rsPtn (level + 1) tc
      rsLab[tc + o]!).1 tc (L + 1) =
      rsLab[tc + o]! :: (segN rsLab tc (L + 1)).erase rsLab[tc + o]! := by
    show segN (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
      rsLab[tc + o]!) tc (L + 1) = _
    exact breakout_go_seg (rsLab.size + 1) (L + 1) rsLab tc
      rsLab[tc + o]! ⟨tc + o, by omega, by omega, by omega, rfl⟩
      (by omega) (by omega)
  have hsegO' : segN (breakout rsLab rsPtn (level + 1) tc
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
      (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1
      ((breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1.map
        σ.toFun) := by
    refine cellsPerm_set! hicS (by omega) (Nat.le_refl tc)
      (by omega) ?_ ?_ ?_
    · -- the individualized singletons agree under σ
      rw [show tc + 1 - tc = 1 by omega, segN_cons, segN_zero,
        segN_cons, segN_zero, hheadO',
        getElem!_map_of_lt σ.toFun _ (by rw [hbsz]; omega), hheadO,
        hσvO]
    · -- the remainder cells erase the two vertices and transport
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
      have hlabO'eq : segN (breakout rsLab rsPtn (level + 1) tc
          rsLab[tc + o']!).1 a l = segN rsLab a l := by
        refine segN_congr fun q hq => ?_
        show (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
          rsLab[tc + o']!)[a + q]! = rsLab[a + q]!
        rcases hdisj with hd | hd
        · exact breakout_go_outside _ _ _ _ _ (by omega)
        · exact breakout_go_outside_right _ (L + 1) _ _ _
            ⟨tc + o', by omega, by omega, by omega, rfl⟩ _ (by omega)
      have hlabOeq : segN (breakout rsLab rsPtn (level + 1) tc
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
          getElem!_neg ((breakout rsLab rsPtn (level + 1) tc
              rsLab[tc + o]!).1.map σ.toFun) a
            (by rw [Array.size_map, hbsz]; omega)]
  -- transport the subtree key along the composite automorphism
  have hokc := childNodeOk hs hok hsp hend hvals hic hrange ho
  have hokc' := childNodeOk hs hok hsp hend hvals hic hrange
    (show o' < (L + 1) by omega)
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

end Hex.GraphIso.Nauty
