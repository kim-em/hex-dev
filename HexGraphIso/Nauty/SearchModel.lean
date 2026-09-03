/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert

public section

/-!
Verification of the pruned branch-and-bound search: `searchNode`
threads an incumbent best key and skips any subtree whose refinement
code falls below the incumbent's code at its depth, exactly as the
transcription prunes on `code < canoncode[level]`. `searchNode_eq`
proves the pruned recursion computes the pairwise maximum of the
incumbent and the unpruned subtree key, with no side conditions, so
the root call is a verified pruned evaluator of `canonSpec`
(`searchCanon_eq`) and of `canonSpecKey` (`searchCanon_key`).
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # The key maximum is a semilattice operation -/

theorem keyCmp_bot_ne_gt (b : Key) : keyCmp ⟨[], []⟩ b ≠ .gt := by
  rw [keyCmp]
  rcases b with ⟨codes, rows⟩
  rcases codes with _ | ⟨c, cs⟩
  · rcases rows with _ | ⟨r, rs⟩ <;> simp [listCmp]
  · simp [listCmp]

theorem keyMax_bot_left (b : Key) : keyMax ⟨[], []⟩ b = b := by
  rw [keyMax]
  split
  · rfl
  · next h =>
    rcases hc : keyCmp ⟨[], []⟩ b with _ | _ | _
    · exact absurd hc h
    · exact keyCmp_eq_iff.mp hc
    · exact absurd hc (keyCmp_bot_ne_gt b)

theorem keyMax_bot_right (b : Key) : keyMax b ⟨[], []⟩ = b := by
  rw [keyMax]
  split
  · next h =>
    exact absurd (keyCmp_gt_iff_lt.mpr h) (keyCmp_bot_ne_gt b)
  · rfl

theorem keyMax_eq_left {b y : Key} (h : keyLe y b) : keyMax b y = b := by
  rw [keyMax]
  split
  · next hlt => exact absurd (keyCmp_gt_iff_lt.mpr hlt) h
  · rfl

theorem keyMax_eq_right {b y : Key} (h : keyCmp b y = .lt) :
    keyMax b y = y := by
  rw [keyMax, ite_eq_left h]

theorem keyMax_assoc (x y z : Key) :
    keyMax (keyMax x y) z = keyMax x (keyMax y z) := by
  refine keyCmp_antisym ?_ ?_
  · rcases keyMax_mem x (keyMax y z) with hm | hm <;> rw [hm]
    · exact keyCmp_ge_trans (keyMax_not_lt_left _ z)
        (keyMax_not_lt_left x y)
    · rcases keyMax_mem y z with hm2 | hm2 <;> rw [hm2]
      · exact keyCmp_ge_trans (keyMax_not_lt_left _ z)
          (keyMax_not_lt_right x y)
      · exact keyMax_not_lt_right _ z
  · rcases keyMax_mem (keyMax x y) z with hm | hm <;> rw [hm]
    · rcases keyMax_mem x y with hm2 | hm2 <;> rw [hm2]
      · exact keyMax_not_lt_left x (keyMax y z)
      · exact keyCmp_ge_trans (keyMax_not_lt_right x _)
          (keyMax_not_lt_left y z)
    · exact keyCmp_ge_trans (keyMax_not_lt_right x _)
        (keyMax_not_lt_right y z)

theorem keysMax_keyMax : ∀ (l : List Key) (b c : Key),
    keysMax (keyMax b c) l = keyMax b (keysMax c l)
  | [], _, _ => rfl
  | c' :: l, b, c => by
    rw [keysMax, keysMax, keyMax_assoc]
    exact keysMax_keyMax l b (keyMax c c')

/-! # First-code comparisons against a whole key -/

theorem keyCmp_lt_of_nil {b y : Key} (hb : b.codes = [])
    (hy : y.codes ≠ []) : keyCmp b y = .lt := by
  rw [keyCmp, hb]
  rcases hyc : y.codes with _ | ⟨c, cs⟩
  · exact absurd hyc hy
  · simp [listCmp]

/-- Prefixing a common code commutes with the key maximum. -/
theorem keyMax_cons (c : Nat) (cs cs' r r' : List Nat) :
    keyMax ⟨c :: cs, r⟩ ⟨c :: cs', r'⟩ =
      ⟨c :: (keyMax ⟨cs, r⟩ ⟨cs', r'⟩).codes,
        (keyMax ⟨cs, r⟩ ⟨cs', r'⟩).rows⟩ := by
  rw [keyMax, keyMax, keyCmp_cons_eq]
  split
  · rfl
  · rfl

/-! # The incumbent maximum -/

/-- The contract of one pruned search node: the incumbent absorbed
into the subtree's best key, an absent incumbent contributing
nothing. -/
@[expose] def incMax : Option Key → Key → Key
  | none, y => y
  | some b, y => keyMax b y

/-! # The pruned search computes the incumbent maximum -/

mutual

/-- The pruned branch-and-bound recursion computes exactly the
maximum of the incumbent and the unpruned subtree key: the code
prune is lossless. No side conditions. -/
theorem searchNode_eq (ctx : Ctx) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (inc : Option Key),
      searchNode ctx tcLevel fuel level lab ptn active numcells inc =
        incMax inc
          (specNode ctx tcLevel fuel level lab ptn active numcells)
  | 0, level, lab, ptn, active, numcells, none => by
    rw [searchNode, specNode, incMax]
    rfl
  | 0, level, lab, ptn, active, numcells, some b => by
    rw [searchNode, specNode, incMax, keyMax_bot_right]
    rfl
  | fuel + 1, level, lab, ptn, active, numcells, none => by
    rw [incMax, searchNode, specNode]
    simp only []
    rcases hdisc : discreteAt (refine ctx level lab ptn active
        numcells).ptn level ctx.n with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      obtain ⟨m, hm⟩ : ∃ m, (specMaketargetcell ctx
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn level
            tcLevel).2.2 = m + 1 := ⟨_, rfl⟩
      rw [hm, List.range_succ_eq_map,
        searchFold_cons ctx tcLevel fuel level _ _ _ _ _ _ none,
        List.map_cons]
      simp only [incMax]
    · simp only [ite_true]
  | fuel + 1, level, lab, ptn, active, numcells,
      some ⟨[], brows⟩ => by
    have hswitch : searchNode ctx tcLevel (fuel + 1) level lab ptn
        active numcells (some ⟨[], brows⟩) =
        searchNode ctx tcLevel (fuel + 1) level lab ptn active
          numcells none := by
      rw [searchNode, searchNode]
    rw [hswitch,
      searchNode_eq ctx tcLevel (fuel + 1) level lab ptn active
        numcells none,
      incMax, incMax]
    obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel fuel
      level lab ptn active numcells
    exact (keyMax_eq_right
      (keyCmp_lt_of_nil rfl (by rw [hrest]; simp))).symm
  | fuel + 1, level, lab, ptn, active, numcells,
      some ⟨bc :: brest, brows⟩ => by
    rcases hcmp : compare (refine ctx level lab ptn active
        numcells).longcode bc with _ | _ | _
    · -- code prune: the whole subtree is dominated
      rw [searchNode]
      simp only []
      simp only [hcmp]
      rw [incMax,
        keyMax_eq_left (specNode_keyLe_of_code_lt tcLevel fuel
          brest brows (Nat.compare_eq_lt.mp hcmp))]
    · -- equal codes: descend, threading the incumbent's tail
      have hbc : (refine ctx level lab ptn active
          numcells).longcode = bc := Nat.compare_eq_eq.mp hcmp
      rw [searchNode, incMax, specNode]
      simp only []
      simp only [hcmp]
      rcases hdisc : discreteAt (refine ctx level lab ptn active
          numcells).ptn level ctx.n with _ | _
      · simp only [Bool.false_eq_true, ite_false]
        obtain ⟨m, hm⟩ : ∃ m, (specMaketargetcell ctx
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn level
              tcLevel).2.2 = m + 1 := ⟨_, rfl⟩
        rw [hm, List.range_succ_eq_map,
          searchFold_cons ctx tcLevel fuel level _ _ _ _ _ _
            (some ⟨brest, brows⟩),
          List.map_cons]
        simp only [incMax]
        rw [← hbc, keyMax_cons]
      · simp only [ite_true]
        rw [← hbc, keyMax_cons]
    · -- incumbent's code is smaller: descend unpruned, subtree wins
      have hswitch : searchNode ctx tcLevel (fuel + 1) level lab ptn
          active numcells (some ⟨bc :: brest, brows⟩) =
          searchNode ctx tcLevel (fuel + 1) level lab ptn active
            numcells none := by
        rw [searchNode, searchNode]
        simp only []
        simp only [hcmp]
      rw [hswitch,
        searchNode_eq ctx tcLevel (fuel + 1) level lab ptn active
          numcells none,
        incMax, incMax]
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
  termination_by fuel _ _ _ _ _ inc =>
    (fuel, 0, match inc with | none => 0 | some _ => 1)

/-- The child sweep from a present accumulator: folding the pruned
child searches computes the running key maximum over the unpruned
child keys. -/
theorem searchFold_eq (ctx : Ctx) (tcLevel fuel level : Nat)
    (rsLab rsPtn : Array Nat) (tc numcells : Nat) :
    ∀ (os : List Nat) (t : Key),
      os.foldl (fun (acc : Option Key) o =>
        some (searchNode ctx tcLevel fuel (level + 1)
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
          (numcells + 1) acc))
        (some t) =
      some (keysMax t (os.map
        (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells)))
  | [], t => rfl
  | o :: rest, t => by
    rw [List.foldl_cons, List.map_cons, keysMax]
    rw [searchNode_eq ctx tcLevel fuel (level + 1) _ _ _ _
      (some t), incMax]
    exact searchFold_eq ctx tcLevel fuel level rsLab rsPtn tc
      numcells rest _
  termination_by os _ => (fuel, 1, os.length)

/-- One unfolding of the child sweep from an arbitrary accumulator:
the first child absorbs the incumbent, the rest fold from its
result. -/
theorem searchFold_cons (ctx : Ctx) (tcLevel fuel level : Nat)
    (rsLab rsPtn : Array Nat) (tc numcells o : Nat) (os : List Nat)
    (tail0 : Option Key) :
    (o :: os).foldl (fun (acc : Option Key) o =>
      some (searchNode ctx tcLevel fuel (level + 1)
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
        (numcells + 1) acc))
      tail0 =
    some (incMax tail0 (keysMax
      (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o)
      (os.map
        (childKey ctx tcLevel fuel level rsLab rsPtn tc
          numcells)))) := by
  rw [List.foldl_cons]
  rw [searchNode_eq ctx tcLevel fuel (level + 1) _ _ _ _ tail0]
  rcases tail0 with _ | b
  · rw [incMax, incMax]
    exact searchFold_eq ctx tcLevel fuel level rsLab rsPtn tc
      numcells os _
  · rw [incMax, incMax,
      searchFold_eq ctx tcLevel fuel level rsLab rsPtn tc numcells
        os _,
      keysMax_keyMax]
  termination_by (fuel, 2, 0)

end

/-! # The verified pruned evaluator at the root -/

/-- The pruned search from an empty incumbent: a verified pruned
evaluator of the spec key. -/
@[expose] def searchCanon (n : Nat) (g lab0 : Array Nat)
    (cellEnds : List Nat) : Key :=
  if n == 0 then
    ⟨[], []⟩
  else
    searchNode { n, g } 100 n 1 lab0 (initPtn n (n + 2) cellEnds)
      (initActive cellEnds) cellEnds.length none

theorem searchCanon_eq (n : Nat) (g lab0 : Array Nat)
    (cellEnds : List Nat) :
    searchCanon n g lab0 cellEnds = canonSpec n g lab0 cellEnds := by
  rw [searchCanon, canonSpec]
  split
  · rfl
  · exact searchNode_eq _ 100 n 1 lab0 _ _ _ none

/-- The pruned search computes the nauty-semantic canonical key. -/
theorem searchCanon_key (G : Colored n k) :
    searchCanon n (rowsOf G) (initialPartition G).1
      (initialPartition G).2 = canonSpecKey G := by
  rw [searchCanon_eq, canonSpecKey]

end Hex.GraphIso.Nauty
