/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Achieved

public section

/-!
Completeness of the certificate pipeline on honest inputs: replaying
the certificate built for the true spec key always succeeds. The
totality theorem `certifyCanon?_isSome` (SearchOutcomeCertify) builds
on this to make the certificate-backed canonicalization total.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Key n-order decompositions -/

theorem keyLe_cons_head {c bc : Nat} {cs brest : List Nat} {r br : List (VSet n)}
    (h : keyLe ⟨c :: cs, r⟩ ⟨bc :: brest, br⟩) : c ≤ bc := by
  rcases Nat.lt_or_ge bc c with hlt | hle
  · exact absurd (keyCmp_cons_gt hlt cs brest r br) h
  · omega

theorem keyLe_cons_tail {c : Nat} {cs brest : List Nat} {r br : List (VSet n)}
    (h : keyLe ⟨c :: cs, r⟩ ⟨c :: brest, br⟩) :
    keyLe ⟨cs, r⟩ ⟨brest, br⟩ := by
  rw [keyLe, ← keyCmp_cons_eq c]
  exact h

theorem key_cons_eq_iff {c : Nat} {cs brest : List Nat} {r br : List (VSet n)} :
    (⟨c :: cs, r⟩ : Key n) = ⟨c :: brest, br⟩ ↔
      (⟨cs, r⟩ : Key n) = ⟨brest, br⟩ := by
  constructor
  · intro h
    have h1 : c :: cs = c :: brest := congrArg Key.codes h
    have h2 : r = br := congrArg Key.rows h
    injection h1 with _ h3
    rw [h3, h2]
  · intro h
    have h1 : cs = brest := congrArg Key.codes h
    have h2 : r = br := congrArg Key.rows h
    rw [h1, h2]

theorem key_ne_of_head_lt {c bc : Nat} {cs brest : List Nat} {r br : List (VSet n)}
    (h : c < bc) : (⟨c :: cs, r⟩ : Key n) ≠ ⟨bc :: brest, br⟩ := by
  intro he
  have h1 : c :: cs = bc :: brest := congrArg Key.codes he
  injection h1 with h2
  omega

/-! # The checker accepts the honest certificate -/

theorem certifyNode_not_autom {ctx : Ctx n} (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active : VSet n) (numcells : Nat) (bcodes : List Nat) (o' : Nat)
      (γ : Array Nat),
      certifyNode ctx tcLevel fuel level lab ptn active numcells
        bcodes ≠ CertNode.autom o' γ := by
  intro fuel level lab ptn active numcells bcodes o' γ h
  rw [certifyNode.eq_def] at h
  rcases fuel with _ | fuel
  · exact CertNode.noConfusion h
  · rcases bcodes with _ | ⟨bc, brest⟩
    · exact CertNode.noConfusion h
    · dsimp only at h
      rcases hcmp : compare (refine ctx level lab ptn active
          numcells).longcode bc with _ | _ | _ <;> rw [hcmp] at h
      · exact CertNode.noConfusion h
      · rcases hdisc : discreteAt (refine ctx level lab ptn active
            numcells).ptn level n with _ | _ <;>
          rw [hdisc] at h
        · simp only [Bool.false_eq_true, ite_false] at h
          exact CertNode.noConfusion h
        · simp only [ite_true] at h
          exact CertNode.noConfusion h
      · exact CertNode.noConfusion h

mutual

theorem certifyNode_complete {ctx : Ctx n}
    (hgsz : ctx.g.size = n) (tcLevel : Nat) (brows : List (VSet n))
    (vgens : List (Array Nat)) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active : VSet n) (numcells : Nat) (bc : Nat) (brest : List Nat),
      NodeOk n level lab ptn active →
      n + 1 ≤ level + fuel →
      level ≤ bcount ptn level n →
      keyLe (specNode ctx tcLevel fuel level lab ptn active
        numcells) ⟨bc :: brest, brows⟩ →
      ∃ a, checkNode ctx tcLevel brows vgens fuel level lab ptn active
        numcells
        (certifyNode ctx tcLevel fuel level lab ptn active numcells
          (bc :: brest)) (bc :: brest) = some a ∧
        (a = true ↔ specNode ctx tcLevel fuel level lab ptn active
          numcells = ⟨bc :: brest, brows⟩)
  | 0, level, lab, ptn, active, numcells, bc, brest, hok, hlfl,
      hbc, hle => by
    exfalso
    have := bcount_le ptn level n
    omega
  | fuel + 1, level, lab, ptn, active, numcells, bc, brest, hok,
      hlfl, hbc, hle => by
    have hlevn : level ≤ n := by
      have := bcount_le ptn level n
      omega
    have hstR := refine_stOk (ctx := ctx) (active := active) (level := level)
      (numcells := numcells) hok.labSize hok.labOk hok.ptnSize
      hok.ptnEnd
    have hRvals : ∀ q : Nat,
        (refine ctx level lab ptn active numcells).ptn[q]! ≤ level ∨ (refine ctx level lab ptn active numcells).ptn[q]! = n + 2 := by
      intro q
      rcases ptn_refine_vals ctx level lab ptn active numcells q
        with he | he
      · rw [he]
        exact hok.vals q
      · rw [he]
        exact Or.inl (Nat.le_refl level)
    have hRinv := refine_refInv (ctx := ctx) (level := level)
      (lab := lab) (ptn := ptn) (active := active)
      (numcells := numcells) (by rw [hok.ptnSize]; omega)
      (by rw [hok.labSize, hok.ptnSize]) hok.ptnEnd
    obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel fuel
      level lab ptn active numcells
    have hkeyform : specNode ctx tcLevel (fuel + 1) level lab ptn
        active numcells =
        ⟨(refine ctx level lab ptn active numcells).longcode :: rest,
          (specNode ctx tcLevel (fuel + 1) level lab ptn active
            numcells).rows⟩ := by
      rw [← hrest]
    have hheadle : (refine ctx level lab ptn active numcells).longcode ≤ bc := by
      have h1 := hle
      rw [hkeyform] at h1
      exact keyLe_cons_head h1
    rcases hcmp : compare (refine ctx level lab ptn active numcells).longcode bc with _ | _ | _
    · -- longcode < bc: pruned by code on both sides
      refine ⟨false, ?_, ?_⟩
      · simp only [certifyNode, checkNode, hcmp]
        simp
      · refine ⟨fun hx => Bool.noConfusion hx, fun he => ?_⟩
        exfalso
        rw [hkeyform] at he
        exact key_ne_of_head_lt (Nat.compare_eq_lt.mp hcmp) he
    · -- equal heads
      have hlc : (refine ctx level lab ptn active numcells).longcode = bc := Nat.compare_eq_eq.mp hcmp
      rcases hdisc : discreteAt (refine ctx level lab ptn active numcells).ptn level n with _ | _
      · -- non-discrete: recurse through the children
        obtain ⟨p, hptc, hp12, hpb, hicp, hce⟩ := targetcell_facts (ctx := ctx) (tcLevel := tcLevel) (refine ctx level lab ptn active numcells).lab hstR.ptnSize hstR.ptnEnd
          hdisc
        have hM1 : (specMaketargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level
            tcLevel).1 = p.1 := hptc
        have hM22 : (specMaketargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level
            tcLevel).2.2 = p.2 + 1 - p.1 := by
          show cellEnd (refine ctx level lab ptn active numcells).ptn level
            (specTargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level tcLevel + 1) -
            specTargetcell ctx (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn level tcLevel + 1 =
            p.2 + 1 - p.1
          rw [hptc, hce]
          omega
        obtain ⟨m, hm⟩ : ∃ m, p.2 + 1 - p.1 = m + 1 :=
          ⟨p.2 - p.1, by omega⟩
        have hspec : specNode ctx tcLevel (fuel + 1) level lab ptn
            active numcells =
            ⟨(refine ctx level lab ptn active numcells).longcode ::
              (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
                ((List.range m).map fun j =>
                  childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells (j + 1))).codes,
            (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
              ((List.range m).map fun j =>
                childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells (j + 1))).rows⟩ := by
          rw [specNode]
          simp only [hdisc, Bool.false_eq_true, ite_false]
          rw [hM1, hM22, hm, List.range_succ_eq_map, List.map_cons,
            List.map_map]
          rfl
        have htail : keyLe (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
            ((List.range m).map fun j => childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells (j + 1)))
            ⟨brest, brows⟩ := by
          rw [← key_eta (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0)
            ((List.range m).map fun j => childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells (j + 1)))]
          refine keyLe_cons_tail (c := bc) ?_
          rw [← hlc]
          have h1 := hle
          rw [hspec] at h1
          rw [hlc] at h1
          rw [← hlc] at h1
          exact h1
        have hchildle : ∀ i, i < m + 1 →
            keyLe (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells i) ⟨brest, brows⟩ := by
          intro i hi
          refine keyLe_trans ?_ htail
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · exact keyLe_keysMax (Or.inl rfl)
          · refine keyLe_keysMax (Or.inr (List.mem_map.mpr
              ⟨i - 1, List.mem_range.mpr (by omega), ?_⟩))
            rw [show i - 1 + 1 = i from by omega]
        have hbcChild : level + 1 ≤
            bcount ((refine ctx level lab ptn active numcells).ptn.set! p.1 (level + 1)) (level + 1)
              n := by
          have h1 : bcount ptn level n ≤ bcount (refine ctx level lab ptn active numcells).ptn level n :=
            bcount_mono hRinv.grow
          have h2 := bcount_breakout (n := n) (ptn := (refine ctx level lab ptn active numcells).ptn)
            (level := level) (tc := p.1) (nn := n) hRvals (by omega)
            (hicp.2.2.1 p.1 (Nat.le_refl p.1) (by omega)) (by omega)
            (by rw [hstR.ptnSize]; omega)
          omega
        obtain ⟨a', ha', hiff⟩ := certifyChildren_complete hgsz
          tcLevel brows vgens fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1
          (p.2 + 1 - p.1) (refine ctx level lab ptn active numcells).numcells brest (m + 1) 0
          hstR.labSize hstR.labOk hstR.ptnSize hstR.ptnEnd hRvals
          hicp (by omega) (by omega) (by omega) hbcChild
          (fun i _ hi2 => hchildle i (by omega))
        refine ⟨a', ?_, ?_⟩
        · simp only [certifyNode, checkNode, hcmp, hdisc,
            Bool.false_eq_true, ite_false]
          rw [hM1, hM22, hm]
          rw [ite_eq_left (by rw [List.length_map, List.length_range])]
          rw [checkNode_children_eq]
          simp only [Nat.zero_add] at ha'
          rw [ha']
          simp
        · rw [hiff, hspec, ← hlc, key_cons_eq_iff, key_eta]
          constructor
          · rintro ⟨i, hi0, him, hik⟩
            refine keysMax_eq_of_le (hchildle 0 (by omega))
              (fun y hy => ?_) ?_
            · rcases List.mem_map.mp hy with ⟨j, hj, rfl⟩
              exact hchildle (j + 1) (by
                have := List.mem_range.mp hj
                omega)
            · rcases Nat.eq_zero_or_pos i with rfl | hpos
              · exact Or.inl hik.symm
              · refine Or.inr (List.mem_map.mpr
                  ⟨i - 1, List.mem_range.mpr (by omega), ?_⟩)
                rw [show i - 1 + 1 = i from by omega]
                exact hik
          · intro hkm
            rcases keysMax_mem ((List.range m).map fun j =>
              childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells (j + 1)) (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 (refine ctx level lab ptn active numcells).numcells 0) with he | he
            · exact ⟨0, by omega, by omega, by rw [← he]; exact hkm⟩
            · rcases List.mem_map.mp he with ⟨j, hj, hje⟩
              exact ⟨j + 1, by omega, by
                have := List.mem_range.mp hj
                omega, by rw [hje]; exact hkm⟩
      · -- discrete leaf: direct comparison
        have hkey : specNode ctx tcLevel (fuel + 1) level lab ptn
            active numcells =
            ⟨[(refine ctx level lab ptn active numcells).longcode, codeSentinel],
              leafRows ctx (refine ctx level lab ptn active numcells).lab⟩ := by
          rw [specNode, ite_eq_left hdisc]
        rcases hkc : keyCmp ⟨[(refine ctx level lab ptn active numcells).longcode, codeSentinel],
            leafRows ctx (refine ctx level lab ptn active numcells).lab⟩ ⟨bc :: brest, brows⟩
            with _ | _ | _
        · refine ⟨false, ?_, ?_⟩
          · simp only [certifyNode, checkNode, hcmp, hdisc, ite_true,
              hkc]
          · refine ⟨fun hx => Bool.noConfusion hx, fun he => ?_⟩
            exfalso
            rw [hkey] at he
            rw [he, keyCmp_self] at hkc
            exact Ordering.noConfusion hkc
        · refine ⟨true, ?_, ?_⟩
          · simp only [certifyNode, checkNode, hcmp, hdisc, ite_true,
              hkc]
          · refine ⟨fun _ => ?_, fun _ => rfl⟩
            rw [hkey]
            exact keyCmp_eq_iff.mp hkc
        · exfalso
          have h1 := hle
          rw [hkey, keyLe] at h1
          exact h1 hkc
    · -- longcode > bc contradicts the bound
      exfalso
      have := Nat.compare_eq_gt.mp hcmp
      omega
  termination_by fuel _ _ _ _ _ _ _ _ _ _ _ => (fuel, 0)

theorem certifyChildren_complete {ctx : Ctx n}
    (hgsz : ctx.g.size = n) (tcLevel : Nat) (brows : List (VSet n))
    (vgens : List (Array Nat))
    (fuel level : Nat) (rsLab rsPtn : Array Nat)
    (tc lenT numcells : Nat) (brest : List Nat) :
    ∀ (cnt o : Nat),
      rsLab.size = n → LabOk rsLab n → rsPtn.size = n →
      rsPtn[rsPtn.size - 1]! ≤ level →
      (∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2) →
      IsCell rsPtn level tc lenT → tc + lenT ≤ n →
      o + cnt ≤ lenT →
      n + 1 ≤ level + 1 + fuel →
      level + 1 ≤ bcount (rsPtn.set! tc (level + 1))
        (level + 1) n →
      (∀ i, o ≤ i → i < o + cnt →
        keyLe (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells i) ⟨brest, brows⟩) →
      ∃ a, checkChildren ctx tcLevel brows vgens fuel level rsLab rsPtn tc
        numcells brest
        ((List.range cnt).map fun j =>
          certifyNode ctx tcLevel fuel (level + 1)
            (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.2 (numcells + 1) brest) o =
          some a ∧
        (a = true ↔ ∃ i, o ≤ i ∧ i < o + cnt ∧
          childKey ctx tcLevel fuel level rsLab rsPtn tc numcells i = ⟨brest, brows⟩)
  | 0, o, hs, hok, hsp, hend, hvals, hic, hrange, hlen, hlf, hbcC,
      hbnd => by
    refine ⟨false, ?_, ?_⟩
    · rw [List.range_zero, List.map_nil, checkChildren]
    · refine ⟨fun hx => Bool.noConfusion hx, fun he => ?_⟩
      obtain ⟨i, h1, h2, _⟩ := he
      omega
  | cnt + 1, o, hs, hok, hsp, hend, hvals, hic, hrange, hlen, hlf,
      hbcC, hbnd => by
    have hoLen : o < lenT := by omega
    have hchildOk := childNodeOk (n := n) (level := level)
      (tc := tc) (lenT := lenT) (o := o) hs hok hsp hend hvals hic
      hrange hoLen
    rcases brest with _ | ⟨bc', brest'⟩
    · -- an empty best suffix cannot bound a live child key
      exfalso
      have hb0 := hbnd o (Nat.le_refl o) (by omega)
      have hble := bcount_le (rsPtn.set! tc (level + 1))
        (level + 1) n
      obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 :=
        ⟨fuel - 1, by omega⟩
      obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel f'
        (level + 1) (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1)
      have hb0' : keyLe (specNode ctx tcLevel (f' + 1) (level + 1)
          (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1))
          ⟨[], brows⟩ := hb0
      have hkeyform : specNode ctx tcLevel (f' + 1) (level + 1)
          (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1) =
          ⟨(refine ctx (level + 1) (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
            (numcells + 1)).longcode :: rest,
          (specNode ctx tcLevel (f' + 1) (level + 1)
            (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1)).rows⟩ := by
        rw [← hrest]
      rw [hkeyform, keyLe] at hb0'
      apply hb0'
      rw [keyCmp]
      rfl
    · obtain ⟨a, ha, haiff⟩ := certifyNode_complete hgsz tcLevel
        brows vgens fuel (level + 1)
        (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1) bc' brest'
        hchildOk (by omega) hbcC
        (hbnd o (Nat.le_refl o) (by omega))
      obtain ⟨a', ha', haiff'⟩ := certifyChildren_complete hgsz
        tcLevel brows vgens fuel level rsLab rsPtn tc lenT numcells
        (bc' :: brest') cnt (o + 1) hs hok hsp hend hvals hic hrange
        (by omega) hlf hbcC
        (fun i hi1 hi2 => hbnd i (by omega) (by omega))
      have hlist : ((List.range cnt).map fun j =>
          certifyNode ctx tcLevel fuel (level + 1)
            (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.2 (numcells + 1)
            (bc' :: brest')) =
          (List.range cnt).map
            ((fun j => certifyNode ctx tcLevel fuel (level + 1)
              (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.2 (numcells + 1)
              (bc' :: brest')) ∘ Nat.succ) := by
        refine List.map_congr_left fun j _ => ?_
        show certifyNode ctx tcLevel fuel (level + 1)
          (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.2 (numcells + 1)
          (bc' :: brest') =
          certifyNode ctx tcLevel fuel (level + 1)
          (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + Nat.succ j)]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + Nat.succ j)]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + Nat.succ j)]!).2.2 (numcells + 1)
          (bc' :: brest')
        rw [show o + 1 + j = o + Nat.succ j from by omega]
      refine ⟨a || a', ?_, ?_⟩
      · rw [List.range_succ_eq_map, List.map_cons, List.map_map,
          checkChildren]
        rcases hcert : certifyNode ctx tcLevel fuel (level + 1)
            (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 0)]!).1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 0)]!).2.1 (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + (o + 0)]!).2.2 (numcells + 1)
            (bc' :: brest') with _ | _ | ⟨o', γ⟩ | ch
        · have ha2 := ha
          rw [show (o : Nat) = o + 0 from by omega, hcert] at ha2
          rw [show (o : Nat) + 0 = o from by omega] at ha2
          rw [ha2]
          rw [hlist] at ha'
          rw [ha']
        · have ha2 := ha
          rw [show (o : Nat) = o + 0 from by omega, hcert] at ha2
          rw [show (o : Nat) + 0 = o from by omega] at ha2
          rw [ha2]
          rw [hlist] at ha'
          rw [ha']
        · exact absurd hcert (certifyNode_not_autom tcLevel _ _ _ _
            _ _ _ _ _)
        · have ha2 := ha
          rw [show (o : Nat) = o + 0 from by omega, hcert] at ha2
          rw [show (o : Nat) + 0 = o from by omega] at ha2
          rw [ha2]
          rw [hlist] at ha'
          rw [ha']
        · exact fun o'' γ' hx => certifyNode_not_autom tcLevel
            _ _ _ _ _ _ _ o'' γ' hx
      · constructor
        · intro hx
          rcases Bool.or_eq_true_iff.mp hx with hx1 | hx1
          · exact ⟨o, Nat.le_refl o, by omega, haiff.mp hx1⟩
          · obtain ⟨i, h1, h2, h3⟩ := haiff'.mp hx1
            exact ⟨i, by omega, by omega, h3⟩
        · rintro ⟨i, h1, h2, h3⟩
          rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
          · exact Bool.or_eq_true_iff.mpr (Or.inl (haiff.mpr h3))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (haiff'.mpr
              ⟨i, by omega, by omega, h3⟩))
  termination_by cnt _ _ _ _ _ _ _ _ _ _ _ _ => (fuel, cnt + 1)
end

/-! # Root-level completeness of the key check -/

theorem specNode_codes_head' {ctx : Ctx n} (tcLevel : Nat)
    {fuel : Nat} (hfuel : 1 ≤ fuel) (level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) :
    ∃ rest, (specNode ctx tcLevel fuel level lab ptn active
      numcells).codes =
      (refine ctx level lab ptn active numcells).longcode ::
        rest := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  exact specNode_codes_head ctx tcLevel f' level lab ptn active
    numcells

/-- The honest certificate for the true key always passes
`checkKey`. -/
theorem checkKey_complete (G : Colored n k) :
    checkKey G
      (certifyNode { g := rowsOf G } 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive n (initialPartition G).2)
        (initialPartition G).2.length (canonSpecKey G).codes)
      (canonSpecKey G) = true := by
  rw [checkKey]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [ite_eq_left (by rfl)]
    rw [show canonSpecKey G = ⟨[], []⟩ from by
      rw [canonSpecKey, canonSpec, ite_eq_left (by rfl)]]
    rfl
  · rw [ite_eq_right (by simp; omega)]
    have hok := initial_nodeOk G hn0
    have hbc : 1 ≤ bcount (initPtn n (n + 2)
        (initialPartition G).2) 1 n := by
      refine bcount_pos_of_boundary (q := n - 1) (by omega) ?_
      have h1 := hok.ptnEnd
      rw [size_initPtn] at h1
      exact h1
    have hkeydef : canonSpecKey G =
        specNode { g := rowsOf G } 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive n (initialPartition G).2)
        (initialPartition G).2.length := by
      rw [canonSpecKey, canonSpec, ite_eq_right (by simp; omega)]
    obtain ⟨rest, hrest⟩ : ∃ rest, (canonSpecKey G).codes =
        (refine { g := rowsOf G } 1 (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive n (initialPartition G).2)
        (initialPartition G).2.length).longcode :: rest := by
      rw [hkeydef]
      exact specNode_codes_head' _ (by omega) _ _ _ _ _
    have hkeyrec : (⟨(refine { g := rowsOf G } 1 (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive n (initialPartition G).2)
        (initialPartition G).2.length).longcode :: rest,
        (canonSpecKey G).rows⟩ : Key n) = canonSpecKey G := by
      rw [← hrest, key_eta]
    obtain ⟨a, ha, haiff⟩ := certifyNode_complete (n := n)
      (ctx := { g := rowsOf G }) (size_rowsOf G) 100
      (canonSpecKey G).rows
      (validGammas (rowsOf G)
        (certifyNode { g := rowsOf G } 100 n 1
          (initialPartition G).1
          (initPtn n (n + 2) (initialPartition G).2)
          (initActive n (initialPartition G).2)
          (initialPartition G).2.length
          ((refine { g := rowsOf G } 1 (initialPartition G).1
            (initPtn n (n + 2) (initialPartition G).2)
            (initActive n (initialPartition G).2)
            (initialPartition G).2.length).longcode :: rest)))
      n 1 (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive n (initialPartition G).2)
      (initialPartition G).2.length
      (refine { g := rowsOf G } 1 (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive n (initialPartition G).2)
        (initialPartition G).2.length).longcode rest hok
      (by show n + 1 ≤ 1 + n; omega) hbc
      (by
        rw [hkeyrec]
        exact keyLe_of_eq hkeydef.symm)
    have hat : a = true := haiff.mpr (by
      rw [hkeyrec]
      exact hkeydef.symm)
    rw [hat] at ha
    refine decide_eq_true ?_
    rw [hrest]
    exact ha

end Hex.GraphIso.Nauty
