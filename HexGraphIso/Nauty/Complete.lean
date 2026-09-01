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
the certificate built for the true spec key always succeeds. Together
with the soundness theorems this makes the certificate-backed
canonicalization total.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Key-order decompositions -/

theorem keyLe_cons_head {c bc : Nat} {cs brest r br : List Nat}
    (h : keyLe ⟨c :: cs, r⟩ ⟨bc :: brest, br⟩) : c ≤ bc := by
  rcases Nat.lt_or_ge bc c with hlt | hle
  · exact absurd (keyCmp_cons_gt hlt cs brest r br) h
  · omega

theorem keyLe_cons_tail {c : Nat} {cs brest r br : List Nat}
    (h : keyLe ⟨c :: cs, r⟩ ⟨c :: brest, br⟩) :
    keyLe ⟨cs, r⟩ ⟨brest, br⟩ := by
  rw [keyLe, ← keyCmp_cons_eq c]
  exact h

theorem key_cons_eq_iff {c : Nat} {cs brest r br : List Nat} :
    (⟨c :: cs, r⟩ : Key) = ⟨c :: brest, br⟩ ↔
      (⟨cs, r⟩ : Key) = ⟨brest, br⟩ := by
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

theorem key_ne_of_head_lt {c bc : Nat} {cs brest r br : List Nat}
    (h : c < bc) : (⟨c :: cs, r⟩ : Key) ≠ ⟨bc :: brest, br⟩ := by
  intro he
  have h1 : c :: cs = bc :: brest := congrArg Key.codes he
  injection h1 with h2
  omega

/-! # The checker accepts the honest certificate -/

theorem certifyNode_not_autom {ctx : Ctx} (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (bcodes : List Nat) (o' : Nat)
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
            numcells).ptn level ctx.n with _ | _ <;>
          rw [hdisc] at h
        · simp only [Bool.false_eq_true, if_false] at h
          exact CertNode.noConfusion h
        · simp only [if_true] at h
          exact CertNode.noConfusion h
      · exact CertNode.noConfusion h

mutual

theorem certifyNode_complete {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) (tcLevel : Nat) (brows : List Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (bc : Nat) (brest : List Nat),
      NodeOk n level lab ptn active →
      n + 1 ≤ level + fuel →
      level ≤ bcount ptn level n →
      keyLe (specNode ctx tcLevel fuel level lab ptn active
        numcells) ⟨bc :: brest, brows⟩ →
      ∃ a, checkNode ctx tcLevel brows fuel level lab ptn active
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
    have hstR := refine_stOk (ctx := ctx) hn (level := level)
      (numcells := numcells) hok.labSize hok.labOk hok.ptnSize
      hok.act hok.ptnEnd
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
      rcases hdisc : discreteAt (refine ctx level lab ptn active numcells).ptn level ctx.n with _ | _
      · -- non-discrete: recurse through the children
        obtain ⟨p, hptc, hp12, hpb, hicp, hce⟩ := targetcell_facts
          hn (tcLevel := tcLevel) (refine ctx level lab ptn active numcells).lab hstR.ptnSize hstR.ptnEnd
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
              (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells 0)
                ((List.range m).map fun j =>
                  childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells (j + 1))).codes,
            (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells 0)
              ((List.range m).map fun j =>
                childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells (j + 1))).rows⟩ := by
          rw [specNode]
          simp only [hdisc, Bool.false_eq_true, if_false]
          rw [hM1, hM22, hm, List.range_succ_eq_map, List.map_cons,
            List.map_map]
          rfl
        have htail : keyLe (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells 0)
            ((List.range m).map fun j => childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells (j + 1)))
            ⟨brest, brows⟩ := by
          rw [← key_eta (keysMax (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells 0)
            ((List.range m).map fun j => childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells (j + 1)))]
          refine keyLe_cons_tail (c := bc) ?_
          rw [← hlc]
          have h1 := hle
          rw [hspec] at h1
          rw [hlc] at h1
          rw [← hlc] at h1
          exact h1
        have hchildle : ∀ i, i < m + 1 →
            keyLe (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells i) ⟨brest, brows⟩ := by
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
        obtain ⟨a', ha', hiff⟩ := certifyChildren_complete hn hgsz
          tcLevel brows fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1
          (p.2 + 1 - p.1) numcells brest (m + 1) 0
          hstR.labSize hstR.labOk hstR.ptnSize hstR.ptnEnd hRvals
          hicp (by omega) (by omega) (by omega) hbcChild
          (fun i _ hi2 => hchildle i (by omega))
        refine ⟨a', ?_, ?_⟩
        · simp only [certifyNode, checkNode, hcmp, hdisc,
            Bool.false_eq_true, if_false]
          rw [hM1, hM22, hm]
          rw [if_pos (by rw [List.length_map, List.length_range])]
          simp only [Nat.zero_add] at ha'
          exact ha'
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
              childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells (j + 1)) (childKey ctx tcLevel fuel level (refine ctx level lab ptn active numcells).lab (refine ctx level lab ptn active numcells).ptn p.1 numcells 0) with he | he
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
          rw [specNode, if_pos hdisc]
        rcases hkc : keyCmp ⟨[(refine ctx level lab ptn active numcells).longcode, codeSentinel],
            leafRows ctx (refine ctx level lab ptn active numcells).lab⟩ ⟨bc :: brest, brows⟩
            with _ | _ | _
        · refine ⟨false, ?_, ?_⟩
          · simp only [certifyNode, checkNode, hcmp, hdisc, if_true,
              hkc]
          · refine ⟨fun hx => Bool.noConfusion hx, fun he => ?_⟩
            exfalso
            rw [hkey] at he
            rw [he, keyCmp_self] at hkc
            exact Ordering.noConfusion hkc
        · refine ⟨true, ?_, ?_⟩
          · simp only [certifyNode, checkNode, hcmp, hdisc, if_true,
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

theorem certifyChildren_complete {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) (tcLevel : Nat) (brows : List Nat)
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
      ∃ a, checkChildren ctx tcLevel brows fuel level rsLab rsPtn tc
        numcells brest
        ((List.range cnt).map fun j =>
          certifyNode ctx tcLevel fuel (level + 1)
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.2 (numcells + 1) brest) o =
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
        (level + 1) (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1)
      have hb0' : keyLe (specNode ctx tcLevel (f' + 1) (level + 1)
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1))
          ⟨[], brows⟩ := hb0
      have hkeyform : specNode ctx tcLevel (f' + 1) (level + 1)
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1) =
          ⟨(refine ctx (level + 1) (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
            (numcells + 1)).longcode :: rest,
          (specNode ctx tcLevel (f' + 1) (level + 1)
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1)).rows⟩ := by
        rw [← hrest]
      rw [hkeyform, keyLe] at hb0'
      apply hb0'
      rw [keyCmp]
      rfl
    · obtain ⟨a, ha, haiff⟩ := certifyNode_complete hn hgsz tcLevel
        brows fuel (level + 1)
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2 (numcells + 1) bc' brest'
        hchildOk (by omega) hbcC
        (hbnd o (Nat.le_refl o) (by omega))
      obtain ⟨a', ha', haiff'⟩ := certifyChildren_complete hn hgsz
        tcLevel brows fuel level rsLab rsPtn tc lenT numcells
        (bc' :: brest') cnt (o + 1) hs hok hsp hend hvals hic hrange
        (by omega) hlf hbcC
        (fun i hi1 hi2 => hbnd i (by omega) (by omega))
      have hlist : ((List.range cnt).map fun j =>
          certifyNode ctx tcLevel fuel (level + 1)
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.2 (numcells + 1)
            (bc' :: brest')) =
          (List.range cnt).map
            ((fun j => certifyNode ctx tcLevel fuel (level + 1)
              (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + j)]!).2.2 (numcells + 1)
              (bc' :: brest')) ∘ Nat.succ) := by
        refine List.map_congr_left fun j _ => ?_
        show certifyNode ctx tcLevel fuel (level + 1)
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 1 + j)]!).2.2 (numcells + 1)
          (bc' :: brest') =
          certifyNode ctx tcLevel fuel (level + 1)
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + Nat.succ j)]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + Nat.succ j)]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + Nat.succ j)]!).2.2 (numcells + 1)
          (bc' :: brest')
        rw [show o + 1 + j = o + Nat.succ j from by omega]
      refine ⟨a || a', ?_, ?_⟩
      · rw [List.range_succ_eq_map, List.map_cons, List.map_map,
          checkChildren]
        rcases hcert : certifyNode ctx tcLevel fuel (level + 1)
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 0)]!).1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 0)]!).2.1 (breakout rsLab rsPtn (level + 1) tc rsLab[tc + (o + 0)]!).2.2 (numcells + 1)
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

theorem specNode_codes_head' {ctx : Ctx} (tcLevel : Nat)
    {fuel : Nat} (hfuel : 1 ≤ fuel) (level : Nat)
    (lab ptn : Array Nat) (active numcells : Nat) :
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
      (certifyNode { n := n, g := rowsOf G } 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length (canonSpecKey G).codes)
      (canonSpecKey G) = true := by
  rw [checkKey]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [if_pos (by rfl)]
    rw [show canonSpecKey G = ⟨[], []⟩ from by
      rw [canonSpecKey, canonSpec, if_pos (by rfl)]]
    rfl
  · rw [if_neg (by simp; omega)]
    have hok := initial_nodeOk G hn0
    have hbc : 1 ≤ bcount (initPtn n (n + 2)
        (initialPartition G).2) 1 n := by
      refine bcount_pos_of_boundary (q := n - 1) (by omega) ?_
      have h1 := hok.ptnEnd
      rw [size_initPtn] at h1
      exact h1
    have hkeydef : canonSpecKey G =
        specNode { n := n, g := rowsOf G } 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length := by
      rw [canonSpecKey, canonSpec, if_neg (by simp; omega)]
    obtain ⟨rest, hrest⟩ : ∃ rest, (canonSpecKey G).codes =
        (refine { n := n, g := rowsOf G } 1 (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length).longcode :: rest := by
      rw [hkeydef]
      exact specNode_codes_head' _ (by omega) _ _ _ _ _
    have hkeyrec : (⟨(refine { n := n, g := rowsOf G } 1 (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length).longcode :: rest,
        (canonSpecKey G).rows⟩ : Key) = canonSpecKey G := by
      rw [← hrest, key_eta]
    obtain ⟨a, ha, haiff⟩ := certifyNode_complete (n := n)
      (ctx := { n := n, g := rowsOf G }) rfl (size_rowsOf G) 100
      (canonSpecKey G).rows n 1 (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length
      (refine { n := n, g := rowsOf G } 1 (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
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


/-! # The exhaustive fallback always succeeds -/

/-- All orderings of a list of vertices. -/
@[expose] def permsOf (l : List Nat) : List (List Nat) :=
  if h : l = [] then
    [[]]
  else
    l.attach.flatMap fun x =>
      (permsOf (l.erase x.val)).map (x.val :: ·)
  termination_by l.length
  decreasing_by
    have := List.length_erase_of_mem x.property
    have hne : 0 < l.length := by
      rcases l with _ | _
      · exact absurd rfl h
      · simp
    omega

theorem mem_permsOf : ∀ {cand l : List Nat}, cand.Perm l →
    cand ∈ permsOf l
  | [], l, hperm => by
    have hl : l = [] := (List.perm_nil.mp hperm.symm)
    subst hl
    rw [permsOf]
    simp
  | x :: rest, l, hperm => by
    have hx : x ∈ l := hperm.mem_iff.mp (by simp)
    have hrest : rest.Perm (l.erase x) := by
      have := List.cons_perm_iff_perm_erase.mp hperm
      exact this.2
    have hne : l ≠ [] := by
      intro he
      subst he
      cases hx
    rw [permsOf, dif_neg hne]
    refine List.mem_flatMap.mpr ⟨⟨x, hx⟩, by simp, ?_⟩
    exact List.mem_map.mpr ⟨rest, mem_permsOf hrest, rfl⟩

/-- Try every labelling; the checker keeps only canonical ones.
Exponential, but provably total: the achieved leaf is among the
candidates. -/
@[expose] def bruteCanon? (G : Colored n k) :
    Option (CanonResult n k) :=
  (permsOf (List.range n)).findSome? fun cand =>
    checkCanon G
      (certifyNode { n := n, g := rowsOf G } 100 n 1
      (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length (canonSpecKey G).codes)
      (canonSpecKey G) cand.toArray

/-- `checkCanon` succeeds on the achieved leaf's labelling. -/
theorem checkCanon_of_achieved {G : Colored n k} {llab : Array Nat}
    (hn0 : 0 < n) (hsz : llab.size = n)
    (hperm : llab.toList.Perm (List.range n))
    (hrows : (canonSpecKey G).rows =
      leafRows { n := n, g := rowsOf G } llab)
    (hcols : ∀ (i : Nat), i < n → ∃ hv : llab[i]! < n,
      (G.coloring.cells[(⟨llab[i]!, hv⟩ : Fin n)]).val =
        (sortedColorSeq G)[i]!) :
    (checkCanon G
      (certifyNode { n := n, g := rowsOf G } 100 n 1
      (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length (canonSpecKey G).codes)
      (canonSpecKey G) llab).isSome := by
  have hbound : ∀ v ∈ llab, v < n := by
    intro v hv
    have hm : v ∈ llab.toList := by simpa using hv
    exact List.mem_range.mp (hperm.mem_iff.mp hm)
  rw [checkCanon]
  rw [dif_pos (⟨hsz, hbound⟩ : llab.size = n ∧ ∀ v ∈ llab, v < n)]
  have hmapval : ((llab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)).toList.map
      Fin.val) = llab.toList := by
    refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
    rw [List.getElem_map, Array.getElem_toList, Array.getElem_map,
      Array.getElem_attach]
    exact (Array.getElem_toList _).symm
  have hnodupv : ((llab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList.Nodup := by
    have hmv : (((llab.attach.map fun v =>
        (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
        Array (Fin n)).toList.map Fin.val).Nodup := by
      rw [hmapval]
      exact hperm.symm.nodup List.nodup_range
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hmv
    rw [List.nodup_iff_pairwise_ne]
    exact hmv.imp fun h he => h (congrArg Fin.val he)
  have hcompl : ∀ i : Fin n, i ∈ ((llab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList := by
    intro i
    have hm : i.val ∈ llab.toList :=
      hperm.mem_iff.mpr (List.mem_range.mpr i.isLt)
    rw [← hmapval] at hm
    rcases List.mem_map.mp hm with ⟨x, hx, hxe⟩
    exact (Fin.eq_of_val_eq hxe : x = i) ▸ hx
  obtain ⟨l, hl⟩ : ∃ l, Label.ofVector?
      (⟨llab.attach.map fun v =>
        (⟨v.val, hbound v.val v.property⟩ : Fin n), by
          simp [hsz]⟩ : Vector (Fin n) n) = some l := by
    rw [Label.ofVector?, Perm.ofVector?]
    rw [dif_pos ⟨hnodupv, hcompl⟩]
    exact ⟨_, rfl⟩
  rw [hl]
  have hcond : (checkKey G
      (certifyNode { n := n, g := rowsOf G } 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length (canonSpecKey G).codes)
      (canonSpecKey G) &&
      ((canonSpecKey G).rows ==
        leafRows { n := n, g := rowsOf G } llab) &&
      colorSortedCheck G llab) = true := by
    refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
      ⟨checkKey_complete G, beq_iff_eq.mpr hrows⟩, ?_⟩
    rw [colorSortedCheck, List.all_eq_true]
    intro i hi
    have hin := List.mem_range.mp hi
    refine (Bool.or_eq_true_iff).mpr ?_
    rcases Decidable.em (i + 1 = n) with he | he
    · exact Or.inl (by simpa using he)
    · right
      refine decide_eq_true ?_
      obtain ⟨hv1, hc1⟩ := hcols i hin
      obtain ⟨hv2, hc2⟩ := hcols (i + 1) (by omega)
      have hl1 : labColor G llab i =
          (sortedColorSeq G)[i]! := by
        rw [labColor, dif_pos ⟨by omega, hv1⟩]
        exact hc1
      have hl2 : labColor G llab (i + 1) =
          (sortedColorSeq G)[i + 1]! := by
        rw [labColor, dif_pos ⟨by omega, hv2⟩]
        exact hc2
      rw [hl1, hl2]
      -- sortedness of the colour sequence at adjacent positions
      have hp := pairwise_sortedColorSeq G
      rw [List.pairwise_iff_getElem] at hp
      have hlen := length_sortedColorSeq G
      have := hp i (i + 1) (by omega) (by omega) (by omega)
      rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)]
      exact this
  simp only [hcond, if_true]
  rfl

/-- The exhaustive fallback finds a canonical result whenever the
graph has vertices. -/
theorem bruteCanon?_isSome (G : Colored n k) (hn0 : 0 < n) :
    (bruteCanon? G).isSome := by
  rw [bruteCanon?, List.findSome?_isSome_iff]
  -- the achieved leaf supplies a passing candidate
  have hok := initial_nodeOk G hn0
  have hbc : 1 ≤ bcount (initPtn n (n + 2)
      (initialPartition G).2) 1 n := by
    refine bcount_pos_of_boundary (q := n - 1) (by omega) ?_
    have h1 := hok.ptnEnd
    rw [size_initPtn] at h1
    exact h1
  obtain ⟨llab, hlsz, hlcp, hlrows⟩ := specNode_achieved
    (ctx := { n := n, g := rowsOf G }) rfl 100 n 1
    (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2)
    (initActive (initialPartition G).2)
    (initialPartition G).2.length hok
    (by show n + 1 ≤ 1 + n; omega) hbc
  have hkrows : (canonSpecKey G).rows =
      leafRows { n := n, g := rowsOf G } llab := by
    rw [canonSpecKey, canonSpec, if_neg (by simp; omega)]
    exact hlrows
  have hperm := achieved_perm_range hlsz hn0 hlcp
  refine ⟨llab.toList, ?_, ?_⟩
  · exact mem_permsOf hperm
  · have hrt : llab.toList.toArray = llab := by simp
    rw [hrt]
    exact checkCanon_of_achieved (G := G) hn0 hlsz hperm hkrows
      (achieved_position_colors hlcp)

/-! # Total certificate-checked canonicalization -/

/-- Certificate-checked canonicalization: the branch-and-bound search
first, the provably total exhaustive fallback second. The final arm
is reachable only for `n = 0`, where it is correct. -/
@[expose] def canonicalizeSpec (G : Colored n k) : CanonResult n k :=
  match certifyCanon? G with
  | some res => res
  | none =>
    match bruteCanon? G with
    | some res => res
    | none => { form := G, label := Label.id n }

theorem canonicalizeSpec_form (G : Colored n k) :
    (canonicalizeSpec G).form = specCanon G := by
  rw [canonicalizeSpec]
  rcases hc : certifyCanon? G with _ | res
  · rcases hb : bruteCanon? G with _ | res2
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · show G = specCanon G
        exact Colored.ext (fun i j => i.elim0) (fun i => i.elim0)
      · exfalso
        have hs := bruteCanon?_isSome G hn0
        rw [hb] at hs
        simp at hs
    · show res2.form = specCanon G
      rw [bruteCanon?] at hb
      obtain ⟨cand, hmem, hchk⟩ := List.exists_of_findSome?_eq_some
        hb
      exact checkCanon_form hchk
  · show res.form = specCanon G
    rw [certifyCanon?] at hc
    split at hc
    · cases hc
    · split at hc
      · cases hc
      · exact checkCanon_form hc

theorem canonicalizeSpec_relabel (G : Colored n k) :
    G.relabel (canonicalizeSpec G).label =
      (canonicalizeSpec G).form := by
  rw [canonicalizeSpec]
  rcases hc : certifyCanon? G with _ | res
  · rcases hb : bruteCanon? G with _ | res2
    · show G.relabel (Label.id n) = G
      exact Colored.relabel_id G
    · show G.relabel res2.label = res2.form
      rw [bruteCanon?] at hb
      obtain ⟨cand, hmem, hchk⟩ := List.exists_of_findSome?_eq_some
        hb
      exact (checkCanon_sound hchk).2.1.symm
  · show G.relabel res.label = res.form
    rw [certifyCanon?] at hc
    split at hc
    · cases hc
    · split at hc
      · cases hc
      · exact (checkCanon_sound hc).2.1.symm

theorem canonicalizeSpec_iso (G : Colored n k) :
    Isomorphic G (canonicalizeSpec G).form := by
  rw [canonicalizeSpec_form]
  exact specCanon_iso G

theorem canonicalizeSpec_invariant {G H : Colored n k}
    (h : Isomorphic G H) :
    (canonicalizeSpec G).form = (canonicalizeSpec H).form := by
  rw [canonicalizeSpec_form, canonicalizeSpec_form]
  exact specCanon_invariant h

theorem iso_iff_canonicalizeSpec_eq {G H : Colored n k} :
    Isomorphic G H ↔
      (canonicalizeSpec G).form = (canonicalizeSpec H).form := by
  rw [canonicalizeSpec_form, canonicalizeSpec_form]
  exact iso_iff_specCanon_eq

end Hex.GraphIso.Nauty
