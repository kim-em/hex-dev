/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Codes
public import HexGraphIso.Nauty.Invariant.Leaves
public import HexGraphIso.Nauty.Spec.CanonSpec
public import HexGraphIso.Nauty.Invariant.Refine
public import HexGraphIso.Nauty.Invariant.Trace
public import HexGraphIso.Nauty.Invariant.Stabilize
public import HexGraphIso.Nauty.Invariant.Autos
public import HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.Invariant.Store
import all HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.Search.State

public section

/-! Refinement-code comparisons, leaf-row equality, and specification-key
bounds. A carried automorphism identifies sibling subtree keys. -/

namespace Hex.GraphIso.Nauty

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-- The incumbent's key: the ghost code list with the sentinel
stamped, and the stored best leaf's rows. -/
@[expose] def incKey (ctx : Ctx n) (bs : List Nat)
    (canonlab : Array Nat) : Key n :=
  ⟨bs ++ [codeSentinel], leafRows ctx canonlab⟩

/-- A leaf key of the current path. -/
@[expose] def pathLeafKey (ctx : Ctx n) (cs : List Nat)
    (lab : Array Nat) : Key n :=
  ⟨cs ++ [codeSentinel], leafRows ctx lab⟩

/-- Under full agreement the path is never deeper than the
incumbent. -/
theorem codeInv_tied_le {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 0) :
    cs.length ≤ bs.length := by
  rcases hinv.tri with ⟨-, -, hle, -⟩ | ⟨j, -, -, -, -, -, hcase⟩
  · exact hle
  · rcases hcase with ⟨hcc, -⟩ | ⟨hcc, -⟩
    · cases hcc
    · cases hcc

/-- A code-tied leaf strictly above the incumbent's depth compares
above it: the leaf's sentinel meets a real incumbent code. -/
theorem tied_short_keyCmp_gt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 0)
    (hshort : cs.length < bs.length) (r1 r2 : List (VSet n)) :
    keyCmp ⟨cs ++ [codeSentinel], r1⟩ ⟨bs ++ [codeSentinel], r2⟩ =
      .gt := by
  rcases hinv.tri with ⟨-, -, -, hmatch⟩ | ⟨j, -, -, -, -, -, hcase⟩
  · rw [keyCmp]
    have hlc : listCmp compare (cs ++ [codeSentinel])
        (bs ++ [codeSentinel]) = .gt := by
      refine listCmp_gt_of_prefix cs.length _ _
        (by rw [List.length_append]; simp)
        (by rw [List.length_append]; simp; omega)
        (fun i hi => ?_) ?_
      · rw [getElem!_append_left hi,
          getElem!_append_sentinel (by omega)]
        have h := hmatch (i + 1) (by omega) (by omega)
        simpa using h
      · rw [getElem!_append_sentinel (bs := cs) (Nat.le_refl _),
          getElem!_append_sentinel (bs := bs) (i := cs.length)
            (by omega),
          bcode_sentinel (bs := cs) (i := cs.length + 1) (by omega)]
        exact bcode_lt hinv.blt (by omega) (by omega)
    rw [hlc]
  · rcases hcase with ⟨hcc, -⟩ | ⟨hcc, -⟩
    · cases hcc
    · cases hcc

/-- A code-tied leaf at the incumbent's depth hands the comparison
to the rows. -/
theorem tied_full_keyCmp {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 0)
    (hlen : cs.length = bs.length) (r1 r2 : List (VSet n)) :
    keyCmp ⟨cs ++ [codeSentinel], r1⟩ ⟨bs ++ [codeSentinel], r2⟩ =
      listCmp VSet.rowCmp r1 r2 := by
  rw [codeInv_eq_of_tied hinv hlen, keyCmp_codes_eq]

/-- The downward-frozen verdict at a leaf, in incumbent-key form. -/
theorem frozen_lt_keyCmp {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {lab canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon
      (-1)) :
    keyCmp (pathLeafKey ctx cs lab) (incKey ctx bs canonlab) =
      .lt :=
  codeInv_keyCmp_lt hinv [codeSentinel] _ _

/-- The upward-frozen verdict at a leaf, in incumbent-key form. -/
theorem frozen_gt_keyCmp {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {lab canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 1) :
    keyCmp (pathLeafKey ctx cs lab) (incKey ctx bs canonlab) =
      .gt :=
  codeInv_keyCmp_gt hinv [codeSentinel] _ _

private theorem pushAuto_lab (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).lab = st.lab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_ptn (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).ptn = st.ptn := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_canonlab (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).canonlab = st.canonlab := by
  rw [pushAuto]; split <;> rfl

private theorem pushAuto_firstlab (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).firstlab = st.firstlab := by
  rw [pushAuto]; split <;> rfl

private theorem forIn_scatter_eq {flab lab : Array Nat} :
    ∀ (l : List Nat) (w : Array Nat),
      (forIn l w (fun i r =>
        pure (ForInStep.yield (r.set! flab[i]! lab[i]!))) :
          Id (Array Nat)) =
      l.foldl (fun r i => r.set! flab[i]! lab[i]!) w
  | [], _ => rfl
  | i :: l, w => by
    rw [List.forIn_cons, List.foldl_cons]
    exact forIn_scatter_eq l _

private theorem id_run_eq {α : Type} (x : Id α) : Id.run x = x := rfl

private theorem pushAuto_orbits (st : Search n) (p : VSet n × VSet n) :
    (pushAuto st p).orbits = st.orbits := by
  rw [pushAuto]; split <;> rfl

section Frames

end Frames

section Seed

private theorem ftF_eqlevFirst (level : Nat) (st : Search n) :
    (firstterminal level st).eqlevFirst = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem ftF_firstcode (level : Nat) (st : Search n) :
    (firstterminal level st).firstcode =
      st.firstcode.set! (level + 1) codeSentinel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

/-- `firstterminal` seeds the first-path machine: the just-installed
first leaf agrees with itself at full depth. -/
theorem firstterminal_firstCodeInv {nn : Nat} {cs : List Nat}
    {st : Search n}
    (hsize : st.firstcode.size = nn + 2)
    (hLnn : cs.length ≤ nn)
    (hfc : ∀ i, 1 ≤ i → i ≤ cs.length →
      st.firstcode[i]! = cs[i - 1]!)
    (hclt : ∀ c ∈ cs, c < codeSentinel) :
    FirstCodeInv nn cs cs
      (firstterminal cs.length st).firstcode
      (firstterminal cs.length st).eqlevFirst := by
  rw [ftF_firstcode, ftF_eqlevFirst]
  refine ⟨by rw [Array.size_set!]; exact hsize, hLnn, hclt,
    fun i h1 h2 => ?_, ?_, Nat.le_refl _, Nat.le_refl _,
    fun i h1 h2 => rfl⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact hfc i h1 h2
  · rw [Array.getElem!_set!_self _ _ _ (by rw [hsize]; omega)]

end Seed

/-- The absolute key of a spec subtree below the path codes `cs`. -/
@[expose] def prefixKey (cs : List Nat) (kk : Key n) : Key n :=
  ⟨cs ++ kk.codes, kk.rows⟩

theorem prefixKey_nil (kk : Key n) : prefixKey [] kk = kk := rfl

/-- Prefixing by common path codes commutes with the key maximum. -/
theorem prefixKey_keyMax :
    ∀ (cs : List Nat) (k1 k2 : Key n),
      prefixKey cs (keyMax k1 k2) =
        keyMax (prefixKey cs k1) (prefixKey cs k2)
  | [], k1, k2 => by
    rw [prefixKey_nil, prefixKey_nil, prefixKey_nil]
  | c :: cs, k1, k2 => by
    show (⟨c :: (cs ++ (keyMax k1 k2).codes),
        (keyMax k1 k2).rows⟩ : Key n) =
      keyMax ⟨c :: (cs ++ k1.codes), k1.rows⟩
        ⟨c :: (cs ++ k2.codes), k2.rows⟩
    rw [keyMax_cons]
    have ih := prefixKey_keyMax cs k1 k2
    rw [prefixKey, prefixKey, prefixKey] at ih
    rw [← ih]

/-- Prefixing a common code moves it into the path. -/
theorem prefixKey_cons (cs : List Nat) (code : Nat) (K : Key n) :
    prefixKey cs ⟨code :: K.codes, K.rows⟩ =
      prefixKey (cs ++ [code]) K := by
  rw [prefixKey, prefixKey, List.append_assoc]
  rfl

/-- Prefixing distributes over the seeded list maximum. -/
theorem prefixKey_keysMax :
    ∀ (l : List (Key n)) (b : Key n) (cs : List Nat),
      prefixKey cs (keysMax b l) =
        keysMax (prefixKey cs b) (l.map (prefixKey cs))
  | [], b, cs => by rw [keysMax, List.map_nil, keysMax]
  | kk :: t, b, cs => by
    rw [keysMax, List.map_cons, keysMax,
      prefixKey_keysMax t (keyMax b kk) cs, prefixKey_keyMax]

/-- One child key of a spec node: the subtree below individualizing
the `o`-th target-cell vertex of the refined state. -/
@[expose] def specChild (ctx : Ctx n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (o : Nat) : Key n :=
  let rs := refine ctx level lab ptn active numcells
  let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
  let br := breakout n rs.lab rs.ptn (level + 1) tcr.1
    rs.lab[tcr.1 + o]!
  specNode ctx tcLevel fuel (level + 1) br.1 br.2.1 br.2.2
    (rs.numcells + 1)

/-- The internal arm of `specNode`, isolated: at a non-discrete node
the subtree key under the path prefix is the maximum of the
children's keys under the path extended by the node's own code. -/
theorem specNode_internal {ctx : Ctx n} {tcLevel fuel level : Nat}
    {lab ptn : Array Nat} {active : VSet n} {numcells : Nat} {len : Nat}
    (cs : List Nat)
    (hdisc : discreteAt (refine ctx level lab ptn active
      numcells).ptn level n = false)
    (hlen : (specMaketargetcell ctx
        (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn level
          tcLevel).2.2 = len + 1) :
    prefixKey cs
        (specNode ctx tcLevel (fuel + 1) level lab ptn active
          numcells) =
      keysMax
        (prefixKey (cs ++ [(refine ctx level lab ptn active
            numcells).longcode])
          (specChild ctx tcLevel fuel level lab ptn active numcells
            0))
        ((List.range len).map fun o =>
          prefixKey (cs ++ [(refine ctx level lab ptn active
              numcells).longcode])
            (specChild ctx tcLevel fuel level lab ptn active numcells
              (o + 1))) := by
  rw [specNode]
  simp only [hdisc, Bool.false_eq_true, ite_false, hlen,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [prefixKey_cons, prefixKey_keysMax, List.map_map]
  rfl

/-- Discreteness is exactly a full boundary count. -/
theorem discreteAt_iff_bcount {ptn : Array Nat} {level nn : Nat}
    (hnn : nn = ptn.size) (hend : ptn[ptn.size - 1]! ≤ level) :
    discreteAt ptn level nn = true ↔ bcount ptn level nn = nn := by
  have hnn' : nn ≤ ptn.size := Nat.le_of_eq hnn
  constructor
  · intro hdisc
    have h : List.countP (fun q => decide (ptn[q]! ≤ level))
        (List.range nn) = (List.range nn).length := by
      refine List.countP_eq_length.mpr fun q hq => ?_
      have hqn : q < nn := List.mem_range.mp hq
      obtain ⟨p, hpm, hp1, hp2⟩ := cells_cover (ptn := ptn)
        (level := level) q hqn
      have hsingle : p.1 = p.2 := by
        have h := cells_eq_of_discreteAt hdisc p hpm
        simpa using h
      have hic := cells_isCell hnn' hend p hpm
      have hq1 : p.1 = q := by omega
      have hq2 : p.2 = q := by omega
      rw [hq1, hq2] at hic
      have hcl := hic.2.2.2
      rw [show q + (q + 1 - q) - 1 = q from by omega] at hcl
      simpa using hcl
    rw [List.length_range] at h
    rw [bcount]
    exact h
  · intro hb
    have hb' : List.countP (fun q => decide (ptn[q]! ≤ level))
        (List.range nn) = (List.range nn).length := by
      rw [List.length_range]
      rw [bcount] at hb
      exact hb
    have hall : ∀ q, q < nn → ptn[q]! ≤ level := by
      intro q hq
      have h := List.countP_eq_length.mp hb' q
        (List.mem_range.mpr hq)
      simpa using h
    rw [discreteAt, List.all_eq_true]
    intro p hpm
    have hic := cells_isCell hnn' hend p hpm
    have hle := cells_le p hpm
    have hbnd := cells_bound hnn' hend p hpm
    rcases Decidable.em (p.1 = p.2) with heq | hne
    · simpa using heq
    · exfalso
      have hlt : p.1 < p.2 := by omega
      have hint := hic.2.2.1 p.1 (Nat.le_refl _)
        (by omega)
      have := hall p.1 (by omega)
      omega

variable {n k : Nat}

/-- Equal canonical-row comparison identifies the two leaf-row lists. -/
theorem rows_eq_of_testcanlab_tie {ctx : Ctx n} {st : Search n}
    (hinv : CanongInv ctx st.canong st.canonlab st.samerows)
    (h : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1
        = 0) :
    leafRows ctx st.canonlab = leafRows ctx st.lab := by
  rw [testcanlab_fst, rows_of_canongInv (updatecan_inv hinv)] at h
  have hc : listCmp VSet.rowCmp (leafRows ctx st.lab)
      (leafRows ctx st.canonlab) = .eq := by
    rcases hcc : listCmp VSet.rowCmp (leafRows ctx st.lab)
        (leafRows ctx st.canonlab) with _ | _ | _
    · rw [hcc] at h; exact absurd h (by decide)
    · rfl
    · rw [hcc] at h; exact absurd h (by decide)
  exact ((listCmp_eq_iff (fun _ _ => VSet.rowCmp_eq_iff) _ _).mp hc).symm

/-- A reached labelling lands in the vertex range. -/
theorem labOk_of_reach {G : Colored n k} {lab : Array Nat}
    (hsz : lab.size = n) (h : CellsReach G lab) : LabOk lab n := by
  intro i hi
  exact cellsReach_lt h i (by omega)

/-- A reached labelling is injective: it is a permutation of the
vertex range, hence duplicate-free. -/
theorem labInj_of_reach {G : Colored n k} {lab : Array Nat}
    (hsz : lab.size = n) (hn0 : 0 < n) (h : CellsReach G lab) :
    LabInj lab n := by
  have hp := isPerm_of_cellsReach hsz hn0 h
  have hnd : lab.toList.Nodup := hp.nodup_iff.mpr List.nodup_range
  intro i j hi hj he
  have hi' : i < lab.toList.length := by simp [hsz]; omega
  have hj' : j < lab.toList.length := by simp [hsz]; omega
  rw [getElem!_pos lab i (by omega), getElem!_pos lab j (by omega)]
    at he
  have hg : lab.toList[i] = lab.toList[j] := by simpa using he
  exact (List.Nodup.getElem_inj hnd).mp hg

private theorem getElem!_take'' {l : List Nat} {m i : Nat}
    (him : i < m) (hil : i < l.length) : (l.take m)[i]! = l[i]! := by
  have hti : i < (l.take m).length := by
    rw [List.length_take]
    omega
  rw [getElem!_pos (l.take m) i hti, getElem!_pos l i hil,
    List.getElem_take]

/-- The frozen divergence survives truncation: with the divergence
recorded at level `eqlevCanon + 1`, the path prefix down to any level
at or beyond it still compares below the incumbent, whatever comes
after. -/
theorem codeInv_take_listCmp_lt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    {M : Nat} (hM : eqlevCanon.toNat < M) (hMcs : M ≤ cs.length)
    (ext : List Nat) :
    listCmp compare (cs.take M ++ ext) (bs ++ [codeSentinel]) =
      .lt := by
  rcases hinv.tri with ⟨hcc, -⟩ | ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
  · cases hcc
  rcases hcase with ⟨-, hlt⟩ | ⟨hcc, -⟩
  case inr => cases hcc
  have hjM : j ≤ M := by
    rw [hec] at hM
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast] at hM
    omega
  refine listCmp_lt_of_prefix (j - 1) _ _
    (by rw [List.length_append, List.length_take]; omega)
    (by rw [List.length_append]; simp; omega)
    (fun i hi => ?_) ?_
  · rw [getElem!_append_left
        (as := cs.take M) (by rw [List.length_take]; omega),
      getElem!_append_sentinel (by omega),
      getElem!_take'' (by omega) (by omega)]
    have hp := hpre (i + 1) (by omega) (by omega)
    simpa using hp
  · rw [getElem!_append_left
        (as := cs.take M) (by rw [List.length_take]; omega),
      getElem!_append_sentinel (by omega),
      getElem!_take'' (by omega) (by omega),
      (by omega : j - 1 + 1 = j)]
    exact hlt

/-- The key-level truncated verdict: every subtree hanging below the
truncated path is dominated once the machine froze downward at or
above the truncation level. -/
theorem frozen_take_keyCmp_lt {nn : Nat} {cs bs : List Nat}
    {ctx : Ctx n} {canoncode : Array Nat} {canonlevel : Nat}
    {eqlevCanon : Int} {canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    {M : Nat} (hM : eqlevCanon.toNat < M) (hMcs : M ≤ cs.length)
    (K : Key n) :
    keyCmp (prefixKey (cs.take M) K) (incKey ctx bs canonlab) =
      .lt := by
  rw [prefixKey, incKey, keyCmp]
  show (match listCmp compare (cs.take M ++ K.codes)
      (bs ++ [codeSentinel]) with
    | .eq => listCmp VSet.rowCmp K.rows (leafRows ctx canonlab)
    | .lt => .lt
    | .gt => .gt) = .lt
  rw [codeInv_take_listCmp_lt hinv hM hMcs K.codes]

/-- `frozen_take_keyCmp_lt` in the `keyLe` form the absorption
consumes. -/
theorem frozen_take_keyLe {nn : Nat} {cs bs : List Nat}
    {ctx : Ctx n} {canoncode : Array Nat} {canonlevel : Nat}
    {eqlevCanon : Int} {canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    {M : Nat} (hM : eqlevCanon.toNat < M) (hMcs : M ≤ cs.length)
    (K : Key n) :
    keyLe (prefixKey (cs.take M) K) (incKey ctx bs canonlab) := by
  show keyCmp _ _ ≠ .gt
  rw [frozen_take_keyCmp_lt hinv hM hMcs K]
  intro h
  cases h

/-- The whole-path instance: with the machine frozen downward, every
subtree below the current path is dominated. -/
theorem frozen_keyLe {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    {canonlab : Array Nat}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    (K : Key n) :
    keyLe (prefixKey cs K) (incKey ctx bs canonlab) := by
  have hM : eqlevCanon.toNat < cs.length := by
    rcases hinv.tri with ⟨hcc, -⟩ |
      ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
    · cases hcc
    rw [hec]
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
    omega
  have h := frozen_take_keyLe (ctx := ctx) (canonlab := canonlab)
    hinv hM (Nat.le_refl cs.length) K
  rwa [List.take_length] at h

/-- A checked automorphism stabilizing the refined node's cells and
carrying one target-cell vertex onto another identifies the two
children's subtree keys. -/
theorem childKey_of_carried {ctx : Ctx n}
    (hgsz : ctx.g.size = n) {γ : Array Nat}
    (hAut : checkAutom ctx.g γ = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o o' : Nat}
    (hstab : CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (ho' : o' < lenT)
    (hlf : level + 1 + fuel ≤ n + 1)
    (hcarry : γ[rsLab[tc + o']!]! = rsLab[tc + o]!) :
    childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' := by
  rcases Decidable.em (o = o') with rfl | hne
  · rfl
  obtain ⟨σ, hσeq, hσrows⟩ := checkAutom_sound hgsz hAut
  have hvO : rsLab[tc + o]! < n := hok _ (by omega)
  have hvO' : rsLab[tc + o']! < n := hok _ (by omega)
  have hσv : σ.toFun rsLab[tc + o']! = rsLab[tc + o]! := by
    rw [hσeq _ hvO']
    exact hcarry
  obtain ⟨L, rfl⟩ : ∃ L, lenT = L + 1 := ⟨lenT - 1, by omega⟩
  have hbsz : (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o']!).1.size = n := by
    show (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
      rsLab[tc + o']!).size = n
    rw [breakout_go_size, hs]
  have hsegO : segN (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o]!).1 tc (L + 1) =
      rsLab[tc + o]! ::
        (segN rsLab tc (L + 1)).erase rsLab[tc + o]! := by
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
  have hstabSeg : ∀ (a l : Nat), IsCell rsPtn level a l → a + l ≤ n →
      (segN rsLab a l).Perm ((segN rsLab a l).map σ.toFun) := by
    intro a l hicl hbnd
    have h := hstab a l hicl
    rw [segN_map_of_le _ _ _ _ (by omega)] at h
    have hcg : (segN rsLab a l).map (fun w => γ[w]!) =
        (segN rsLab a l).map σ.toFun := by
      refine List.map_congr_left fun x hx => ?_
      rw [segN] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hilt := List.mem_range.mp hi
      exact (hσeq _ (hok _ (by omega))).symm
    rw [hcg] at h
    exact h
  have hicS : IsCell rsPtn (level + 1) tc (L + 1) :=
    isCell_succ hvals (by omega) hic
  have hend' : rsPtn[n - 1]! ≤ level := by
    have h := hend
    rwa [hsp] at h
  have hcp : cellsPerm (rsPtn.set! tc (level + 1)) (level + 1)
      (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
      ((breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1.map
        σ.toFun) := by
    refine cellsPerm_set! hicS (by omega) (Nat.le_refl tc)
      (by omega) ?_ ?_ ?_
    · rw [show tc + 1 - tc = 1 by omega, segN_cons, segN_zero,
        segN_cons, segN_zero, hheadO,
        getElem!_map_of_lt σ.toFun _ (by rw [hbsz]; omega), hheadO',
        hσv]
    · rw [show tc + (L + 1) - (tc + 1) = L by omega, htailO,
        segN_map_of_le _ _ _ _ (by rw [hbsz]; omega), htailO']
      have hCstab := hstabSeg tc (L + 1) hic hrange
      have hvoC : rsLab[tc + o]! ∈ segN rsLab tc (L + 1) := by
        rw [segN]
        exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩
      have hvo'C : rsLab[tc + o']! ∈ segN rsLab tc (L + 1) := by
        rw [segN]
        exact List.mem_map.mpr ⟨o', List.mem_range.mpr ho', rfl⟩
      have h5 : ((segN rsLab tc (L + 1)).map σ.toFun).Perm
          (rsLab[tc + o]! ::
            ((segN rsLab tc (L + 1)).erase rsLab[tc + o']!).map
              σ.toFun) := by
        have h := (List.perm_cons_erase hvo'C).map σ.toFun
        rw [List.map_cons, hσv] at h
        exact h
      exact ((List.perm_cons_erase hvoC).symm.trans
        (hCstab.trans h5)).cons_inv
    · intro a l hicA hdisj
      have hlabOeq : segN (breakout n rsLab rsPtn (level + 1) tc
          rsLab[tc + o]!).1 a l = segN rsLab a l := by
        refine segN_congr fun q hq => ?_
        show (breakout.go rsLab[tc + o]! (rsLab.size + 1) rsLab tc
          rsLab[tc + o]!)[a + q]! = rsLab[a + q]!
        rcases hdisj with hd | hd
        · exact breakout_go_outside _ _ _ _ _ (by omega)
        · exact breakout_go_outside_right _ (L + 1) _ _ _
            ⟨tc + o, by omega, by omega, by omega, rfl⟩ _ (by omega)
      have hlabO'eq : segN (breakout n rsLab rsPtn (level + 1) tc
          rsLab[tc + o']!).1 a l = segN rsLab a l := by
        refine segN_congr fun q hq => ?_
        show (breakout.go rsLab[tc + o']! (rsLab.size + 1) rsLab tc
          rsLab[tc + o']!)[a + q]! = rsLab[a + q]!
        rcases hdisj with hd | hd
        · exact breakout_go_outside _ _ _ _ _ (by omega)
        · exact breakout_go_outside_right _ (L + 1) _ _ _
            ⟨tc + o', by omega, by omega, by omega, rfl⟩ _ (by omega)
      rcases Nat.lt_or_ge a n with han | han
      · have hbnd : a + l ≤ n := by
          rcases Nat.lt_or_ge (a + l) (n + 1) with h1 | h1
          · omega
          · exfalso
            have hi := hicA.2.2.1 (n - 1) (by omega) (by omega)
            omega
        have hicL : IsCell rsPtn level a l :=
          isCell_pred hvals (by omega) hicA
        rw [hlabOeq,
          segN_map_of_le _ _ _ _ (by rw [hbsz]; exact hbnd),
          hlabO'eq]
        exact hstabSeg a l hicL hbnd
      · have hl1 : l = 1 := by
          rcases Nat.lt_or_ge l 2 with h2 | h2
          · have := hicA.1
            omega
          · exfalso
            have hi := hicA.2.2.1 a (Nat.le_refl a) (by omega)
            rw [getElem!_neg _ _ (by omega)] at hi
            have hd : (default : Nat) = 0 := rfl
            omega
        subst hl1
        rw [hlabOeq, segN_cons, segN_zero, segN_cons, segN_zero,
          getElem!_neg rsLab a (by omega),
          getElem!_neg ((breakout n rsLab rsPtn (level + 1) tc
              rsLab[tc + o']!).1.map σ.toFun) a
            (by rw [Array.size_map, hbsz]; omega)]
  have hokc := childNodeOk hs hok hsp hend hvals hic hrange ho
  have hokc' := childNodeOk hs hok hsp hend hvals hic hrange ho'
  exact (specNode_autom hσrows tcLevel fuel (level + 1)
    (lab₁ := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1)
    (lab₂ := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1)
    (ptn := (breakout n rsLab rsPtn (level + 1) tc rsLab[tc + o']!).2.1)
    (active := (breakout n rsLab rsPtn (level + 1) tc
      rsLab[tc + o']!).2.2)
    (numcells := numcells + 1) hcp hokc.labSize hokc'.labSize
    hokc.labOk hokc'.labOk hokc'.ptnSize hokc'.ptnEnd
    hokc'.starts hokc'.vals (by omega)).symm

end Hex.GraphIso.Nauty
