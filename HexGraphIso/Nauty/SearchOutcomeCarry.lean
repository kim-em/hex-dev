/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeSweep
public import HexGraphIso.Nauty.SearchOutcomeTotal
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.OrbJoin

public section

/-!
Facts carried alongside the corrected search induction that no existing
package records: leaf events keep the orbit array sound, small-cell
subtree facts survive a within-cell relabelling, guide relations compose
across a refinement, and a frozen comparison bounds every key below the
current path.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Frame equations -/

theorem pushAuto_firstlab (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).firstlab = st.firstlab := by
  rw [pushAuto]
  split <;> rfl

theorem pushAuto_orbits' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).orbits = st.orbits := by
  rw [pushAuto]
  split <;> rfl

theorem pushAuto_genTrace' (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

theorem recover_firstlab (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).firstlab = st.firstlab :=
  (recover_frames n inf level st).2.2.2.2.1

theorem recover_orbits (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).orbits = st.orbits :=
  (recover_frames n inf level st).2.2.2.2.2.2.2.2.1

theorem recover_genTrace (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).genTrace = st.genTrace :=
  (recover_store n inf level st).1

theorem recover_noncheaplevel (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).noncheaplevel =
      if level < st.noncheaplevel then level + 1 else st.noncheaplevel := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.noncheaplevel, ite_self]

theorem otherNodePrep_firstlab' (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).firstlab = st.firstlab :=
  (otherNodePrep_frames level code st).2.2.2.2.1

theorem otherNodePrep_orbits' (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).orbits = st.orbits :=
  (otherNodePrep_frames level code st).2.2.2.2.2.2.2.2.2.2.1

theorem otherNodePrep_genTrace' (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).genTrace = st.genTrace :=
  (otherNodePrep_store level code st).1

theorem processnode_firstlab' (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.firstlab = st.firstlab :=
  (processnode_frames ctx level numcells st).2.2.2.2.1

theorem processnode_noncheaplevel' (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.noncheaplevel = st.noncheaplevel :=
  (processnode_frames ctx level numcells st).2.2.2.2.2.2.2.1

/-! # Leaf events keep the orbit array sound -/

/-- The generator store paired with the orbit array, kept opaque while
the leaf event is unfolded. -/
@[expose] def genOrb (st : SearchSt n) : Array (Array Nat) × Array Nat :=
  (st.genTrace, st.orbits)

private theorem pushAuto_genOrb (st : SearchSt n) (pair : VSet n × VSet n) :
    genOrb (pushAuto st pair) = genOrb st := by
  rw [pushAuto]
  split <;> rfl

private theorem id_run_eq {α : Type} (x : Id α) : x.run = x := rfl

private theorem forIn_range_toList {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

private theorem forIn_scatter_eq (lab₁ lab₂ : Array Nat) :
    ∀ (l : List Nat) (base : Array Nat),
      (forIn l base (fun i r =>
        pure (ForInStep.yield (r.set! lab₁[i]! lab₂[i]!))) :
          Id (Array Nat)) =
      l.foldl (fun r i => r.set! lab₁[i]! lab₂[i]!) base
  | [], _ => rfl
  | i :: l, base => by
    rw [List.forIn_cons]
    exact forIn_scatter_eq lab₁ lab₂ l _

/-- `processnode` either leaves both the generator store and the orbit
array alone, or appends one generator and joins the orbits by it. -/
theorem processnode_genOrb (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    genOrb (processnode ctx level numcells st).2 = genOrb st ∨
    ∃ γ, genOrb (processnode ctx level numcells st).2 =
      (st.genTrace.push γ, (orbjoin st.orbits γ n).1) := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => genOrb x.2),
    pushAuto_genOrb]
  simp only [id_run_eq, forIn_range_toList, forIn_scatter_eq]
  simp only [genOrb, pushAuto_genTrace', pushAuto_orbits', ite_self]
  rcases Decidable.em (st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    with h1 | h1
  · rw [ite_eq_left h1]
    left
    rfl
  rw [ite_eq_right h1]
  rcases Decidable.em ((numcells == n) = true) with h2 | h2
  · rw [ite_eq_left h2]
    rcases Decidable.em (((st.eqlevFirst == level) &&
        (st.firstcode[level + 1]! == codeSentinel)) = true) with h3 | h3
    · rw [ite_eq_left h3]
      rcases Decidable.em (isautom ctx ((List.range n).foldl
            (fun r i => r.set! st.firstlab[i]! st.lab[i]!)
            (Array.replicate n 0)) = true) with h4 | h4
      · rw [ite_eq_left h4, ite_eq_right (by decide)]
        right
        exact ⟨_, rfl⟩
      · rw [ite_eq_right h4, ite_eq_left (by decide)]
        rcases Decidable.em ((st.compCanon == 0) = true) with h5 | h5
        · rw [ite_eq_left h5]
          rcases Decidable.em (level < st.canonlevel) with h6 | h6
          · rw [ite_eq_left h6, ite_eq_right (by decide)]
            left
            rfl
          · rw [ite_eq_right h6]
            rcases Decidable.em (((testcanlab ctx (updatecan ctx
                st.canong st.canonlab st.samerows) st.lab).1 == 0) =
                true) with h7 | h7
            · rw [ite_eq_left h7]
              right
              exact ⟨_, rfl⟩
            · rw [ite_eq_right h7]
              left
              rfl
        · rw [ite_eq_right h5, ite_eq_right h5]
          left
          rfl
    · rw [ite_eq_right h3, ite_eq_left (by decide)]
      rcases Decidable.em ((st.compCanon == 0) = true) with h5 | h5
      · rw [ite_eq_left h5]
        rcases Decidable.em (level < st.canonlevel) with h6 | h6
        · rw [ite_eq_left h6, ite_eq_right (by decide)]
          left
          rfl
        · rw [ite_eq_right h6]
          rcases Decidable.em (((testcanlab ctx (updatecan ctx
              st.canong st.canonlab st.samerows) st.lab).1 == 0) =
              true) with h7 | h7
          · rw [ite_eq_left h7]
            right
            exact ⟨_, rfl⟩
          · rw [ite_eq_right h7]
            left
            rfl
      · rw [ite_eq_right h5, ite_eq_right h5]
        left
        rfl
  · rw [ite_eq_right h2]
    left
    rfl

/-- Every checked generator list keeps the orbit relation symmetric. -/
theorem orbConn_symm_of_check {ctx : Ctx n} {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true) :
    ∀ a b, OrbConn gens n a b → OrbConn gens n b a :=
  orbConn_symm (fun γ hγ v hv' => checkAutom_bound (hv γ hγ) v hv')
    (fun γ hγ => checkAutom_inj (hv γ hγ))

/-- The orbit array stays sound across a leaf event whose appended
generator, if any, is checked. -/
theorem processnode_orbSound {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hsound : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcheck : ∀ γ ∈ (processnode ctx level numcells st).2.genTrace,
      checkAutom ctx.g γ = true) :
    OrbSound
      (OrbConn (processnode ctx level numcells st).2.genTrace.toList n)
      (processnode ctx level numcells st).2.orbits n := by
  rcases processnode_genOrb ctx level numcells st with hsame | ⟨γ, hpush⟩
  · have hgen : (processnode ctx level numcells st).2.genTrace =
        st.genTrace := congrArg Prod.fst hsame
    have horb : (processnode ctx level numcells st).2.orbits =
        st.orbits := congrArg Prod.snd hsame
    rw [hgen, horb]
    exact hsound
  · have hgen : (processnode ctx level numcells st).2.genTrace =
        st.genTrace.push γ := congrArg Prod.fst hpush
    have horb : (processnode ctx level numcells st).2.orbits =
        (orbjoin st.orbits γ n).1 := congrArg Prod.snd hpush
    rw [hgen, horb]
    rw [hgen] at hcheck
    have hsub : ∀ δ ∈ st.genTrace.toList,
        δ ∈ (st.genTrace.push γ).toList := by
      intro δ hδ
      rw [Array.mem_toList_iff] at hδ ⊢
      exact Array.mem_push.mpr (Or.inl hδ)
    have hcheck' : ∀ δ ∈ (st.genTrace.push γ).toList,
        checkAutom ctx.g δ = true := by
      intro δ hδ
      exact hcheck δ (Array.mem_toList_iff.mp hδ)
    have hγ : γ ∈ (st.genTrace.push γ).toList := by
      rw [Array.mem_toList_iff]
      exact Array.mem_push.mpr (Or.inr rfl)
    apply orbjoin_orbSound (orbConn_symm_of_check hcheck')
      (orbConn_trans _)
      (orbSound_mono (orbConn_mono hsub) hsound)
    intro i hi
    refine ⟨checkAutom_bound (hcheck' γ hγ) i hi, ?_⟩
    unfold OrbConn
    exact ⟨hi, checkAutom_bound (hcheck' γ hγ) i hi, wordConn_step hγ i⟩

/-! # Small-cell subtree facts across a within-cell relabelling -/

/-- The small-cell subtree facts depend on the labelling only through
its cell contents. -/
theorem SubtreeOk.ofCellsPerm {ctx : Ctx n} {level : Nat} {r : RefineSt n}
    {lab' : Array Nat} (h : SubtreeOk ctx level r)
    (hperm : cellsPerm r.ptn level r.lab lab')
    (hsz : lab'.size = n) (hok : LabOk lab' n)
    (hinj : LabInj lab' n) :
    SubtreeOk ctx level { r with lab := lab' } := by
  refine ⟨⟨⟨hsz, hok, h.it.ok.ptnSize, h.it.ok.ptnEnd⟩,
    hinj, h.it.vals, h.it.lvl⟩, ?_, h.acc, h.shape⟩
  exact h.eqt.ofCellsPerm hperm h.it.ok.ptnSize h.it.ok.ptnEnd

/-- The subtree facts ignore the refinement bookkeeping fields. -/
theorem SubtreeOk.ofFrames {ctx : Ctx n} {level : Nat} {r r' : RefineSt n}
    (h : SubtreeOk ctx level r) (hlab : r'.lab = r.lab)
    (hptn : r'.ptn = r.ptn)
    (hcells : r'.numcells = r.numcells) :
    SubtreeOk ctx level r' := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, h.it.lvl⟩, ?_, ?_, ?_⟩
  · rw [hlab]; exact h.it.ok.labSize
  · rw [hlab]; exact h.it.ok.labOk
  · rw [hptn]; exact h.it.ok.ptnSize
  · rw [hptn]; exact h.it.ok.ptnEnd
  · rw [hlab]; exact h.it.inj
  · rw [hptn]; exact h.it.vals
  · rw [hlab, hptn]; exact h.eqt
  · rw [hptn, hcells]; exact h.acc
  · rw [hptn]; exact h.shape

/-! # Guide relations across a refinement -/

namespace GuideRel

/-- Compose a guide relation whose second leg is stated over the refined
frame of the first leg's endpoint.  Refinement only closes more cell
boundaries, so a within-cell permutation of the refined frame is one of
the coarser frame. -/
theorem transRefine {level : Nat} {a b c : SearchSt n}
    (hab : GuideRel level a b) (hbc : GuideRel level b c)
    (hsz : a.ptn.size = b.ptn.size) (hlb : b.lab.size = b.ptn.size)
    (hlc : c.canonlab.size = b.ptn.size)
    (hendB : b.ptn[b.ptn.size - 1]! ≤ level)
    (hendA : a.ptn[a.ptn.size - 1]! ≤ level)
    (hgrow : ∀ q : Nat, a.ptn[q]! ≤ level → b.ptn[q]! ≤ level)
    (hperm : cellsPerm a.ptn level a.lab b.lab) :
    GuideRel level a c := by
  constructor
  · exact hbc.first.trans hab.first
  · exact hbc.order
  · rcases hbc.canon with hold | hnew
    · rw [hold.1, hold.2]
      exact hab.canon
    · right
      refine ⟨hnew.1, ?_⟩
      have hcoarse : cellsPerm a.ptn level b.lab c.canonlab :=
        cellsPerm_coarsen hsz hlb hlc hnew.2 hendB hendA hgrow
      exact cellsPerm_trans hperm hcoarse

end GuideRel

/-! # Result-side facts -/

/-- Every packaged event leaves the comparison sign nonpositive. -/
theorem EventOut.nonpositive {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    out.compCanon ≤ 0 := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ =>
      rcases event.machines with hplain | hreset
      · exact hplain.1
      · exact Int.le_of_lt hreset.1

/-- A negative comparison sign is exactly the frozen downward machine. -/
theorem CodeCmpInv.neg_eq {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    (h : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon compCanon)
    (hneg : compCanon < 0) : compCanon = -1 := by
  rcases h.tri with hzero | ⟨_, _, _, _, _, _, hdown | hup⟩
  · omega
  · exact hdown.1
  · omega

/-- With the machine frozen downward, every key below the current path is
dominated by the incumbent. -/
theorem CodeCmpInv.frozenBound {nn : Nat} {cs bs : List Nat} {ctx : Ctx n}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon compCanon : Int}
    {canonlab : Array Nat}
    (h : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon compCanon)
    (hneg : compCanon < 0) (K : Key n) :
    keyLe (prefixKey cs K) (incKey ctx bs canonlab) := by
  have hcc := h.neg_eq hneg
  subst hcc
  exact frozen_keyLe h K

/-- A frozen node's exact maximum is the unchanged incumbent: every child
key is dominated. -/
theorem incMax_of_frozen {ctx : Ctx n} {bs : List Nat} {canonlab : Array Nat}
    {K : Key n} (hle : keyLe K (incKey ctx bs canonlab)) :
    incMax (some (incKey ctx bs canonlab)) K = incKey ctx bs canonlab := by
  rw [incMax]
  exact keyMax_eq_left hle

/-- Every off-path run only improves the incumbent. -/
theorem OtherRun.grows {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {codes fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (h : OtherRun G ctx tcLevel specFuel runFuel level codes fs st out
      numcells best outBest receiptTrail eventTrail r)
    (hfuel : runFuel ≠ 0) : IncGrows best outBest := by
  cases h.node.exit with
  | done returned exact => rw [exact]; exact IncGrows.incMax best _
  | unwind target returned below sound payload located control =>
      exact sound.grows
  | frozen below exact freeze => rw [exact]; exact IncGrows.incMax best _
  | cheap boundary returned positive atOrAbove saved exact =>
      rw [exact]; exact IncGrows.incMax best _
  | exhausted returned state incumbent emptyFuel => exact (hfuel emptyFuel).elim

end Hex.GraphIso.Nauty
