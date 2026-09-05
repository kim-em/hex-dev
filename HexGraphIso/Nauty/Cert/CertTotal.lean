/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert.CanonForm
public import HexGraphIso.Nauty.Invariant.Reach
public import HexGraphIso.Nauty.Cert.TraceAgree
import all HexGraphIso.Nauty.Cert.CertAutom
import all HexGraphIso.Nauty.Cert.CanonForm

public section

/-!
Totality of the trace-driven candidate producer, and the reduction of
`certifyCanon?` totality to the certificate replay: with no node
budget the producer never exhausts, its key is read off the traced
run, and every conjunct of `checkCanon` except the `checkKey` replay
is discharged by the landed transcription-side results. What remains
of `(certifyCanon? G).isSome` after this file is exactly the layer-
three obligation: the replay accepts the produced certificate against
the traced key.
-/

namespace Hex.GraphIso.Nauty

/-- Charging with no budget is free. -/
private theorem charge_none {st : AutState} (h : st.budget = none) :
    st.charge = st := by
  rw [AutState.charge, h]

/-- Admission never touches the budget. -/
private theorem admit_budget (ctx : Ctx n) (st : AutState)
    (γ : Array Nat) : (st.admit ctx γ).budget = st.budget := by
  rw [AutState.admit]
  simp only [Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

/-- Admission never exhausts. -/
private theorem admit_exhausted (ctx : Ctx n) (st : AutState)
    (γ : Array Nat) : (st.admit ctx γ).exhausted = st.exhausted := by
  rw [AutState.admit]
  simp only [Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

/-- Harvesting never touches the budget. -/
private theorem harvest_budget (ctx : Ctx n) (st : AutState)
    (lab : Array Nat) : (st.harvest ctx lab).budget = st.budget := by
  rw [AutState.harvest]
  simp only []
  repeat' split
  all_goals try simp only [admit_budget]
  all_goals rfl

/-- Harvesting never exhausts. -/
private theorem harvest_exhausted (ctx : Ctx n) (st : AutState)
    (lab : Array Nat) :
    (st.harvest ctx lab).exhausted = st.exhausted := by
  rw [AutState.harvest]
  simp only []
  repeat' split
  all_goals try simp only [admit_exhausted]
  all_goals rfl

/-- Fold steps that preserve a state predicate preserve it over the
whole fold. -/
private theorem foldl_pres {α β : Type} (f : β → α → β)
    (P : β → Prop) :
    ∀ (l : List α) (b : β), P b → (∀ b a, P b → P (f b a)) →
      P (l.foldl f b)
  | [], _, hb, _ => hb
  | a :: l, b, hb, hstep => foldl_pres f P l (f b a) (hstep b a hb) hstep

/-- With no budget, the certificate pass never exhausts and keeps no
budget: the two fields the totality of `produceCand` reads. -/
private theorem certifyNodeAutom_nobudget (ctx : Ctx n) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active : VSet n) (numcells : Nat) (bcodes : List Nat) (st : AutState),
      st.budget = none → st.exhausted = false →
      (certifyNodeAutom ctx tcLevel fuel level lab ptn active numcells
          bcodes st).2.budget = none ∧
        (certifyNodeAutom ctx tcLevel fuel level lab ptn active
          numcells bcodes st).2.exhausted = false
  | 0, _, _, _, _, _, _, st, hb, he => ⟨hb, he⟩
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st, hb, he => by
    rw [certifyNodeAutom.eq_def]
    dsimp only
    rw [charge_none hb]
    rw [ite_eq_right (by rw [he]; exact Bool.false_ne_true)]
    match bcodes with
    | [] => exact ⟨hb, he⟩
    | bc :: brest =>
      dsimp only
      split
      · exact ⟨hb, he⟩
      · exact ⟨hb, he⟩
      · split
        · exact ⟨(harvest_budget ctx st _).trans hb,
            (harvest_exhausted ctx st _).trans he⟩
        · dsimp only
          refine foldl_pres _
            (fun (acc : List CertNode × AutState ×
                Option (Nat × Array (Array Nat × Array Nat))) =>
              acc.2.1.budget = none ∧ acc.2.1.exhausted = false)
            (List.range _) ([], st, none) ?_ ?_
          · exact ⟨hb, he⟩
          intro acc o hacc
          split
          · split
            · exact hacc
            · dsimp only
              exact certifyNodeAutom_nobudget ctx tcLevel fuel _ _ _
                _ _ _ _ hacc.1 hacc.2
          · dsimp only
            exact certifyNodeAutom_nobudget ctx tcLevel fuel _ _ _
              _ _ _ _ hacc.1 hacc.2

variable {n k : Nat}

/-- With no node budget, the candidate producer always returns a
candidate. -/
theorem produceCand_none_isSome (G : Colored n k) :
    (produceCand G none).isSome := by
  rw [produceCand]
  dsimp only
  rw [ite_eq_right (by simp [Option.any])]
  have hst1 : ((runColoredTraced G).autos.foldl
      (fun st γ => st.admit { g := rowsOf G } γ)
      (AutState.init n none)).budget = none ∧
      ((runColoredTraced G).autos.foldl
      (fun st γ => st.admit { g := rowsOf G } γ)
      (AutState.init n none)).exhausted = false := by
    rw [← Array.foldl_toList]
    refine foldl_pres _
      (fun (st : AutState) => st.budget = none ∧
        st.exhausted = false) _ _ ⟨rfl, rfl⟩ ?_
    intro st γ hst
    exact ⟨(admit_budget _ st γ).trans hst.1,
      (admit_exhausted _ st γ).trans hst.2⟩
  have h3 := certifyNodeAutom_nobudget { g := rowsOf G } 100
    n 1 (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2)
    (initActive n (initialPartition G).2)
    (initialPartition G).2.length
    (((runColoredTraced G).bestCodes ++ [codeSentinel]))
    { ((runColoredTraced G).autos.foldl
        (fun st γ => st.admit { g := rowsOf G } γ)
        (AutState.init n none)) with
      refLeaf := some (runColoredTraced G).result.canonlab }
    hst1.1 hst1.2
  split
  · next hcond =>
    rw [h3.2] at hcond
    cases hcond
  · rfl

/-- The key of every produced candidate is read off the traced run:
the recorded code chain with the sentinel, and the spec rows of the
traced canonical labelling. -/
theorem produceCand_key {G : Colored n k} {budget : Option Nat}
    {cert : CertNode} {B : Key n}
    (h : produceCand G budget = some (cert, B)) :
    B = ⟨(runColoredTraced G).bestCodes ++ [codeSentinel],
      leafRows { g := rowsOf G }
        (runColoredTraced G).result.canonlab⟩ := by
  rw [produceCand] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h'
      injection h' with h1 h2
      rw [← h2]

/-- A sized permutation array parses as a label. -/
private theorem label_ofArray?_isSome {lab : Array Nat}
    (hsz : lab.size = n)
    (hperm : lab.toList.Perm (List.range n)) :
    ∃ l, Label.ofArray? n lab = some l := by
  have hbound : ∀ v ∈ lab, v < n := by
    intro v hv
    have hm : v ∈ lab.toList := by simpa using hv
    exact List.mem_range.mp (hperm.mem_iff.mp hm)
  have hmapval : ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)).toList.map
      Fin.val) = lab.toList := by
    refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
    rw [List.getElem_map, Array.getElem_toList, Array.getElem_map,
      Array.getElem_attach]
    exact (Array.getElem_toList _).symm
  have hnodupv : ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList.Nodup := by
    have hmv : (((lab.attach.map fun v =>
        (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
        Array (Fin n)).toList.map Fin.val).Nodup := by
      rw [hmapval]
      exact hperm.symm.nodup List.nodup_range
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hmv
    rw [List.nodup_iff_pairwise_ne]
    exact hmv.imp fun h he => h (congrArg Fin.val he)
  have hcompl : ∀ i : Fin n, i ∈ ((lab.attach.map fun v =>
      (⟨v.val, hbound v.val v.property⟩ : Fin n)) :
      Array (Fin n)).toList := by
    intro i
    have hm : i.val ∈ lab.toList :=
      hperm.mem_iff.mpr (List.mem_range.mpr i.isLt)
    rw [← hmapval] at hm
    rcases List.mem_map.mp hm with ⟨x, hx, hxe⟩
    exact (Fin.eq_of_val_eq hxe : x = i) ▸ hx
  rw [Label.ofArray?,
    dite_eq_left (⟨hsz, hbound⟩ : lab.size = n ∧ ∀ v ∈ lab, v < n)]
  rw [Label.ofVector?, Perm.ofVector?]
  rw [dite_eq_left ⟨hnodupv, hcompl⟩]
  exact ⟨_, rfl⟩

/-- The reduction of `certifyCanon?` totality to the certificate
replay: if the produced certificate replays against the traced key,
every other conjunct of the single trusted validation is discharged
by the landed transcription-side results, so the certified
canonicalization succeeds. The hypothesis is exactly the layer-three
obligation of the verified search refinement programme. -/
theorem certifyCanon?_isSome_of_checkKey (G : Colored n k)
    (h : ∀ cert B, produceCand G none = some (cert, B) →
      checkKey G cert B = true) :
    (certifyCanon? G).isSome := by
  rw [certifyCanon?]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    rw [ite_eq_left (by rfl)]
    obtain ⟨l, hl⟩ := label_ofArray?_isSome (canonlab_size G)
      (canonlab_perm_range G)
    dsimp only
    rw [checkCanon.eq_def, hl]
    dsimp only
    rw [ite_eq_left ?_]
    · rfl
    · refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
        ⟨?_, ?_⟩, ?_⟩
      · rfl
      · refine beq_iff_eq.mpr ?_
        rw [leafRows]
        rfl
      · exact colorSortedCheck_canonlab G
  · rw [ite_eq_right (by simp; omega)]
    have hps := produceCand_none_isSome G
    rcases hp : produceCand G none with _ | ⟨cert, B⟩
    · rw [hp] at hps
      cases hps
    · dsimp only
      have hkey := h cert B hp
      have hB := produceCand_key hp
      obtain ⟨l, hl⟩ := label_ofArray?_isSome (canonlab_size G)
        (canonlab_perm_range G)
      rw [checkCanon.eq_def, hl]
      dsimp only
      rw [ite_eq_left ?_]
      · rfl
      · refine (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr
          ⟨hkey, ?_⟩, colorSortedCheck_canonlab G⟩
        refine beq_iff_eq.mpr ?_
        rw [hB]
        dsimp only
        rw [runColoredTraced_result]

end Hex.GraphIso.Nauty
