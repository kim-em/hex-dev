/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CertTotal
public import HexGraphIso.Nauty.Complete
import all HexGraphIso.Nauty.CertAutom
import all HexGraphIso.Nauty.Cert

public section

/-!
The conditional replay spine: the certificate emitted by the
trace-driven producer replays through the trusted checker. The
theorem is conditional on the two facts the producer cannot certify
about itself: domination (the claimed key bounds this subtree's spec
key, `keyLe (specNode ...) ⟨bcodes, brows⟩`) and store validity
(every `.autom` record's generator is a checked automorphism). Under
those hypotheses `checkNode` accepts every node the walk emits, and
a rejection verdict (`some false`) forces the subtree strictly below
the claim, so at the root a dominated-and-achieved key replays to
`some true`, which is `checkKey`.

The domination hypothesis is semantic and walk-independent: it is
instantiated at the root by the layer-three theorem that the traced
key is `canonSpecKey`. Store validity is instantiated by the traced
generator-validity results. The final assembly is
`produceCand_checkKey` at the end of this file, whose shape matches
the hypothesis of `certifyCanon?_isSome_of_checkKey`.
-/

namespace Hex.GraphIso.Nauty

/-! # Budget plumbing

With no node budget, charging is free and the walk never exhausts.
These mirror the private lemmas of `CertTotal`. -/

private theorem charge_none' {st : AutState} (h : st.budget = none) :
    st.charge = st := by
  rw [AutState.charge, h]

private theorem admit_budget' (ctx : Ctx) (st : AutState)
    (γ : Array Nat) : (st.admit ctx γ).budget = st.budget := by
  rw [AutState.admit]
  set_option linter.unusedSimpArgs false in
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

private theorem admit_exhausted' (ctx : Ctx) (st : AutState)
    (γ : Array Nat) : (st.admit ctx γ).exhausted = st.exhausted := by
  rw [AutState.admit]
  set_option linter.unusedSimpArgs false in
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

private theorem harvest_budget' (ctx : Ctx) (st : AutState)
    (lab : Array Nat) : (st.harvest ctx lab).budget = st.budget := by
  rw [AutState.harvest]
  set_option linter.unusedSimpArgs false in
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals try simp only [admit_budget']
  all_goals rfl

private theorem harvest_exhausted' (ctx : Ctx) (st : AutState)
    (lab : Array Nat) :
    (st.harvest ctx lab).exhausted = st.exhausted := by
  rw [AutState.harvest]
  set_option linter.unusedSimpArgs false in
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals try simp only [admit_exhausted']
  all_goals rfl

private theorem foldl_pres' {α β : Type} (f : β → α → β)
    (P : β → Prop) :
    ∀ (l : List α) (b : β), P b → (∀ b a, P b → P (f b a)) →
      P (l.foldl f b)
  | [], _, hb, _ => hb
  | a :: l, b, hb, hstep => foldl_pres' f P l (f b a) (hstep b a hb) hstep

private theorem certifyNodeAutom_nobudget' (ctx : Ctx) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (bcodes : List Nat) (st : AutState),
      st.budget = none → st.exhausted = false →
      (certifyNodeAutom ctx tcLevel fuel level lab ptn active numcells
          bcodes st).2.budget = none ∧
        (certifyNodeAutom ctx tcLevel fuel level lab ptn active
          numcells bcodes st).2.exhausted = false
  | 0, _, _, _, _, _, _, st, hb, he => ⟨hb, he⟩
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st, hb, he => by
    rw [certifyNodeAutom.eq_def]
    dsimp only
    rw [charge_none' hb]
    rw [ite_eq_right (by rw [he]; exact Bool.false_ne_true)]
    match bcodes with
    | [] => exact ⟨hb, he⟩
    | bc :: brest =>
      dsimp only
      split
      · exact ⟨hb, he⟩
      · exact ⟨hb, he⟩
      · split
        · exact ⟨(harvest_budget' ctx st _).trans hb,
            (harvest_exhausted' ctx st _).trans he⟩
        · dsimp only
          refine foldl_pres' _
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
              exact certifyNodeAutom_nobudget' ctx tcLevel fuel _ _ _
                _ _ _ _ hacc.1 hacc.2
          · dsimp only
            exact certifyNodeAutom_nobudget' ctx tcLevel fuel _ _ _
              _ _ _ _ hacc.1 hacc.2

/-! # Key-order helpers -/

/-- A key with a nonempty code list exceeds any key with an empty
one. -/
theorem keyCmp_codes_nil_gt {c : Nat} {cs r br : List Nat} :
    keyCmp ⟨c :: cs, r⟩ ⟨[], br⟩ = .gt := by
  rw [keyCmp]
  simp only [listCmp]

/-- The maximum of strictly dominated keys is strictly dominated. -/
theorem keysMax_lt {b k : Key} {l : List Key}
    (hk : keyCmp k b = .lt) (hl : ∀ y ∈ l, keyCmp y b = .lt) :
    keyCmp (keysMax k l) b = .lt := by
  induction l generalizing k with
  | nil => exact hk
  | cons y l ih =>
    rw [keysMax]
    refine ih ?_ fun z hz => hl z (List.mem_cons_of_mem _ hz)
    rcases keyMax_mem k y with he | he
    · rw [he]
      exact hk
    · rw [he]
      exact hl y List.mem_cons_self

/-! # Per-record predicates over a certificate tree -/

mutual

/-- Every `.autom` record's generator satisfies `P`. -/
def AutomsOk (P : Array Nat → Prop) : CertNode → Prop
  | .leaf => True
  | .codePrune => True
  | .autom _ γ => P γ
  | .node children => AutomsOkList P children

/-- `AutomsOk` over a list of subtrees. -/
def AutomsOkList (P : Array Nat → Prop) : List CertNode → Prop
  | [] => True
  | c :: cs => AutomsOk P c ∧ AutomsOkList P cs

end

theorem automsOkList_of_mem {P : Array Nat → Prop}
    {cs : List CertNode} (h : AutomsOkList P cs) :
    ∀ c ∈ cs, AutomsOk P c := by
  induction cs with
  | nil => intro c hc; cases hc
  | cons c' cs ih =>
    intro c hc
    rw [AutomsOkList] at h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact ih h.2 c hc

theorem automsOkList_of_forall {P : Array Nat → Prop} :
    ∀ {cs : List CertNode}, (∀ c ∈ cs, AutomsOk P c) →
      AutomsOkList P cs
  | [], _ => trivial
  | c :: _cs, h =>
    ⟨h c List.mem_cons_self,
      automsOkList_of_forall fun c' hc' =>
        h c' (List.mem_cons_of_mem _ hc')⟩

mutual

theorem automsOk_mono {P Q : Array Nat → Prop}
    (hPQ : ∀ γ, P γ → Q γ) :
    ∀ (c : CertNode), AutomsOk P c → AutomsOk Q c
  | .leaf, _ => trivial
  | .codePrune, _ => trivial
  | .autom _ γ, h => hPQ γ h
  | .node children, h => automsOkList_mono hPQ children h

theorem automsOkList_mono {P Q : Array Nat → Prop}
    (hPQ : ∀ γ, P γ → Q γ) :
    ∀ (cs : List CertNode), AutomsOkList P cs → AutomsOkList Q cs
  | [], _ => trivial
  | c :: cs, h =>
    ⟨automsOk_mono hPQ c h.1, automsOkList_mono hPQ cs h.2⟩

end

mutual

/-- The depth of a certificate tree. -/
def CertNode.depth : CertNode → Nat
  | .leaf => 1
  | .codePrune => 1
  | .autom _ _ => 1
  | .node children => 1 + CertNode.depthList children

/-- The maximum depth of a list of certificate subtrees. -/
def CertNode.depthList : List CertNode → Nat
  | [] => 0
  | c :: cs => max c.depth (CertNode.depthList cs)

end

theorem depthList_le {cs : List CertNode} {d : Nat}
    (h : ∀ c ∈ cs, CertNode.depth c ≤ d) :
    CertNode.depthList cs ≤ d := by
  induction cs with
  | nil => exact Nat.zero_le d
  | cons c cs ih =>
    rw [CertNode.depthList]
    exact Nat.max_le.mpr ⟨h c List.mem_cons_self,
      ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')⟩

theorem depth_le_of_mem {cs : List CertNode} {c : CertNode}
    (hc : c ∈ cs) : CertNode.depth c ≤ CertNode.depthList cs := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
    rw [CertNode.depthList]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih hc) (Nat.le_max_right ..)

/-- The walk emits trees no deeper than its fuel allows. -/
theorem certifyNodeAutom_depth (ctx : Ctx) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (bcodes : List Nat) (st : AutState),
      CertNode.depth (certifyNodeAutom ctx tcLevel fuel level lab ptn
        active numcells bcodes st).1 ≤ fuel + 1
  | 0, _, _, _, _, _, _, _ => Nat.le_refl 1
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st => by
    rw [certifyNodeAutom.eq_def]
    dsimp only
    split
    · exact Nat.le_add_left 1 (fuel + 1)
    · match bcodes with
      | [] => exact Nat.le_add_left 1 (fuel + 1)
      | bc :: brest =>
        dsimp only
        split
        · exact Nat.le_add_left 1 (fuel + 1)
        · exact Nat.le_add_left 1 (fuel + 1)
        · split
          · exact Nat.le_add_left 1 (fuel + 1)
          · dsimp only
            rw [CertNode.depth]
            refine Nat.le_trans (Nat.add_le_add_left
              (depthList_le (d := fuel + 1) fun c hc => ?_) 1)
              (by omega)
            rw [List.mem_reverse] at hc
            refine foldl_pres' _
              (fun (acc : List CertNode × AutState ×
                  Option (Nat × Array (Array Nat × Array Nat))) =>
                ∀ c ∈ acc.1, CertNode.depth c ≤ fuel + 1)
              (List.range _) ([], _, none)
              (fun c hc => absurd hc (by simp)) ?_ c hc
            intro acc o hacc
            split
            · split
              · intro c' hc'
                rcases List.mem_cons.mp hc' with rfl | hc'
                · exact Nat.le_add_left 1 fuel
                · exact hacc c' hc'
              · dsimp only
                intro c' hc'
                rcases List.mem_cons.mp hc' with rfl | hc'
                · exact certifyNodeAutom_depth ctx tcLevel fuel _ _
                    _ _ _ _ _
                · exact hacc c' hc'
            · dsimp only
              intro c' hc'
              rcases List.mem_cons.mp hc' with rfl | hc'
              · exact certifyNodeAutom_depth ctx tcLevel fuel _ _ _
                  _ _ _ _
              · exact hacc c' hc'

/-! # Every valid record's generator is in the validated store -/

private theorem gammaEq_self (γ : Array Nat) : gammaEq γ γ = true := by
  rw [gammaEq]
  exact beq_self_eq_true _

private theorem containsGamma_of_mem {vgens : List (Array Nat)}
    {γ : Array Nat} (h : γ ∈ vgens) : containsGamma vgens γ = true := by
  induction vgens with
  | nil => cases h
  | cons g rest ih =>
    rw [containsGamma]
    rcases List.mem_cons.mp h with rfl | h
    · rw [gammaEq_self]
      rfl
    · rw [ih h]
      exact Bool.or_true _

private theorem mem_of_containsGamma {vgens : List (Array Nat)}
    {γ : Array Nat} (h : containsGamma vgens γ = true) : γ ∈ vgens := by
  induction vgens with
  | nil => cases h
  | cons g rest ih =>
    rw [containsGamma] at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h2
    · exact gammaEq_eq h1 ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h2)

/-- Whatever `certGammas` has collected stays collected. -/
private theorem containsGamma_certGammas_mono {γ : Array Nat} :
    ∀ (fuel : Nat) (cert : CertNode) (acc : List (Array Nat)),
      containsGamma acc γ = true →
      containsGamma (certGammas fuel cert acc) γ = true
  | 0, _, _, h => h
  | fuel + 1, .leaf, _, h => h
  | fuel + 1, .codePrune, _, h => h
  | fuel + 1, .autom _ γ', acc, h => by
    rw [certGammas]
    split
    · exact h
    · rw [containsGamma, h]
      exact Bool.or_true _
  | fuel + 1, .node children, acc, h => by
    rw [certGammas]
    exact foldl_pres' _ (fun l => containsGamma l γ = true) children
      acc h fun l c hl => containsGamma_certGammas_mono fuel c l hl

mutual

/-- `certGammas` collects every record of a tree within its depth. -/
private theorem certGammas_covers :
    ∀ (fuel : Nat) (cert : CertNode) (acc : List (Array Nat)),
      CertNode.depth cert ≤ fuel →
      AutomsOk (fun γ => containsGamma (certGammas fuel cert acc) γ =
        true) cert
  | 0, cert, _, hd => by
    exfalso
    rcases cert with _ | _ | _ | children
    all_goals rw [CertNode.depth] at hd; omega
  | fuel + 1, .leaf, _, _ => trivial
  | fuel + 1, .codePrune, _, _ => trivial
  | fuel + 1, .autom _ γ, acc, _ => by
    show containsGamma (certGammas (fuel + 1) (.autom _ γ) acc) γ = true
    rw [certGammas]
    split
    · next h => exact h
    · rw [containsGamma, gammaEq_self]
      rfl
  | fuel + 1, .node children, acc, hd => by
    show AutomsOkList _ children
    rw [certGammas]
    rw [CertNode.depth] at hd
    exact certGammas_covers_list fuel children acc fun c hc =>
      Nat.le_trans (depth_le_of_mem hc) (by omega)

/-- The list companion of `certGammas_covers`. -/
private theorem certGammas_covers_list (fuel : Nat) :
    ∀ (children : List CertNode) (acc : List (Array Nat)),
      (∀ c ∈ children, CertNode.depth c ≤ fuel) →
      AutomsOkList (fun γ =>
        containsGamma (children.foldl
          (fun a c => certGammas fuel c a) acc) γ = true) children
  | [], _, _ => trivial
  | c :: cs, acc, hdc => by
    rw [List.foldl_cons]
    refine ⟨?_, certGammas_covers_list fuel cs (certGammas fuel c acc)
      fun c' hc' => hdc c' (List.mem_cons_of_mem _ hc')⟩
    refine automsOk_mono (fun γ hγ => ?_) c
      (certGammas_covers fuel c acc (hdc c List.mem_cons_self))
    exact foldl_pres' _ (fun l => containsGamma l γ = true) cs
      (certGammas fuel c acc) hγ
      fun l c' hl => containsGamma_certGammas_mono fuel c' l hl

end

mutual

private theorem automsOk_and {P Q : Array Nat → Prop} :
    ∀ (c : CertNode), AutomsOk P c → AutomsOk Q c →
      AutomsOk (fun γ => P γ ∧ Q γ) c
  | .leaf, _, _ => trivial
  | .codePrune, _, _ => trivial
  | .autom _ _, h1, h2 => ⟨h1, h2⟩
  | .node children, h1, h2 => automsOkList_and children h1 h2

private theorem automsOkList_and {P Q : Array Nat → Prop} :
    ∀ (cs : List CertNode), AutomsOkList P cs → AutomsOkList Q cs →
      AutomsOkList (fun γ => P γ ∧ Q γ) cs
  | [], _, _ => trivial
  | c :: cs, h1, h2 =>
    ⟨automsOk_and c h1.1 h2.1, automsOkList_and cs h1.2 h2.2⟩

end

/-- A certificate whose records all pass `checkAutom` has every
record's generator in its own validated store. -/
theorem automsOk_validGammas {g : Array Nat} {nn : Nat}
    {cert : CertNode} (hd : CertNode.depth cert ≤ nn + 2)
    (hv : AutomsOk (fun γ => checkAutom g γ nn = true) cert) :
    AutomsOk (fun γ => containsGamma (validGammas g nn cert) γ = true)
      cert := by
  have hcov := certGammas_covers (nn + 2) cert [] hd
  refine automsOk_mono (fun γ hγ => ?_) cert
    (automsOk_and cert hcov hv)
  refine containsGamma_of_mem (List.mem_filter.mpr
    ⟨mem_of_containsGamma hγ.1, hγ.2⟩)

/-! # The walk never emits a bare `.autom` at a node position -/

private theorem certifyNodeAutom_ne_autom (ctx : Ctx) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat) (active numcells : Nat)
      (bcodes : List Nat) (st : AutState) (o' : Nat) (γ : Array Nat),
      (certifyNodeAutom ctx tcLevel fuel level lab ptn active numcells
        bcodes st).1 ≠ .autom o' γ
  | 0, _, _, _, _, _, _, _, _, _ => fun h => nomatch h
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st, o', γ => by
    rw [certifyNodeAutom.eq_def]
    dsimp only
    split
    · exact fun h => nomatch h
    · match bcodes with
      | [] => exact fun h => nomatch h
      | bc :: brest =>
        dsimp only
        split
        · exact fun h => nomatch h
        · exact fun h => nomatch h
        · split
          · exact fun h => nomatch h
          · dsimp only
            exact fun h => nomatch h

/-- The child-sweep equation for a non-`.autom` head. -/
private theorem checkChildren_cons_of_ne_autom {ctx : Ctx}
    (tcLevel : Nat) (brows : List Nat) (vgens : List (Array Nat))
    (fuel level : Nat) (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (brest : List Nat) {c : CertNode}
    (hne : ∀ (o' : Nat) (γ : Array Nat), c ≠ .autom o' γ)
    (rest : List CertNode) (o : Nat) :
    checkChildren ctx tcLevel brows vgens fuel level rsLab rsPtn tc
        numcells brest (c :: rest) o =
      match checkNode ctx tcLevel brows vgens fuel (level + 1)
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
        (numcells + 1) c brest with
      | none => none
      | some a =>
        match checkChildren ctx tcLevel brows vgens fuel level rsLab
          rsPtn tc numcells brest rest (o + 1) with
        | none => none
        | some a' => some (a || a') := by
  rcases c with _ | _ | ⟨o2, γ2⟩ | ch
  · rw [checkChildren] <;> first | rfl | (intro o' γ h; exact nomatch h)
  · rw [checkChildren] <;> first | rfl | (intro o' γ h; exact nomatch h)
  · exact absurd rfl (hne o2 γ2)
  · rw [checkChildren] <;> first | rfl | (intro o' γ h; exact nomatch h)

/-! # The replay sweep

The checker accepts the children a dominated walk emits. The fold
body is abstract: `hstep` characterizes one step of the walk's child
fold (an `.autom` record that passed the emission checks, or a
recursive walk result), and `hnode` is the node-level replay theorem
at the children's fuel, supplied by the induction. -/

private theorem sweep_replays {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) {vgens : List (Array Nat)}
    (hv : ∀ γ ∈ vgens, checkAutom ctx.g γ ctx.n = true)
    (tcLevel : Nat) (brows : List Nat) (fuel level : Nat)
    (rsLab rsPtn : Array Nat) (tc lenT numcells : Nat)
    (brest : List Nat)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (hlf : level + 1 + fuel ≤ n + 1) (hlfl : n ≤ level + fuel)
    (hbcc : level + 1 ≤
      bcount (rsPtn.set! tc (level + 1)) (level + 1) n)
    (hkeyle : ∀ i, i < lenT →
      keyLe (childKey ctx tcLevel fuel level rsLab rsPtn tc numcells
        i) ⟨brest, brows⟩)
    (hnode : ∀ (lab' ptn' : Array Nat) (active' numcells' : Nat)
      (st' : AutState),
      st'.budget = none → st'.exhausted = false →
      NodeOk n (level + 1) lab' ptn' active' →
      level + 1 + fuel ≤ n + 1 → n + 1 ≤ level + 1 + fuel →
      level + 1 ≤ bcount ptn' (level + 1) n →
      keyLe (specNode ctx tcLevel fuel (level + 1) lab' ptn' active'
        numcells') ⟨brest, brows⟩ →
      AutomsOk (fun γ => containsGamma vgens γ = true)
        (certifyNodeAutom ctx tcLevel fuel (level + 1) lab' ptn'
          active' numcells' brest st').1 →
      ∃ a, checkNode ctx tcLevel brows vgens fuel (level + 1) lab'
          ptn' active' numcells'
          (certifyNodeAutom ctx tcLevel fuel (level + 1) lab' ptn'
            active' numcells' brest st').1 brest = some a ∧
        (a = false →
          keyCmp (specNode ctx tcLevel fuel (level + 1) lab' ptn'
            active' numcells') ⟨brest, brows⟩ = .lt))
    (f : List CertNode × AutState ×
        Option (Nat × Array (Array Nat × Array Nat)) → Nat →
      List CertNode × AutState ×
        Option (Nat × Array (Array Nat × Array Nat)))
    (hstep : ∀ (kids : List CertNode) (stx : AutState)
      (cch : Option (Nat × Array (Array Nat × Array Nat))) (o : Nat),
      o < lenT → stx.budget = none → stx.exhausted = false →
      ∃ c st' cch', f (kids, stx, cch) o = (c :: kids, st', cch') ∧
        st'.budget = none ∧ st'.exhausted = false ∧
        ((∃ o' γ, c = .autom o' γ ∧ o' < o ∧
          checkCellsPerm
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1
            ((breakout rsLab rsPtn (level + 1) tc
              rsLab[tc + o]!).1.map fun w => γ[w]!)
            (level + 1) ctx.n = true) ∨
         (∃ stz, stz.budget = none ∧ stz.exhausted = false ∧
           c = (certifyNodeAutom ctx tcLevel fuel (level + 1)
             (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
             (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
             (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
             (numcells + 1) brest stz).1))) :
    ∀ (len o : Nat) (kids0 : List CertNode) (stx : AutState)
      (cch0 : Option (Nat × Array (Array Nat × Array Nat)))
      (kidsF : List CertNode) (stF : AutState)
      (cchF : Option (Nat × Array (Array Nat × Array Nat))),
      o + len ≤ lenT → stx.budget = none → stx.exhausted = false →
      (List.range' o len).foldl f (kids0, stx, cch0) =
        (kidsF, stF, cchF) →
      ∃ kidsNew, kidsF = kidsNew ++ kids0 ∧
        kidsNew.length = len ∧
        (AutomsOkList (fun γ => containsGamma vgens γ = true)
          kidsNew.reverse →
        ∃ a, checkChildren ctx tcLevel brows vgens fuel level rsLab
            rsPtn tc numcells brest kidsNew.reverse o = some a ∧
          ((a = false ∧ ∀ i, i < o →
            keyCmp (childKey ctx tcLevel fuel level rsLab rsPtn tc
              numcells i) ⟨brest, brows⟩ = .lt) →
            ∀ i, o ≤ i → i < o + len →
              keyCmp (childKey ctx tcLevel fuel level rsLab rsPtn tc
                numcells i) ⟨brest, brows⟩ = .lt))
  | 0, o, kids0, stx, cch0, kidsF, stF, cchF, _, _, _, hfold => by
    rw [List.range'_zero, List.foldl_nil] at hfold
    injection hfold with h1 h2
    refine ⟨[], by rw [← h1]; rfl, rfl, fun _ => ?_⟩
    exact ⟨false, rfl, fun _ i hi1 hi2 => by omega⟩
  | len + 1, o, kids0, stx, cch0, kidsF, stF, cchF, hlen, hbz, hez,
      hfold => by
    obtain ⟨c, st', cch', hf, hb', he', hdis⟩ :=
      hstep kids0 stx cch0 o (by omega) hbz hez
    rw [List.range'_succ, List.foldl_cons, hf] at hfold
    obtain ⟨kidsNew', hkF, hkL, hrest⟩ := sweep_replays hn hgsz hv
      tcLevel brows fuel level rsLab rsPtn tc lenT numcells brest hs
      hok hsp hend hvals hic hrange hlf hlfl hbcc hkeyle hnode f
      hstep len (o + 1) (c :: kids0) st' cch' kidsF stF cchF
      (by omega) hb' he' hfold
    refine ⟨kidsNew' ++ [c], by rw [hkF, List.append_assoc]; rfl,
      by simp [hkL], ?_⟩
    intro hgl
    rw [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append] at hgl ⊢
    have hgl1 : AutomsOk (fun γ => containsGamma vgens γ = true) c :=
      hgl.1
    have hgl2 := hgl.2
    obtain ⟨a', hcc', hstrict'⟩ := hrest hgl2
    rcases hdis with ⟨o', γ, rfl, ho'o, hcp⟩ | ⟨stz, hbz2, hez2, hc⟩
    · -- automorphism record
      have hcont : containsGamma vgens γ = true := hgl1
      rw [checkChildren]
      have hcond : (decide (o' < o) && containsGamma vgens γ &&
          checkCellsPerm
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
            (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o']!).1
            ((breakout rsLab rsPtn (level + 1) tc
              rsLab[tc + o]!).1.map fun w => γ[w]!)
            (level + 1) ctx.n) = true := by
        rw [hcont, hcp]
        simp [ho'o]
      rw [hcond]
      rw [hcc']
      refine ⟨false || a', rfl, fun hfa => ?_⟩
      simp only [Bool.false_or] at hfa
      -- the pruned child's key repeats the earlier sibling's
      have hAut := hv γ (containsGamma_mem hcont)
      rw [hn] at hAut hcp
      obtain ⟨σ, hσeq, hσrows⟩ := checkAutom_sound hgsz hAut
      have hoLen : o < lenT := by omega
      have ho'Len : o' < lenT := by omega
      have hokc := childNodeOk hs hok hsp hend hvals hic hrange hoLen
      have hokc' := childNodeOk hs hok hsp hend hvals hic hrange
        ho'Len
      have hmapeq : ((breakout rsLab rsPtn (level + 1) tc
          rsLab[tc + o]!).1.map fun w => γ[w]!) =
          (breakout rsLab rsPtn (level + 1) tc
            rsLab[tc + o]!).1.map σ.toFun :=
        map_congr_of_labOk hokc.labOk (fun w hw => (hσeq w hw).symm)
      rw [hmapeq] at hcp
      have hcpc := checkCellsPerm_sound
        (ptn := (breakout rsLab rsPtn (level + 1) tc
          rsLab[tc + o]!).2.1)
        (lab₁ := (breakout rsLab rsPtn (level + 1) tc
          rsLab[tc + o']!).1)
        (lab₂' := (breakout rsLab rsPtn (level + 1) tc
          rsLab[tc + o]!).1.map σ.toFun) (level := level + 1)
        hokc.ptnSize hokc'.labSize
        (by rw [Array.size_map]; exact hokc.labSize)
        hokc.ptnEnd hcp
      have hkeyeq : childKey ctx tcLevel fuel level rsLab rsPtn tc
          numcells o =
          childKey ctx tcLevel fuel level rsLab rsPtn tc numcells
            o' :=
        specNode_autom hn hσrows tcLevel fuel (level + 1)
          (lab₁ := (breakout rsLab rsPtn (level + 1) tc
            rsLab[tc + o']!).1)
          (lab₂ := (breakout rsLab rsPtn (level + 1) tc
            rsLab[tc + o]!).1)
          (ptn := (breakout rsLab rsPtn (level + 1) tc
            rsLab[tc + o]!).2.1)
          (active := (breakout rsLab rsPtn (level + 1) tc
            rsLab[tc + o]!).2.2)
          (numcells := numcells + 1) hcpc hokc'.labSize hokc.labSize
          hokc'.labOk hokc.labOk hokc.ptnSize hokc.act hokc.ptnEnd
          hokc.starts hokc.vals (by omega)
      intro i hi1 hi2
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hgt
      · rw [hkeyeq]
        exact hfa.2 o' ho'o
      · refine hstrict' ⟨hfa.1, fun j hj => ?_⟩ i hgt (by omega)
        rcases Nat.lt_or_ge j o with hj2 | hj2
        · exact hfa.2 j hj2
        · have hjo : j = o := by omega
          rw [hjo, hkeyeq]
          exact hfa.2 o' ho'o
    · -- recursively walked child
      have hoLen : o < lenT := by omega
      have hokc := childNodeOk hs hok hsp hend hvals hic hrange hoLen
      have hchild := hnode
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
        (numcells + 1) stz hbz2 hez2 hokc hlf (by omega)
        (by exact hbcc) (hkeyle o hoLen) (by rw [← hc]; exact hgl1)
      obtain ⟨a0, hcn, hstr0⟩ := hchild
      rw [← hc] at hcn
      have hne : ∀ (o2 : Nat) (γ2 : Array Nat),
          c ≠ CertNode.autom o2 γ2 := by
        intro o2 γ2 h
        rw [hc] at h
        exact certifyNodeAutom_ne_autom ctx tcLevel fuel (level + 1)
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
          (numcells + 1) brest stz o2 γ2 h
      rw [checkChildren_cons_of_ne_autom tcLevel brows vgens fuel
        level rsLab rsPtn tc numcells brest hne]
      rw [hcn]
      dsimp only
      rw [hcc']
      refine ⟨a0 || a', rfl, fun hfa => ?_⟩
      obtain ⟨ha0, ha'⟩ := Bool.or_eq_false_iff.mp hfa.1
      intro i hi1 hi2
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hgt
      · exact hstr0 ha0
      · refine hstrict' ⟨ha', fun j hj => ?_⟩ i hgt (by omega)
        rcases Nat.lt_or_ge j o with hj2 | hj2
        · exact hfa.2 j hj2
        · have hjo : j = o := by omega
          rw [hjo]
          exact hstr0 ha0

/-! # The node-level replay -/

/-- A dominated walk's certificate replays: `checkNode` accepts it,
and a `some false` verdict forces the subtree strictly below the
claimed suffix. -/
theorem certifyNode_replays {ctx : Ctx} (hn : ctx.n = n)
    (hgsz : ctx.g.size = n) {vgens : List (Array Nat)}
    (hv : ∀ γ ∈ vgens, checkAutom ctx.g γ ctx.n = true)
    (tcLevel : Nat) (brows : List Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat) (active numcells : Nat)
      (bcodes : List Nat) (st : AutState),
      st.budget = none → st.exhausted = false →
      NodeOk n level lab ptn active →
      level + fuel ≤ n + 1 → n + 1 ≤ level + fuel →
      level ≤ bcount ptn level n →
      keyLe (specNode ctx tcLevel fuel level lab ptn active numcells)
        ⟨bcodes, brows⟩ →
      AutomsOk (fun γ => containsGamma vgens γ = true)
        (certifyNodeAutom ctx tcLevel fuel level lab ptn active
          numcells bcodes st).1 →
      ∃ a, checkNode ctx tcLevel brows vgens fuel level lab ptn
          active numcells
          (certifyNodeAutom ctx tcLevel fuel level lab ptn active
            numcells bcodes st).1 bcodes = some a ∧
        (a = false →
          keyCmp (specNode ctx tcLevel fuel level lab ptn active
            numcells) ⟨bcodes, brows⟩ = .lt)
  | 0, level, lab, ptn, active, numcells, bcodes, st, _, _, _, _,
      hlfl, hbc, _, _ => by
    exfalso
    have := bcount_le ptn level n
    omega
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st, hb, he,
      hok, hlf, hlfl, hbc, hdom, hgs => by
    rcases bcodes with _ | ⟨bc, brest⟩
    · -- an empty claimed suffix contradicts domination
      exfalso
      obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel fuel
        level lab ptn active numcells
      have hk : specNode ctx tcLevel (fuel + 1) level lab ptn active
          numcells =
          ⟨(refine ctx level lab ptn active numcells).longcode ::
            rest,
          (specNode ctx tcLevel (fuel + 1) level lab ptn active
            numcells).rows⟩ := by
        rw [← hrest]
      rw [keyLe, hk, keyCmp_codes_nil_gt] at hdom
      exact hdom rfl
    -- name the walk result
    rcases hcw : certifyNodeAutom ctx tcLevel (fuel + 1) level lab
      ptn active numcells (bc :: brest) st with ⟨cert, stw⟩
    rw [hcw] at hgs
    dsimp only at hgs
    -- invert the walk equation
    rw [certifyNodeAutom.eq_def] at hcw
    dsimp only at hcw
    rw [charge_none' hb,
      ite_eq_right (by rw [he]; exact Bool.false_ne_true)] at hcw
    have hstR := refine_stOk (ctx := ctx) hn (level := level)
      (numcells := numcells) hok.labSize hok.labOk hok.ptnSize
      hok.act hok.ptnEnd
    have hRvals : ∀ q : Nat,
        (refine ctx level lab ptn active numcells).ptn[q]! ≤ level ∨
          (refine ctx level lab ptn active numcells).ptn[q]! =
            n + 2 := by
      intro q
      rcases ptn_refine_vals ctx level lab ptn active numcells q
        with he' | he'
      · rw [he']
        exact hok.vals q
      · rw [he']
        exact Or.inl (Nat.le_refl level)
    have hRinv := refine_refInv (ctx := ctx) (level := level)
      (lab := lab) (ptn := ptn) (active := active)
      (numcells := numcells) (by rw [hok.ptnSize]; omega)
      (by rw [hok.labSize, hok.ptnSize]) hok.ptnEnd
    obtain ⟨rest, hrest⟩ := specNode_codes_head ctx tcLevel fuel
      level lab ptn active numcells
    have hkspec : specNode ctx tcLevel (fuel + 1) level lab ptn
        active numcells =
        ⟨(refine ctx level lab ptn active numcells).longcode :: rest,
        (specNode ctx tcLevel (fuel + 1) level lab ptn active
          numcells).rows⟩ := by
      rw [← hrest]
    split at hcw
    · -- compare = .lt: the walk emitted a code prune
      next heq =>
      injection hcw with h1 h2
      subst h1
      have hlt := Nat.compare_eq_lt.mp heq
      refine ⟨false, ?_, fun _ => ?_⟩
      · rw [checkNode]
        rw [ite_eq_left heq]
      · rw [hkspec, keyCmp_cons_lt hlt]
    · -- compare = .gt contradicts domination
      next heq =>
      exfalso
      have hgt := Nat.compare_eq_gt.mp heq
      rw [keyLe, hkspec, keyCmp_cons_gt hgt] at hdom
      exact hdom rfl
    · -- compare = .eq
      next heq =>
      have hlc : (refine ctx level lab ptn active numcells).longcode
          = bc := Nat.compare_eq_eq.mp heq
      split at hcw
      · -- discrete: the walk emitted a leaf
        next hdisc =>
        injection hcw with h1 h2
        subst h1
        have hleafspec : specNode ctx tcLevel (fuel + 1) level lab
            ptn active numcells =
            ⟨[(refine ctx level lab ptn active numcells).longcode,
              codeSentinel],
            leafRows ctx (refine ctx level lab ptn active
              numcells).lab⟩ := by
          rw [specNode, ite_eq_left hdisc]
        have hdom' := hdom
        rw [keyLe, hleafspec] at hdom'
        rcases hkc : keyCmp
            ⟨[(refine ctx level lab ptn active numcells).longcode,
              codeSentinel],
            leafRows ctx (refine ctx level lab ptn active
              numcells).lab⟩ ⟨bc :: brest, brows⟩ with _ | _ | _
        · -- keyCmp = .lt: replay accepts, subtree strictly below
          refine ⟨false, ?_, fun _ => ?_⟩
          · rw [checkNode]
            rw [heq]
            dsimp only
            rw [ite_eq_left hdisc, hkc]
          · rw [hleafspec]
            exact hkc
        · -- keyCmp = .eq: replay accepts and achieves
          refine ⟨true, ?_, fun hx => Bool.noConfusion hx⟩
          rw [checkNode]
          rw [heq]
          dsimp only
          rw [ite_eq_left hdisc, hkc]
        · exact absurd hkc hdom'
      · -- non-discrete: the walk emitted a node
        next hdisc =>
        obtain ⟨p, hptc, hp12, hpb, hicp, hce⟩ := targetcell_facts
          hn (tcLevel := tcLevel)
          (refine ctx level lab ptn active numcells).lab
          hstR.ptnSize hstR.ptnEnd (by
            rcases hd2 : discreteAt (refine ctx level lab ptn active
                numcells).ptn level ctx.n with _ | _
            · rfl
            · exact absurd hd2 hdisc)
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
              tcLevel + 1 = p.2 + 1 - p.1
          rw [hptc, hce]
          omega
        obtain ⟨m, hm⟩ : ∃ m, p.2 + 1 - p.1 = m + 1 :=
          ⟨p.2 - p.1, by omega⟩
        -- the structural spec equation at this node
        have hspec : specNode ctx tcLevel (fuel + 1) level lab ptn
            active numcells =
            ⟨(refine ctx level lab ptn active numcells).longcode ::
              (keysMax (childKey ctx tcLevel fuel level
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn p.1
                (refine ctx level lab ptn active numcells).numcells
                0)
                ((List.range m).map fun j =>
                  childKey ctx tcLevel fuel level
                    (refine ctx level lab ptn active numcells).lab
                    (refine ctx level lab ptn active numcells).ptn
                    p.1
                    (refine ctx level lab ptn active
                      numcells).numcells (j + 1))).codes,
            (keysMax (childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells 0)
              ((List.range m).map fun j =>
                childKey ctx tcLevel fuel level
                  (refine ctx level lab ptn active numcells).lab
                  (refine ctx level lab ptn active numcells).ptn p.1
                  (refine ctx level lab ptn active
                    numcells).numcells (j + 1))).rows⟩ := by
          rw [specNode]
          simp only [hdisc, Bool.false_eq_true, ite_false]
          rw [hM1, hM22, hm, List.range_succ_eq_map, List.map_cons,
            List.map_map]
          rfl
        -- domination of every child key
        have hkM : keyLe (keysMax (childKey ctx tcLevel fuel level
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn p.1
            (refine ctx level lab ptn active numcells).numcells 0)
            ((List.range m).map fun j =>
              childKey ctx tcLevel fuel level
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn p.1
                (refine ctx level lab ptn active numcells).numcells
                (j + 1))) ⟨brest, brows⟩ := by
          have hd2 := hdom
          rw [hspec, hlc] at hd2
          have hd4 := keyLe_cons_tail hd2
          rw [key_eta] at hd4
          exact hd4
        have hkeyle : ∀ i, i < p.2 + 1 - p.1 →
            keyLe (childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells i)
              ⟨brest, brows⟩ := by
          intro i hi
          refine keyLe_trans (keyLe_iff.mpr (keysMax_ge _ _ _ ?_))
            hkM
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · exact Or.inl rfl
          · refine Or.inr (List.mem_map.mpr
              ⟨i - 1, List.mem_range.mpr (by omega), ?_⟩)
            rw [show i - 1 + 1 = i from by omega]
        -- the child bcount seed
        have hbcChild : level + 1 ≤
            bcount ((refine ctx level lab ptn active
              numcells).ptn.set! p.1 (level + 1)) (level + 1) n := by
          have h1 : bcount ptn level n ≤
              bcount (refine ctx level lab ptn active numcells).ptn
                level n :=
            bcount_mono hRinv.grow
          have h2 := bcount_breakout (n := n)
            (ptn := (refine ctx level lab ptn active numcells).ptn)
            (level := level) (tc := p.1) (nn := n) hRvals (by omega)
            (hicp.2.2.1 p.1 (Nat.le_refl p.1) (by omega))
            (by omega) (by rw [hstR.ptnSize]; omega)
          omega
        -- destructure the child fold
        rw [hM1, hM22] at hcw
        rcases hfold : (List.range (p.2 + 1 - p.1)).foldl _
          ([], st, none) with ⟨children, stx, cachex⟩
        rw [hfold] at hcw
        dsimp only at hcw
        injection hcw with h1 h2
        subst h1
        rw [AutomsOk] at hgs
        -- run the sweep
        rw [List.range_eq_range'] at hfold
        obtain ⟨kidsNew, hkF, hkL, hccl⟩ := sweep_replays hn hgsz hv
          tcLevel brows fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn p.1
          (p.2 + 1 - p.1)
          (refine ctx level lab ptn active numcells).numcells brest
          hstR.labSize hstR.labOk hstR.ptnSize hstR.ptnEnd hRvals
          hicp (by omega) (by omega) (by omega) hbcChild hkeyle
          (fun lab' ptn' active' numcells' st' hb' he' hok' hlf'
            hlfl' hbc' hdom' hgs' =>
            certifyNode_replays hn hgsz hv tcLevel brows fuel
              (level + 1) lab' ptn' active' numcells' brest st' hb'
              he' hok' hlf' hlfl' hbc' hdom' hgs') _
          (by
            intro kids stx2 cch o ho hbz hez
            split
            · next o' γ hw =>
              split
              · next hcc =>
                rw [childCellsOk] at hcc
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                  at hcc
                exact ⟨.autom o' γ, stx2, _, rfl, hbz, hez,
                  Or.inl ⟨o', γ, rfl, hcc.1, hcc.2⟩⟩
              · refine ⟨_, _, _, rfl, ?_, ?_, Or.inr ⟨stx2, hbz,
                  hez, rfl⟩⟩
                · exact (certifyNodeAutom_nobudget' ctx tcLevel fuel
                    _ _ _ _ _ _ _ hbz hez).1
                · exact (certifyNodeAutom_nobudget' ctx tcLevel fuel
                    _ _ _ _ _ _ _ hbz hez).2
            · refine ⟨_, _, _, rfl, ?_, ?_, Or.inr ⟨stx2, hbz, hez,
                rfl⟩⟩
              · exact (certifyNodeAutom_nobudget' ctx tcLevel fuel
                  _ _ _ _ _ _ _ hbz hez).1
              · exact (certifyNodeAutom_nobudget' ctx tcLevel fuel
                  _ _ _ _ _ _ _ hbz hez).2)
          (p.2 + 1 - p.1) 0 [] st none children stx cachex
          (by omega) hb he hfold
        -- assemble the checker verdict
        rw [List.append_nil] at hkF
        subst hkF
        obtain ⟨a, hcc, hstrict⟩ := hccl hgs
        refine ⟨a, ?_, fun hfa => ?_⟩
        · rw [checkNode]
          dsimp only
          rw [heq]
          dsimp only
          rw [ite_eq_right hdisc]
          rw [checkNode_children_eq, hM1]
          rw [ite_eq_left (by
            rw [List.length_reverse, hkL, hM22])]
          rw [hcc]
          simp only [Bool.false_or]
        · have hall := hstrict ⟨hfa, fun i hi => absurd hi
            (by omega)⟩
          rw [hspec, hlc]
          have hlt : keyCmp (keysMax (childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells 0)
              ((List.range m).map fun j =>
                childKey ctx tcLevel fuel level
                  (refine ctx level lab ptn active numcells).lab
                  (refine ctx level lab ptn active numcells).ptn p.1
                  (refine ctx level lab ptn active
                    numcells).numcells (j + 1))) ⟨brest, brows⟩ =
              .lt := by
            refine keysMax_lt (hall 0 (Nat.le_refl 0) (by omega))
              fun y hy => ?_
            rcases List.mem_map.mp hy with ⟨j, hj, rfl⟩
            have hjm := List.mem_range.mp hj
            exact hall (j + 1) (by omega) (by omega)
          rw [show keyCmp
              ⟨bc :: (keysMax (childKey ctx tcLevel fuel level
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn p.1
                (refine ctx level lab ptn active numcells).numcells
                0)
                ((List.range m).map fun j =>
                  childKey ctx tcLevel fuel level
                    (refine ctx level lab ptn active numcells).lab
                    (refine ctx level lab ptn active numcells).ptn
                    p.1
                    (refine ctx level lab ptn active
                      numcells).numcells (j + 1))).codes,
              (keysMax (childKey ctx tcLevel fuel level
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn p.1
                (refine ctx level lab ptn active numcells).numcells
                0)
                ((List.range m).map fun j =>
                  childKey ctx tcLevel fuel level
                    (refine ctx level lab ptn active numcells).lab
                    (refine ctx level lab ptn active numcells).ptn
                    p.1
                    (refine ctx level lab ptn active
                      numcells).numcells (j + 1))).rows⟩
              ⟨bc :: brest, brows⟩ =
            keyCmp (keysMax (childKey ctx tcLevel fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn p.1
              (refine ctx level lab ptn active numcells).numcells 0)
              ((List.range m).map fun j =>
                childKey ctx tcLevel fuel level
                  (refine ctx level lab ptn active numcells).lab
                  (refine ctx level lab ptn active numcells).ptn p.1
                  (refine ctx level lab ptn active
                    numcells).numcells (j + 1))) ⟨brest, brows⟩ from
            by rw [keyCmp_cons_eq bc, key_eta]]
          exact hlt

/-! # The replay at the root -/

/-- The traced key of the candidate producer, as `produceCand`
claims it. -/
@[expose] def tracedKey (G : Colored n k) : Key :=
  ⟨(runColoredTraced G).bestCodes ++ [codeSentinel],
    leafRows { n := n, g := rowsOf G }
      (runColoredTraced G).result.canonlab⟩

/-- The produced certificate replays: under domination (the traced
key is the spec key) and store validity (every record's generator is
a checked automorphism), `checkKey` accepts the produced pair. -/
theorem produceCand_checkKey {G : Colored n k} {cert : CertNode}
    {B : Key} (hp : produceCand G none = some (cert, B))
    (hval : AutomsOk (fun γ => checkAutom (rowsOf G) γ n = true)
      cert)
    (hdom : canonSpecKey G = B) :
    checkKey G cert B = true := by
  have hB := produceCand_key hp
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- domination rules out the empty graph
    exfalso
    subst hn0
    rw [canonSpecKey, canonSpec, ite_eq_left (by rfl)] at hdom
    have hc := congrArg Key.codes (hdom.trans hB)
    dsimp only at hc
    exact absurd (List.append_eq_nil_iff.mp hc.symm).2 (by simp)
  -- name the producer's state and extract the walk equation
  subst hB
  rw [produceCand] at hp
  dsimp only at hp
  rw [ite_eq_right (by simp [Option.any])] at hp
  split at hp
  · cases hp
  · next hex3 =>
    injection hp with hp'
    injection hp' with hcert hBeq
    -- the producer's threaded state has no budget and never exhausts
    have hst1 : ((runColoredTraced G).autos.foldl
        (fun st γ => st.admit { n := n, g := rowsOf G } γ)
        (AutState.init n none)).budget = none ∧
        ((runColoredTraced G).autos.foldl
        (fun st γ => st.admit { n := n, g := rowsOf G } γ)
        (AutState.init n none)).exhausted = false := by
      rw [← Array.foldl_toList]
      refine foldl_pres' _
        (fun (st : AutState) => st.budget = none ∧
          st.exhausted = false) _ _ ⟨rfl, rfl⟩ ?_
      intro st γ hst
      exact ⟨(admit_budget' _ st γ).trans hst.1,
        (admit_exhausted' _ st γ).trans hst.2⟩
    have hok := initial_nodeOk G hn0
    have hbc1 : 1 ≤ bcount
        (initPtn n (n + 2) (initialPartition G).2) 1 n := by
      refine bcount_pos_of_boundary (q := n - 1) (by omega) ?_
      have hend := hok.ptnEnd
      rw [hok.ptnSize] at hend
      exact hend
    have hspecroot : canonSpecKey G =
        specNode { n := n, g := rowsOf G } 100 n 1
          (initialPartition G).1
          (initPtn n (n + 2) (initialPartition G).2)
          (initActive (initialPartition G).2)
          (initialPartition G).2.length := by
      rw [canonSpecKey, canonSpec, ite_eq_right (by simp; omega)]
    have hdom' : keyLe (specNode { n := n, g := rowsOf G } 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length)
        ⟨(runColoredTraced G).bestCodes ++ [codeSentinel],
          leafRows { n := n, g := rowsOf G }
            (runColoredTraced G).result.canonlab⟩ :=
      keyLe_of_eq (hspecroot.symm.trans hdom)
    have hdepth : CertNode.depth cert ≤ n + 2 := by
      rw [← hcert]
      exact Nat.le_trans
        (certifyNodeAutom_depth _ _ _ _ _ _ _ _ _ _) (by omega)
    have hgsC : AutomsOk (fun γ =>
        containsGamma (validGammas (rowsOf G) n cert) γ = true)
        cert := automsOk_validGammas hdepth hval
    obtain ⟨a, hcheck, hstrict⟩ := certifyNode_replays
      (n := n) (ctx := { n := n, g := rowsOf G }) rfl
      (size_rowsOf G)
      (fun γ hγ => validGammas_sound hγ) 100
      (leafRows { n := n, g := rowsOf G }
        (runColoredTraced G).result.canonlab) n 1
      (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length
      ((runColoredTraced G).bestCodes ++ [codeSentinel])
      { ((runColoredTraced G).autos.foldl
          (fun st γ => st.admit { n := n, g := rowsOf G } γ)
          (AutState.init n none)) with
        refLeaf := some (runColoredTraced G).result.canonlab }
      hst1.1 hst1.2 hok (by omega) (by omega) hbc1 hdom'
      (by rw [hcert]; exact hgsC)
    have ha : a = true := by
      rcases Bool.eq_false_or_eq_true a with hta | hfa
      · exact hta
      · exfalso
        have hlt := hstrict hfa
        rw [← hspecroot, hdom, keyCmp_self] at hlt
        exact Ordering.noConfusion hlt
    rw [checkKey, ite_eq_right (by simp; omega)]
    refine decide_eq_true ?_
    rw [hcert] at hcheck
    exact ha ▸ hcheck

/-- The two remaining layer-three clauses close `certifyCanon?`
totality: domination (the traced key is the spec key) and store
validity (every produced record's generator is a checked
automorphism). -/
theorem certifyCanon?_isSome_of_dominated (G : Colored n k)
    (hdom : canonSpecKey G = tracedKey G)
    (hval : ∀ cert B, produceCand G none = some (cert, B) →
      AutomsOk (fun γ => checkAutom (rowsOf G) γ n = true) cert) :
    (certifyCanon? G).isSome :=
  certifyCanon?_isSome_of_checkKey G fun cert B hp =>
    produceCand_checkKey hp (hval cert B hp)
      (by rw [hdom, tracedKey, produceCand_key hp])

end Hex.GraphIso.Nauty
