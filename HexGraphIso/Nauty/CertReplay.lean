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

end Hex.GraphIso.Nauty
