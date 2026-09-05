/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Incumbent
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Orbits

public section

/-!
The orbit closure is complete (SPEC § Verified search refinement).

A loop's fold runs over the children it visited, while a node's key
is the maximum over the whole subtree. The two agree once every child
is dominated by the maximum over the visited ones. Supplying that
domination for the children `firstChildLoop` drops is the loop step's
real content.

The justification of a dropped child is `childKey_of_orbPruned`, whose
hypothesis is the model's `orbPruned`, phrased through the executable
forward closure `orbitClose` at fuel `nn`. The transcription's test is
a single pointer read, and `orbConn_of_ptr` turns that into
`WordConn gens v orbits[v]!`. Between the two sits a gap `Invariant/Orbits`
deliberately left open: it proved the closure *sound*, which is all
store validity needed, and recorded that completeness "is not needed
for soundness, only if B2 wants to show the model prunes at least as
much as the transcription". The domination step is exactly that
direction, so this file closes the gap.

The word a `WordConn` supplies can be longer than `nn`, so fuel `nn`
is not justified by running the word. It is justified by saturation:
one round applies every generator to every member of the round's
*starting* set, the rounds form an increasing chain of subsets of
`[0, nn)`, and a chain that is strict at every step would exceed the
bound. So some round repeats, a repeated round is a fixed point, and a
fixed point absorbs the whole word however long it is.
-/

namespace Hex.GraphIso.Nauty

/-! # One round -/

/-- A fold whose steps only add members, and one of whose steps adds a
particular member regardless of the accumulator, has that member. -/
private theorem foldl_mem_covers {nn : Nat} {β : Type} {f : VSet nn → β → VSet nn}
    {x : Nat} {b₀ : β}
    (hmono : ∀ a b y, a.mem y = true → (f a b).mem y = true)
    (hadd : ∀ a, (f a b₀).mem x = true) :
    ∀ (l : List β) (init : VSet nn), b₀ ∈ l →
      (l.foldl f init).mem x = true
  | [], _, hb => absurd hb List.not_mem_nil
  | b :: l, init, hb => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact foldl_invariant (P := fun a => a.mem x = true) l _
        (hadd init) (fun a b _ ha => hmono a b x ha)
    · exact foldl_mem_covers hmono hadd l _ hb'

/-- The inner round over one generator only adds members. -/
private theorem inner_grows {nn : Nat} {s : VSet nn} {γ : Array Nat}
    {a : VSet nn} {y : Nat} (hy : a.mem y = true) :
    ((List.range nn).foldl
      (fun acc w => if s.mem w then acc.insert γ[w]! else acc)
      a).mem y = true := by
  refine foldl_invariant (P := fun acc => acc.mem y = true)
    (List.range nn) a hy ?_
  intro acc' w _ hacc'
  rcases hw : s.mem w with _ | _
  · rw [ite_eq_right (by simp [])]; exact hacc'
  · rw [ite_eq_left (by simp [])]
    exact VSet.mem_insert_mono _ _ hacc'

/-- One closure round only adds members. -/
theorem orbitStepSet_grows {nn : Nat} {gens : List (Array Nat)}
    {s : VSet nn} {x : Nat} (hx : s.mem x = true) :
    (orbitStepSet nn gens s).mem x = true := by
  rw [orbitStepSet]
  refine foldl_invariant (P := fun acc => acc.mem x = true)
    gens s hx ?_
  intro acc γ _ hacc
  exact inner_grows hacc

/-- One closure round applies every generator to every member. -/
theorem orbitStepSet_step {nn : Nat} {gens : List (Array Nat)}
    {s : VSet nn} {u : Nat} {γ : Array Nat} (hγ : γ ∈ gens) (hu : u < nn)
    (hγu : γ[u]! < nn) (hs : s.mem u = true) :
    (orbitStepSet nn gens s).mem γ[u]! = true := by
  rw [orbitStepSet]
  refine foldl_mem_covers (b₀ := γ)
    (fun a b y hy => inner_grows hy) (fun a => ?_) gens s hγ
  refine foldl_mem_covers (b₀ := u)
    (fun a' w y hy => ?_) (fun a' => ?_) (List.range nn) a
    (List.mem_range.mpr hu)
  · rcases hw : s.mem w with _ | _
    · rw [ite_eq_right (by simp [])]; exact hy
    · rw [ite_eq_left (by simp [])]
      exact VSet.mem_insert_mono _ _ hy
  · rw [ite_eq_left (by simp [hs])]
    exact VSet.mem_insert_self _ hγu

/-! # Rounds compose -/

/-- The closure only adds members. -/
theorem orbitClose_grows {nn : Nat} {gens : List (Array Nat)} :
    ∀ (fuel : Nat) (s : VSet nn) (x : Nat), s.mem x = true →
      (orbitClose nn gens fuel s).mem x = true
  | 0, _, _, hx => hx
  | fuel + 1, s, x, hx => by
    rw [orbitClose]
    exact orbitClose_grows fuel _ x (orbitStepSet_grows hx)

/-- Rounds peel off the far end as well as the near end. -/
theorem orbitClose_succ {nn : Nat} {gens : List (Array Nat)} :
    ∀ (fuel : Nat) (s : VSet nn), orbitClose nn gens (fuel + 1) s =
      orbitStepSet nn gens (orbitClose nn gens fuel s)
  | 0, _ => rfl
  | fuel + 1, s => by
    rw [orbitClose, orbitClose_succ fuel (orbitStepSet nn gens s),
      orbitClose]

/-- More fuel never loses a member. -/
theorem orbitClose_mono_fuel {nn : Nat} {gens : List (Array Nat)}
    {f f' : Nat} (hle : f ≤ f') {s : VSet nn} {x : Nat} :
      (orbitClose nn gens f s).mem x = true →
      (orbitClose nn gens f' s).mem x = true := by
  intro hx
  induction f' with
  | zero =>
    have : f = 0 := by omega
    subst this
    exact hx
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq; exact hx
    · rw [orbitClose_succ]
      exact orbitStepSet_grows (ih (Nat.le_of_lt_succ hlt))

/-- A word of length `w.length` is absorbed in `w.length` rounds. -/
theorem orbitClose_applyWord {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ gens) →
      ∀ (s : VSet nn) (u : Nat), s.mem u = true → u < nn →
        (orbitClose nn gens w.length s).mem (applyWord w u) = true
  | [], _, _, _, hs, _ => hs
  | γ :: w, hw, s, u, hs, hu => by
    have hγ : γ ∈ gens := hw γ (List.mem_cons_self ..)
    have hstep : (orbitStepSet nn gens s).mem γ[u]! = true :=
      orbitStepSet_step hγ hu (hb γ hγ u hu) hs
    have := orbitClose_applyWord hb w
      (fun δ hδ => hw δ (List.mem_cons_of_mem _ hδ))
      (orbitStepSet nn gens s) γ[u]! hstep (hb γ hγ u hu)
    rw [show (γ :: w).length = w.length + 1 from rfl, orbitClose]
    exact this

/-! # Saturation

The rounds form a chain of subsets of `[0, nn)`, so the member count
is non-decreasing and capped by `nn`. A round that does not increase
the count is a fixed point, by `VSet.eq_of_subset_of_card_eq`, and a
fixed point stays fixed. -/

/-- A round that does not add to the count is a fixed point. -/
private theorem stepSet_fixed_of_card_eq {nn : Nat}
    {gens : List (Array Nat)} {s : VSet nn}
    (heq : s.card = (orbitStepSet nn gens s).card) :
    orbitStepSet nn gens s = s :=
  (VSet.eq_of_subset_of_card_eq
    (VSet.subset_iff.mpr fun _ hi => orbitStepSet_grows hi) heq).symm

/-- A round over the empty set changes nothing: every guard reads the
starting set, which has no members. -/
private theorem orbitStepSet_empty {nn : Nat} {gens : List (Array Nat)} :
    orbitStepSet nn gens (VSet.empty : VSet nn) = VSet.empty := by
  rw [orbitStepSet]
  refine foldl_invariant (P := fun acc => acc = VSet.empty) gens _ rfl ?_
  intro acc γ _ hacc
  refine foldl_invariant (P := fun acc => acc = VSet.empty) (List.range nn)
    acc hacc ?_
  intro acc' w _ hacc'
  rw [ite_eq_right (by simp)]
  exact hacc'

/-- **The closure saturates within `nn` rounds.** After `nn` rounds a
further round adds nothing. -/
theorem orbitStepSet_orbitClose_nn {nn : Nat} {gens : List (Array Nat)}
    {s : VSet nn} :
    orbitStepSet nn gens (orbitClose nn gens nn s) =
      orbitClose nn gens nn s := by
  -- Either some round below `nn` is a fixed point, or the count
  -- strictly increases at every one of `nn` rounds.
  rcases Decidable.em (∃ i, i < nn ∧
      orbitStepSet nn gens (orbitClose nn gens i s) =
        orbitClose nn gens i s) with hfix | hnofix
  · obtain ⟨i, hi, hf⟩ := hfix
    have hstay : ∀ d, orbitClose nn gens (i + d) s =
        orbitClose nn gens i s := by
      intro d
      induction d with
      | zero => rfl
      | succ p ih =>
        rw [show i + (p + 1) = (i + p) + 1 from rfl,
          orbitClose_succ, ih, hf]
    have hnn : orbitClose nn gens nn s = orbitClose nn gens i s := by
      have := hstay (nn - i)
      rwa [Nat.add_sub_cancel' (Nat.le_of_lt hi)] at this
    rw [hnn, hf]
  · have hne : ∀ i, i < nn →
        orbitStepSet nn gens (orbitClose nn gens i s) ≠
          orbitClose nn gens i s := fun i hi h => hnofix ⟨i, hi, h⟩
    have hgrow : ∀ i, i < nn →
        (orbitClose nn gens i s).card <
          (orbitClose nn gens (i + 1) s).card := by
      intro i hi
      have hle : (orbitClose nn gens i s).card ≤
          (orbitClose nn gens (i + 1) s).card :=
        VSet.card_le_of_subset (VSet.subset_iff.mpr
          fun _ hj => orbitClose_mono_fuel (Nat.le_succ i) hj)
      rcases Nat.lt_or_ge (orbitClose nn gens i s).card
        (orbitClose nn gens (i + 1) s).card with h | h
      · exact h
      · refine absurd ?_ (hne i hi)
        refine stepSet_fixed_of_card_eq ?_
        rw [← orbitClose_succ]
        omega
    have hchain : ∀ i, i ≤ nn →
        s.card + i ≤ (orbitClose nn gens i s).card := by
      intro i
      induction i with
      | zero => intro _; exact Nat.le_of_eq rfl
      | succ p ih =>
        intro hp
        have h1 := ih (Nat.le_of_succ_le hp)
        have h2 := hgrow p (Nat.lt_of_succ_le hp)
        omega
    have hbig := hchain nn (Nat.le_refl nn)
    have hcap := VSet.card_le (orbitClose nn gens nn s)
    have hzero : s.card = 0 := by omega
    have hs0 : s = VSet.empty := VSet.eq_empty_of_card_eq_zero hzero
    rcases Nat.eq_zero_or_pos nn with hnz | hpos
    · subst hnz
      rw [show orbitClose 0 gens 0 s = s from rfl, hs0,
        orbitStepSet_empty]
    · exfalso
      refine hne 0 hpos ?_
      show orbitStepSet nn gens (orbitClose nn gens 0 s) =
        orbitClose nn gens 0 s
      rw [show orbitClose nn gens 0 s = s from rfl, hs0,
        orbitStepSet_empty]

/-! # Completeness

The saturated set is closed under the generators, so it contains
everything a word reaches, however long the word is. That is the
converse of `orbitClose_sound`, and it is what turns the
transcription's pointer test into the model's `orbPruned`. -/

/-- The saturated set absorbs a whole word from any of its members. -/
private theorem orbitClose_nn_word {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {s : VSet nn} :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ gens) →
      ∀ (x : Nat), (orbitClose nn gens nn s).mem x = true →
        (orbitClose nn gens nn s).mem (applyWord w x) = true
  | [], _, _, hx => hx
  | γ :: w, hw, x, hx => by
    have hγ : γ ∈ gens := hw γ (List.mem_cons_self ..)
    have hxn : x < nn := VSet.mem_lt hx
    have hstep : (orbitClose nn gens nn s).mem γ[x]! = true := by
      have := orbitStepSet_step (nn := nn) (gens := gens)
        (s := orbitClose nn gens nn s) hγ hxn (hb γ hγ x hxn) hx
      rwa [orbitStepSet_orbitClose_nn] at this
    exact orbitClose_nn_word hb w
      (fun δ hδ => hw δ (List.mem_cons_of_mem _ hδ)) γ[x]! hstep

/-- **The orbit closure is complete.** Anything a forward word reaches
from `v` is in the closure of `{v}` at fuel `nn`. This is the converse
of `orbitClose_sound`, and the direction the domination step needs. -/
theorem orbitClose_of_wordConn {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {v u : Nat}
    (hv : v < nn) (h : WordConn gens v u) :
    (orbitClose nn gens nn ((VSet.empty : VSet nn).insert v)).mem u = true := by
  obtain ⟨w, hw, happ⟩ := h
  have hv0 : (orbitClose nn gens nn ((VSet.empty : VSet nn).insert v)).mem v =
      true :=
    orbitClose_grows nn _ v (VSet.mem_insert_self _ hv)
  have := orbitClose_nn_word hb w hw v hv0
  rwa [happ] at this

/-- **The transcription's orbit test implies the model's prune.** An
earlier sibling word-connected to this one makes `orbPruned` true, so
`childKey_of_orbPruned` applies and the dropped child repeats a key
the loop already folded in. -/
theorem orbPruned_of_wordConn {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {rsLab : Array Nat}
    {tc o o' : Nat} (ho' : o' < o) (hv : rsLab[tc + o]! < nn)
    (hconn : WordConn gens rsLab[tc + o]! rsLab[tc + o']!) :
    orbPruned nn gens rsLab tc o = true := by
  rw [orbPruned]
  refine List.any_eq_true.mpr ⟨o', List.mem_range.mpr ho', ?_⟩
  exact orbitClose_of_wordConn hb hv hconn

/-! # Word-connected siblings have equal child keys

`childKey_of_orbPruned` concludes with an existential `o' < o`, which
is the shape `orbPruned` hands it and not the shape the loop needs: a
skipped child must be matched with an offset the loop actually
explored, and that offset need not come earlier in the labelling. The
ordering is incidental to the mathematics. `childKey_of_carried` takes
two offsets with no ordering at all, so composing the word first and
applying that is both cleaner and stronger. -/

/-- **Word-connected members of a target cell have equal child keys.**
The word composes to a single checked, cell-stabilizing automorphism
carrying one member onto the other, and `childKey_of_carried`
transports the subtree key. No ordering of the two offsets is
involved. -/
theorem childKey_of_wordConn {ctx : Ctx n}
    (hgsz : ctx.g.size = n)
    {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o o' : Nat}
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (ho' : o' < lenT)
    (hlf : level + 1 + fuel ≤ n + 1)
    (hconn : WordConn gens rsLab[tc + o']! rsLab[tc + o]!) :
    childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' := by
  obtain ⟨w, hw, happ⟩ := hconn
  obtain ⟨hAutC, hstabC, hpointC⟩ :=
    wordPerm_spec hok hsp hs hend hv hstab w hw
  refine childKey_of_carried hgsz hAutC tcLevel fuel level
    hstabC hs hok hsp hend hvals hic hrange ho ho' hlf ?_
  rw [hpointC _ (hok _ (by omega)), happ]

/-- The same, with the connection in the other direction. Forward
words suffice because a checked automorphism's inverse is one of its
own forward powers, which is what `wordConn_symm` records. -/
theorem childKey_of_wordConn' {ctx : Ctx n}
    (hgsz : ctx.g.size = n)
    {gens : List (Array Nat)}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o o' : Nat}
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (ho' : o' < lenT)
    (hlf : level + 1 + fuel ≤ n + 1)
    (hconn : WordConn gens rsLab[tc + o]! rsLab[tc + o']!) :
    childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' := by
  refine childKey_of_wordConn hgsz hv tcLevel fuel level hstab
    hs hok hsp hend hvals hic hrange ho ho' hlf ?_
  have hbnd : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n := fun γ hγ v hv' =>
    checkAutom_bound (hv γ hγ) v hv'
  have hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b := fun γ hγ => checkAutom_inj (hv γ hγ)
  obtain ⟨w, hw, happ⟩ := hconn
  exact wordConn_symm hbnd hinj w (hok _ (by omega)) hw happ

/-! # The loop's orbit test

The transcription does not consult a closure: it reads one entry of
the `orbits` union-find array and compares it with the vertex. These
are the two forms the child loop needs, one for a single pointer read
and one for a chase, which is what reaches an orbit representative
when the pointer's target was itself skipped. Both reduce to
`childKey_of_wordConn'`: the pointer relation is word connectivity by
the store's soundness invariant, and word connectivity equates the
child keys. -/

/-- A pointer chase from a sound array stays in range and stays word
connected. `orbSound_iter` wants an unconditionally reflexive
relation, which `OrbConn` is not, so the chase is done directly. -/
private theorem orbConn_ptrIter {gens : List (Array Nat)}
    {orbits : Array Nat}
    (hsound : OrbSound (OrbConn gens n) orbits n) :
    ∀ (k v : Nat), v < n →
      ptrIter orbits v k < n ∧ WordConn gens v (ptrIter orbits v k)
  | 0, v, hv => ⟨hv, wordConn_refl gens v⟩
  | k + 1, v, hv => by
    obtain ⟨hlt, hconn⟩ := orbConn_ptrIter hsound k v hv
    obtain ⟨hlt', hconn'⟩ := orbConn_of_ptr hsound hlt
    rw [ptrIter]
    exact ⟨hlt', wordConn_trans hconn hconn'⟩

/-- **A skipped child repeats the key of its orbit pointer's target.**
This is the domination fact for one step of the transcription's orbit
test. -/
theorem childKey_of_orbitPtr {ctx : Ctx n}
    (hgsz : ctx.g.size = n)
    {gens : List (Array Nat)} {orbits : Array Nat}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o o' : Nat}
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (ho' : o' < lenT)
    (hlf : level + 1 + fuel ≤ n + 1)
    (hsound : OrbSound (OrbConn gens n) orbits n)
    (hptr : orbits[rsLab[tc + o]!]! = rsLab[tc + o']!) :
    childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' := by
  obtain ⟨-, hconn⟩ := orbConn_of_ptr hsound (hok (tc + o) (by omega))
  rw [hptr] at hconn
  exact childKey_of_wordConn' hgsz hv tcLevel fuel level hstab
    hs hok hsp hend hvals hic hrange ho ho' hlf hconn

/-- **A skipped child repeats the key at the end of its pointer
chase.** The chase is what reaches an orbit representative, which is
the offset the loop actually explored, so this is the form the
domination step applies. -/
theorem childKey_of_ptrIter {ctx : Ctx n}
    (hgsz : ctx.g.size = n)
    {gens : List (Array Nat)} {orbits : Array Nat}
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ = true)
    (tcLevel fuel level : Nat) {rsLab rsPtn : Array Nat}
    {tc lenT numcells o o' k : Nat}
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = n) (hok : LabOk rsLab n)
    (hsp : rsPtn.size = n) (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = n + 2)
    (hic : IsCell rsPtn level tc lenT) (hrange : tc + lenT ≤ n)
    (ho : o < lenT) (ho' : o' < lenT)
    (hlf : level + 1 + fuel ≤ n + 1)
    (hsound : OrbSound (OrbConn gens n) orbits n)
    (hptr : ptrIter orbits rsLab[tc + o]! k = rsLab[tc + o']!) :
    childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o =
      childKey ctx tcLevel fuel level rsLab rsPtn tc numcells o' := by
  have hbnd : ∀ γ ∈ gens, ∀ v, v < n → γ[v]! < n := fun γ hγ v hv' =>
    checkAutom_bound (hv γ hγ) v hv'
  have hinj : ∀ γ ∈ gens, ∀ a b, a < n → b < n →
      γ[a]! = γ[b]! → a = b := fun γ hγ => checkAutom_inj (hv γ hγ)
  obtain ⟨-, hconn⟩ := orbConn_ptrIter hsound k _ (hok (tc + o) (by omega))
  rw [hptr] at hconn
  exact childKey_of_wordConn' hgsz hv tcLevel fuel level hstab
    hs hok hsp hend hvals hic hrange ho ho' hlf hconn

end Hex.GraphIso.Nauty
