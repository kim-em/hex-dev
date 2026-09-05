/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.QuartetStmt
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.OrbJoin

public section

/-!
The orbit closure is complete (SPEC § Verified search refinement).

`LoopConcl.full` folds only the children the loop visited, while
`NodeConcl.full` claims the whole subtree, and `node_absorbs_of_loop`
bridges the two given that every child is dominated by the maximum
over the visited ones. Supplying that domination for the children
`firstChildLoop` drops is the loop step's real content.

The justification of a dropped child is `childKey_of_orbPruned`, whose
hypothesis is the model's `orbPruned`, phrased through the executable
forward closure `orbitClose` at fuel `nn`. The transcription's test is
a single pointer read, and `orbConn_of_ptr` turns that into
`WordConn gens v orbits[v]!`. Between the two sits a gap `OrbJoin`
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

/-- A fold whose steps only add bits, and one of whose steps adds a
particular bit regardless of the accumulator, sets that bit. -/
private theorem foldl_bits_covers {β : Type} {f : Nat → β → Nat}
    {x : Nat} {b₀ : β}
    (hmono : ∀ a b y, a.testBit y = true → (f a b).testBit y = true)
    (hadd : ∀ a, (f a b₀).testBit x = true) :
    ∀ (l : List β) (init : Nat), b₀ ∈ l →
      (l.foldl f init).testBit x = true
  | [], _, hb => absurd hb List.not_mem_nil
  | b :: l, init, hb => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact foldl_invariant (P := fun a => a.testBit x = true) l _
        (hadd init) (fun a b _ ha => hmono a b x ha)
    · exact foldl_bits_covers hmono hadd l _ hb'

/-- The inner round over one generator only adds bits. -/
private theorem inner_grows {nn : Nat} {s : Nat} {γ : Array Nat}
    {a y : Nat} (hy : a.testBit y = true) :
    ((List.range nn).foldl
      (fun acc w => if s.testBit w then acc.insert γ[w]! else acc)
      a).testBit y = true := by
  refine foldl_invariant (P := fun acc => acc.testBit y = true)
    (List.range nn) a hy ?_
  intro acc' w _ hacc'
  rcases hw : s.testBit w with _ | _
  · rw [ite_eq_right (by simp [hw])]; exact hacc'
  · rw [ite_eq_left (by simp [hw]), VSet.mem_insert, hacc']; rfl

/-- One closure round only adds bits. -/
theorem orbitStepSet_grows {nn : Nat} {gens : List (Array Nat)}
    {s x : Nat} (hx : s.testBit x = true) :
    (orbitStepSet nn gens s).testBit x = true := by
  rw [orbitStepSet]
  refine foldl_invariant (P := fun acc => acc.testBit x = true)
    gens s hx ?_
  intro acc γ _ hacc
  exact inner_grows hacc

/-- One closure round applies every generator to every member. -/
theorem orbitStepSet_step {nn : Nat} {gens : List (Array Nat)}
    {s u : Nat} {γ : Array Nat} (hγ : γ ∈ gens) (hu : u < nn)
    (hs : s.testBit u = true) :
    (orbitStepSet nn gens s).testBit γ[u]! = true := by
  rw [orbitStepSet]
  refine foldl_bits_covers (b₀ := γ)
    (fun a b y hy => inner_grows hy) (fun a => ?_) gens s hγ
  refine foldl_bits_covers (b₀ := u)
    (fun a' w y hy => ?_) (fun a' => ?_) (List.range nn) a
    (List.mem_range.mpr hu)
  · rcases hw : s.testBit w with _ | _
    · rw [ite_eq_right (by simp [hw])]; exact hy
    · rw [ite_eq_left (by simp [hw]), VSet.mem_insert, hy]; rfl
  · rw [ite_eq_left (by simp [hs]), VSet.mem_insert]
    simp

/-- A round keeps the set inside the bound, given bounded
generators. -/
theorem orbitStepSet_lt {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {s : Nat}
    (hs : s < 2 ^ nn) : orbitStepSet nn gens s < 2 ^ nn := by
  rw [orbitStepSet]
  refine foldl_invariant (P := fun acc => acc < 2 ^ nn) gens s hs ?_
  intro acc γ hγ hacc
  refine foldl_invariant (P := fun acc => acc < 2 ^ nn)
    (List.range nn) acc hacc ?_
  intro acc' w hw hacc'
  rcases hsw : s.testBit w with _ | _
  · rw [ite_eq_right (by simp [hsw])]; exact hacc'
  · rw [ite_eq_left (by simp [hsw])]
    refine lt_two_pow_of_bits fun i hi => ?_
    rw [VSet.mem_insert]
    have h1 : acc'.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hacc'
        (Nat.pow_le_pow_right (by omega) hi))
    have h2 : γ[w]! ≠ i := by
      have := hb γ hγ w (List.mem_range.mp hw)
      omega
    simp [h1, h2]

/-! # Rounds compose -/

/-- The closure only adds bits. -/
theorem orbitClose_grows {nn : Nat} {gens : List (Array Nat)} :
    ∀ (fuel s x : Nat), s.testBit x = true →
      (orbitClose nn gens fuel s).testBit x = true
  | 0, _, _, hx => hx
  | fuel + 1, s, x, hx => by
    rw [orbitClose]
    exact orbitClose_grows fuel _ x (orbitStepSet_grows hx)

/-- The closure stays inside the bound. -/
theorem orbitClose_lt {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) :
    ∀ (fuel s : Nat), s < 2 ^ nn → orbitClose nn gens fuel s < 2 ^ nn
  | 0, _, hs => hs
  | fuel + 1, s, hs => by
    rw [orbitClose]
    exact orbitClose_lt hb fuel _ (orbitStepSet_lt hb hs)

/-- A round at the end is a round at the front: the closure's rounds
commute with the closure itself. This is what makes the fuel a simple
counter rather than something to be threaded through the set. -/
theorem orbitClose_succ {nn : Nat} {gens : List (Array Nat)} :
    ∀ (fuel s : Nat), orbitClose nn gens (fuel + 1) s =
      orbitStepSet nn gens (orbitClose nn gens fuel s)
  | 0, _ => rfl
  | fuel + 1, s => by
    rw [orbitClose, orbitClose_succ fuel (orbitStepSet nn gens s),
      orbitClose]

/-- The closure is monotone in its fuel. -/
theorem orbitClose_mono_fuel {nn : Nat} {gens : List (Array Nat)}
    {s : Nat} : ∀ {f f' : Nat}, f ≤ f' → ∀ {x : Nat},
      (orbitClose nn gens f s).testBit x = true →
      (orbitClose nn gens f' s).testBit x = true := by
  intro f f' hf
  induction f' with
  | zero => intro x hx; rwa [Nat.le_zero.mp hf] at hx
  | succ p ih =>
    intro x hx
    rcases Nat.lt_or_ge f (p + 1) with hlt | hge
    · rw [orbitClose_succ]
      exact orbitStepSet_grows (ih (Nat.le_of_lt_succ hlt) hx)
    · rwa [Nat.le_antisymm hf hge] at hx

/-- Fuel equal to a word's length runs that word. -/
theorem orbitClose_applyWord {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ gens) →
      ∀ (s u : Nat), s.testBit u = true → u < nn →
        (orbitClose nn gens w.length s).testBit (applyWord w u) = true
  | [], _, _, _, hs, _ => hs
  | γ :: w, hw, s, u, hs, hu => by
    have hγ : γ ∈ gens := hw γ (List.mem_cons_self ..)
    have hstep : (orbitStepSet nn gens s).testBit γ[u]! = true :=
      orbitStepSet_step hγ hu hs
    have := orbitClose_applyWord hb w
      (fun δ hδ => hw δ (List.mem_cons_of_mem _ hδ))
      (orbitStepSet nn gens s) γ[u]! hstep (hb γ hγ u hu)
    rw [show applyWord (γ :: w) u = applyWord w γ[u]! from rfl]
    rw [show (γ :: w).length = w.length + 1 from rfl, orbitClose]
    exact this

/-! # Saturation

The chain of rounds is increasing and lives below the bound, so its
population is non-decreasing and capped by `nn`. A round that does not
increase the population is a fixed point, by
`eq_of_submask_of_popCount_eq`, and a fixed point stays fixed. -/

/-- The population of a bounded set is at most the bound. -/
private theorem popCount_le_bound {nn s : Nat} (hs : s < 2 ^ nn) :
    popCount s ≤ nn := by
  rw [popCount_eq_bitCount nn s hs, bitCount]
  exact Nat.le_trans List.countP_le_length
    (Nat.le_of_eq (List.length_range ..))

/-- A round that does not add to the population is a fixed point. -/
private theorem stepSet_fixed_of_popCount_eq {nn : Nat}
    {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {s : Nat}
    (hs : s < 2 ^ nn)
    (heq : popCount s = popCount (orbitStepSet nn gens s)) :
    orbitStepSet nn gens s = s :=
  (eq_of_submask_of_popCount_eq
    (submask_of_testBit fun _ hi => orbitStepSet_grows hi)
    heq hs (orbitStepSet_lt hb hs)).symm

/-- Once a round fixes the set, every later round does. -/
private theorem orbitClose_of_fixed {nn : Nat} {gens : List (Array Nat)}
    {s : Nat} (hfix : orbitStepSet nn gens s = s) :
    ∀ (fuel : Nat), orbitClose nn gens fuel s = s
  | 0 => rfl
  | fuel + 1 => by rw [orbitClose, hfix, orbitClose_of_fixed hfix fuel]

/-- A round over the empty set changes nothing: every guard reads the
starting set, which has no members. -/
private theorem orbitStepSet_zero {nn : Nat} {gens : List (Array Nat)} :
    orbitStepSet nn gens 0 = 0 := by
  rw [orbitStepSet]
  refine foldl_invariant (P := fun acc => acc = 0) gens 0 rfl ?_
  intro acc γ _ hacc
  refine foldl_invariant (P := fun acc => acc = 0) (List.range nn)
    acc hacc ?_
  intro acc' w _ hacc'
  rw [ite_eq_right (by simp [Nat.zero_testBit])]
  exact hacc'

/-- **The closure saturates within `nn` rounds.** After `nn` rounds a
further round adds nothing. -/
theorem orbitStepSet_orbitClose_nn {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {s : Nat}
    (hs : s < 2 ^ nn) :
    orbitStepSet nn gens (orbitClose nn gens nn s) =
      orbitClose nn gens nn s := by
  rcases Nat.eq_zero_or_pos nn with rfl | hnpos
  · have hs0 : s = 0 := by simp at hs; omega
    rw [show orbitClose 0 gens 0 s = s from rfl, hs0,
      orbitStepSet_zero]
  -- Either some round below `nn` is a fixed point, or the population
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
  · exfalso
    have hne : ∀ i, i < nn →
        orbitStepSet nn gens (orbitClose nn gens i s) ≠
          orbitClose nn gens i s := fun i hi h => hnofix ⟨i, hi, h⟩
    have hgrow : ∀ i, i < nn →
        popCount (orbitClose nn gens i s) <
          popCount (orbitClose nn gens (i + 1) s) := by
      intro i hi
      have hsub : orbitClose nn gens i s &&&
          orbitClose nn gens (i + 1) s = orbitClose nn gens i s :=
        submask_of_testBit fun _ hj =>
          orbitClose_mono_fuel (Nat.le_succ i) hj
      have hle := popCount_le_of_submask hsub
        (orbitClose_lt hb i s hs) (orbitClose_lt hb (i + 1) s hs)
      rcases Nat.lt_or_ge (popCount (orbitClose nn gens i s))
        (popCount (orbitClose nn gens (i + 1) s)) with h | h
      · exact h
      · refine absurd ?_ (hne i hi)
        refine stepSet_fixed_of_popCount_eq hb
          (orbitClose_lt hb i s hs) ?_
        rw [← orbitClose_succ]
        omega
    have hchain : ∀ i, i ≤ nn →
        popCount s + i ≤ popCount (orbitClose nn gens i s) := by
      intro i
      induction i with
      | zero => intro _; exact Nat.le_of_eq rfl
      | succ p ih =>
        intro hp
        have h1 := ih (Nat.le_of_succ_le hp)
        have h2 := hgrow p (Nat.lt_of_succ_le hp)
        omega
    have hbig := hchain nn (Nat.le_refl nn)
    have hcap := popCount_le_bound (orbitClose_lt hb nn s hs)
    have hzero : popCount s = 0 := by omega
    have hs0 : s = 0 := eq_zero_of_popCount_zero hs hzero
    refine hne 0 ?_ ?_
    · rcases Nat.eq_zero_or_pos nn with rfl | hpos
      · rw [popCount_eq_bitCount 0 s hs, bitCount] at hzero
        simp at hs
        omega
      · exact hpos
    · show orbitStepSet nn gens (orbitClose nn gens 0 s) =
        orbitClose nn gens 0 s
      rw [show orbitClose nn gens 0 s = s from rfl, hs0,
        orbitStepSet_zero]


/-! # Completeness

The saturated set is closed under the generators, so it contains
everything a word reaches, however long the word is. That is the
converse of `orbitClose_sound`, and it is what turns the
transcription's pointer test into the model's `orbPruned`. -/

/-- The saturated set absorbs a whole word from any of its members. -/
private theorem orbitClose_nn_word {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {s : Nat}
    (hs : s < 2 ^ nn) :
    ∀ (w : List (Array Nat)), (∀ γ ∈ w, γ ∈ gens) →
      ∀ (x : Nat), (orbitClose nn gens nn s).testBit x = true →
        (orbitClose nn gens nn s).testBit (applyWord w x) = true
  | [], _, _, hx => hx
  | γ :: w, hw, x, hx => by
    have hγ : γ ∈ gens := hw γ (List.mem_cons_self ..)
    have hxn : x < nn :=
      lt_of_testBit_of_lt (orbitClose_lt hb nn s hs) hx
    have hstep : (orbitClose nn gens nn s).testBit γ[x]! = true := by
      have := orbitStepSet_step (nn := nn) (gens := gens)
        (s := orbitClose nn gens nn s) hγ hxn hx
      rwa [orbitStepSet_orbitClose_nn hb hs] at this
    exact orbitClose_nn_word hb hs w
      (fun δ hδ => hw δ (List.mem_cons_of_mem _ hδ)) γ[x]! hstep

/-- **The orbit closure is complete.** Anything a forward word reaches
from `v` is in the closure of `{v}` at fuel `nn`. This is the converse
of `orbitClose_sound`, and the direction the domination step needs. -/
theorem orbitClose_of_wordConn {nn : Nat} {gens : List (Array Nat)}
    (hb : ∀ γ ∈ gens, ∀ v, v < nn → γ[v]! < nn) {v u : Nat}
    (hv : v < nn) (h : WordConn gens v u) :
    (orbitClose nn gens nn (insert 0 v)).testBit u = true := by
  obtain ⟨w, hw, happ⟩ := h
  have hins : insert 0 v < 2 ^ nn := by
    refine lt_two_pow_of_bits fun i hi => ?_
    rw [VSet.mem_insert, Nat.zero_testBit]
    have : v ≠ i := by omega
    simp [this]
  have hv0 : (orbitClose nn gens nn (insert 0 v)).testBit v = true := by
    refine orbitClose_grows nn _ v ?_
    rw [VSet.mem_insert, Nat.zero_testBit]
    simp
  have := orbitClose_nn_word hb hins w hw v hv0
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
    (hgsz : ctx.g.size = n) (hbg : ∀ v, v < n → ctx.g[v]! < 2 ^ n)
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
    wordPerm_spec hbg hok hsp hs hend hv hstab w hw
  refine childKey_of_carried hn hgsz (by rwa [hn]) tcLevel fuel level
    hstabC hs hok hsp hend hvals hic hrange ho ho' hlf ?_
  rw [hpointC _ (hok _ (by omega)), happ]

/-- The same, with the connection in the other direction. Forward
words suffice because a checked automorphism's inverse is one of its
own forward powers, which is what `wordConn_symm` records. -/
theorem childKey_of_wordConn' {ctx : Ctx n}
    (hgsz : ctx.g.size = n) (hbg : ∀ v, v < n → ctx.g[v]! < 2 ^ n)
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
  refine childKey_of_wordConn hn hgsz hbg hv tcLevel fuel level hstab
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
`OrbJoin`'s soundness invariant, and word connectivity equates the
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
    (hgsz : ctx.g.size = n) (hbg : ∀ v, v < n → ctx.g[v]! < 2 ^ n)
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
  exact childKey_of_wordConn' hn hgsz hbg hv tcLevel fuel level hstab
    hs hok hsp hend hvals hic hrange ho ho' hlf hconn

/-- **A skipped child repeats the key at the end of its pointer
chase.** The chase is what reaches an orbit representative, which is
the offset the loop actually explored, so this is the form the
domination step applies. -/
theorem childKey_of_ptrIter {ctx : Ctx n}
    (hgsz : ctx.g.size = n) (hbg : ∀ v, v < n → ctx.g[v]! < 2 ^ n)
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
  exact childKey_of_wordConn' hn hgsz hbg hv tcLevel fuel level hstab
    hs hok hsp hend hvals hic hrange ho ho' hlf hconn

end Hex.GraphIso.Nauty
