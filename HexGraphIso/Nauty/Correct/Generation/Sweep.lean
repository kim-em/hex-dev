/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Carry
import all HexGraphIso.Nauty.Correct.Generation.Carry
import all HexGraphIso.Generated

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- Coverage of the first child's full stabilizer orbit by generated
carriers and the remaining target vertices. Vertices in other orbits
place no generation obligation on this sweep. -/
structure Cover (G : Colored n k) (base : List (Fin n)) (guide : Fin n)
    (tcell : VSet n) (cursor : Option Nat) : Prop where
  cover : RelCover (Aut.Carries G base) Fin.val (Aut.Orbit G base guide)
    (fun v => Aut.Carries G base v guide)
    (fun v => Aut.Orbit G base guide v ∧ tcell.mem v.val = true ∧ After cursor v.val)
  past : ∀ v, Aut.Orbit G base guide v → tcell.mem v.val = true →
    ¬ After cursor v.val → Aut.Carries G base v guide

namespace Cover

variable {G : Colored n k} {base : List (Fin n)} {guide : Fin n}
    {tcell tcell' : VSet n} {cursor : Option Nat}

/-- Before the first child, all images of the guide are live. -/
theorem start (hwindow : ∀ v, Aut.Orbit G base guide v → tcell.mem v.val = true) :
    Cover G base guide tcell none := by
  constructor
  · intro v hv
    exact Or.inr ⟨v, ⟨hv, hwindow v hv, trivial⟩, Aut.Carries.refl G base v, Nat.le_refl _⟩
  · intro v _ _ h
    exact (h trivial).elim

/-- Visiting the least live vertex advances the cursor once its orbit
obligation has been discharged. -/
theorem advance (h : Cover G base guide tcell cursor) {tv : Fin n}
    (hnext : tcell.nextElem cursor = some tv.val)
    (hcur : Aut.Orbit G base guide tv → Aut.Carries G base tv guide) :
    Cover G base guide tcell (some tv.val) := by
  constructor
  · apply RelCover.step (fun hxy hyz => hxy.trans hyz) h.cover _ (fun _ hd => hd)
    intro v hv
    obtain ⟨horbit, hm, ha⟩ := hv
    have hle := nextElem_le hnext hm ha
    rcases Nat.eq_or_lt_of_le hle with he | hl
    · have heq : v = tv := Fin.ext he.symm
      subst v
      exact Or.inl (fun z hz => hz.trans (hcur horbit))
    · exact Or.inr ⟨v, ⟨horbit, hm, hl⟩, Aut.Carries.refl G base v, Nat.le_refl _⟩
  · intro v hv hm hpast
    rcases after_or_not cursor v.val with ha | ha
    · have hle := nextElem_le hnext hm ha
      have heq : v = tv := Fin.ext (by change ¬ tv.val < v.val at hpast; omega)
      subst v
      exact hcur hv
    · exact h.past v hv hm ha

/-- Every orbit vertex earlier than the next live child is already
covered, including vertices removed by an older filter. -/
theorem before (h : Cover G base guide tcell cursor) {tv u : Fin n}
    (hnext : tcell.nextElem cursor = some tv.val)
    (horbit : Aut.Orbit G base guide u) (hlt : u.val < tv.val) :
    Aut.Carries G base u guide := by
  rcases h.cover u horbit with hd | ⟨v, hv, _, hle⟩
  · exact hd
  · have hmin := nextElem_le hnext hv.2.1 hv.2.2
    omega

/-- A smaller generated image discharges the current child, even if an
older filter removed that image from the target set. -/
theorem smaller (h : Cover G base guide tcell cursor) {tv u : Fin n}
    (hnext : tcell.nextElem cursor = some tv.val)
    (horbit : Aut.Orbit G base guide tv)
    (hcarry : Aut.Carries G base tv u) (hlt : u.val < tv.val) :
    Aut.Carries G base tv guide := by
  have hu := horbit.trans hcarry.orbit
  rcases h.cover u hu with hd | ⟨v, hv, huv, hle⟩
  · exact hcarry.trans hd
  · have hmin := nextElem_le hnext hv.2.1 hv.2.2
    omega

/-- A sound orbit pointer consumes the current first-path child while
retaining its generated stabilizer carrier. -/
theorem orbitSkip (h : Cover G base guide tcell cursor) {tv : Fin n}
    (hnext : tcell.nextElem cursor = some tv.val)
    {store : List (Array Nat)} {orbits : Array Nat}
    (hsound : OrbSound (OrbConn store n) orbits n)
    (htrace : ∀ γ ∈ store, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ store, ∀ b ∈ base, γ[b.val]! = b.val)
    (hne : orbits[tv.val]! ≠ tv.val) : Cover G base guide tcell (some tv.val) := by
  obtain ⟨u, hu, hle, hc⟩ := carries_pointer (v := tv) hsound htrace hfix
  exact h.advance hnext (fun ho => h.smaller hnext ho hc (by omega))

/-- Descending generated carriers preserve coverage under a target-set
filter. The destination need not have survived earlier filters. -/
theorem filterDesc (h : Cover G base guide tcell cursor)
    (hstep : ∀ v, Aut.Orbit G base guide v → tcell.mem v.val = true → After cursor v.val →
      tcell'.mem v.val = true ∨ ∃ u, Aut.Carries G base v u ∧ u.val < v.val)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    Cover G base guide tcell' cursor := by
  constructor
  · apply RelCover.filterDesc (Aut.Carries.refl G base) (fun hxy hyz => hxy.trans hyz) h.cover
    · exact fun _ _ hxy hy => hxy.trans hy
    · intro v hv
      rcases hstep v hv.1 hv.2.1 hv.2.2 with hm | ⟨u, hcarry, hlt⟩
      · exact Or.inl ⟨hv.1, hm, hv.2.2⟩
      · exact Or.inr ⟨u, hv.1.trans hcarry.orbit, hcarry, hlt⟩
  · intro v hv hm ha
    exact h.past v hv (hsub _ hm) ha

/-- Emptying the live suffix represents every image of the guide by a
word in the final generator list that fixes the current base. -/
theorem finish (h : Cover G base guide tcell cursor)
    (hnext : tcell.nextElem cursor = none) :
    ∀ v, Aut.Orbit G base guide v → Aut.Carries G base guide v := by
  intro v hv
  apply Aut.Carries.symm
  exact h.cover.finish (fun u hu => no_child_after hnext u.val hu.2.1 hu.2.2) v hv

/-- The completed sweep closes one step of the point-stabilizer chain. -/
theorem stabilizer (h : Cover G base guide tcell cursor)
    (hnext : tcell.nextElem cursor = none)
    (hdeep : ∀ p, IsIso G G p → Perm.Fixes (guide :: base) p →
      Perm.Generated (Aut.gens G) p) {p : Perm n}
    (hp : IsIso G G p) (hfix : Perm.Fixes base p) : Perm.Generated (Aut.gens G) p := by
  apply Perm.Generated.of_stabilizer hdeep _ hp hfix
  intro q hq hqfix
  exact (h.finish hnext (q.get guide) ⟨q, hq, hqfix, rfl⟩).witness

end Cover

end Hex.GraphIso.Nauty.Generation
