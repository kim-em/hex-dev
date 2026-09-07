/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Outcome
import all HexGraphIso.Nauty.Correct.Outcome

public section

namespace Hex.GraphIso.Nauty.Generation

/-- A sweep counter counts distinct original vertices already known to
satisfy a property. Witnesses lie behind the cursor, so advancing it can
never count the same vertex twice. The mutable target set may shrink. -/
def Counted (vertices : List Nat) (P : Nat → Prop) (cursor : Option Nat) (index : Nat) : Prop :=
  ∃ seen : List Nat, seen.Nodup ∧ seen.length = index ∧
    ∀ v ∈ seen, v ∈ vertices ∧ P v ∧ ¬ After cursor v

namespace Counted

variable {vertices : List Nat} {P Q : Nat → Prop} {cursor : Option Nat} {index : Nat}

/-- The first-path orbit counter starts with no marked vertices. -/
theorem start (vertices : List Nat) (P : Nat → Prop) : Counted vertices P none 0 :=
  ⟨[], by simp, rfl, by simp⟩

private theorem behind {cursor : Option Nat} {u v : Nat}
    (hu : ¬ After cursor u) (hv : After cursor v) : ¬ After (some v) u := by
  cases cursor with
  | none => exact (hu trivial).elim
  | some c =>
    change ¬ c < u at hu
    change c < v at hv
    change ¬ v < u
    omega

/-- A counter increment records precisely the current vertex; a failed
mark only advances the cursor. This is the update used by firstChildLoop. -/
theorem advance (h : Counted vertices P cursor index) {tv : Nat} {mark : Bool}
    (ha : After cursor tv) (hm : tv ∈ vertices) (hp : mark = true → P tv) :
    Counted vertices P (some tv) (if mark then index + 1 else index) := by
  obtain ⟨seen, hnd, hlen, hseen⟩ := h
  have hn : tv ∉ seen := fun hv => (hseen tv hv).2.2 ha
  cases mark with
  | false =>
    refine ⟨seen, hnd, hlen, ?_⟩
    intro v hv
    exact ⟨(hseen v hv).1, (hseen v hv).2.1, behind (hseen v hv).2.2 ha⟩
  | true =>
    refine ⟨tv :: seen, List.nodup_cons.mpr ⟨hn, hnd⟩, ?_, ?_⟩
    · simp [hlen]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨hm, hp rfl, by simp [After]⟩
      · exact ⟨(hseen v hv).1, (hseen v hv).2.1, behind (hseen v hv).2.2 ha⟩

/-- Previously counted properties may be transported along an implication,
for example by retaining their generator words in a later trace. -/
theorem mono (h : Counted vertices P cursor index) (hp : ∀ v, P v → Q v) :
    Counted vertices Q cursor index := by
  obtain ⟨seen, hnd, hlen, hseen⟩ := h
  exact ⟨seen, hnd, hlen, fun v hv =>
    ⟨(hseen v hv).1, hp v (hseen v hv).2.1, (hseen v hv).2.2⟩⟩

/-- A counter equal to the original target size certifies the property
for every original vertex. No assertion about the surviving target set
is needed. -/
theorem full (h : Counted vertices P cursor index) (hfull : vertices.length ≤ index) :
    ∀ v ∈ vertices, P v := by
  obtain ⟨seen, hnd, hlen, hseen⟩ := h
  intro v hv
  by_cases hm : v ∈ seen
  · exact (hseen v hm).2.1
  · have hlong := (List.nodup_cons.mpr ⟨hm, hnd⟩).length_le_of_subset
      (l₂ := vertices) (by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hv
        · exact (hseen u hu).1)
    simp only [List.length_cons, hlen] at hlong
    omega

/-- The orbit-counter test also retains a checked carrier in the frozen
cell stabilizer, without requiring a root trace inclusion premise. -/
theorem cellStep {n level guide tv : Nat} {g : Array (VSet n)} {ptn lab orbits : Array Nat}
    {store : List (Array Nat)}
    (h : Counted vertices
      (fun v => ∃ γ, checkAutom g γ = true ∧ CellStab ptn level lab γ ∧ γ[v]! = guide) cursor index)
    (ha : After cursor tv) (hm : tv ∈ vertices) (htv : tv < n)
    (hok : LabOk lab n) (hsp : ptn.size = n) (hs : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hsound : OrbSound (OrbConn store n) orbits n)
    (hcheck : ∀ γ ∈ store, checkAutom g γ = true)
    (hstab : ∀ γ ∈ store, CellStab ptn level lab γ) :
    Counted vertices
      (fun v => ∃ γ, checkAutom g γ = true ∧ CellStab ptn level lab γ ∧ γ[v]! = guide)
      (some tv) (if orbits[tv]! == guide then index + 1 else index) := by
  apply h.advance ha hm
  intro heq
  obtain ⟨_, _, _, w, hw, hmap⟩ := hsound.2 tv htv
  obtain ⟨hc, hst, hval⟩ := wordPerm_spec hok hsp hs hend hcheck hstab w hw
  exact ⟨wordPerm n w, hc, hst, (hval tv htv).trans (hmap.trans (beq_iff_eq.mp heq))⟩


end Counted

end Hex.GraphIso.Nauty.Generation
