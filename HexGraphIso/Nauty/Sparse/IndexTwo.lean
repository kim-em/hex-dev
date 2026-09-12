/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexRuns
public import HexGraphIso.Nauty.Sparse.Window

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- The first minimum fragment is indexed; the scatter of the second
fragment is complete up to `upto`. -/
structure Two (n first v2 v3 upto : Nat) (lab starts : Array Nat) : Prop where
  size : starts.size = n
  minimum : ∀ q, first ≤ q → q < v2 →
    starts[lab[q]!]! = if v2 = first + 1 then n else first
  second : ∀ q, v2 ≤ q → q < upto →
    starts[lab[q]!]! = if v3 = v2 + 1 then n else v2

namespace Two

variable {n first v2 v3 upto : Nat} {lab starts ends : Array Nat}

theorem initial (hs : starts.size = n) (hb : v2 ≤ n)
    (hbound : ∀ i, i < n → lab[i]! < n)
    (hi : ∀ q, first ≤ q → q < v2 → starts[lab[q]!]! = first) :
    Two n first v2 v3 v2 lab
      (if v2 = first + 1 then starts.setIfInBounds lab[first]! n else starts) := by
  by_cases he : v2 = first + 1
  · rw [ite_eq_left he]
    refine ⟨by simpa using hs, ?_, fun _ hq hq' => by omega⟩
    intro q hq hq'
    have hqf : q = first := by omega
    rw [hqf, ite_eq_left he]
    change (starts.set! lab[first]! n)[lab[first]!]! = n
    rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hbound first (by omega))]
  · rw [ite_eq_right he]
    exact ⟨hs, fun q hq hq' => by rw [ite_eq_right he]; exact hi q hq hq',
      fun _ hq hq' => by omega⟩

theorem step (h : Two n first v2 v3 upto lab starts)
    (hbound : ∀ i, i < n → lab[i]! < n)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hu : v2 ≤ upto) (hb : upto < n) :
    Two n first v2 v3 (upto + 1) lab
      (starts.setIfInBounds lab[upto]! (if v3 = v2 + 1 then n else v2)) := by
  change Two n first v2 v3 (upto + 1) lab
    (starts.set! lab[upto]! (if v3 = v2 + 1 then n else v2))
  refine ⟨by simpa using h.size, ?_, ?_⟩
  · intro q hq hq'
    rw [Array.getElem!_set!_ne _ _ _ _ (fun he => by have := hinj upto q hb (by omega) he; omega)]
    exact h.minimum q hq hq'
  · intro q hq hq'
    by_cases he : q = upto
    · subst q
      rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hbound upto hb)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun hh => he (hinj q upto (by omega) hb hh.symm))]
      exact h.second q hq (by omega)

theorem step_long (h : Two n first v2 v3 upto lab starts)
    (hbound : ∀ i, i < n → lab[i]! < n)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hu : v2 ≤ upto) (hb : upto < n) (hv : v3 ≠ v2 + 1) :
    Two n first v2 v3 (upto + 1) lab (starts.setIfInBounds lab[upto]! v2) := by
  simpa only [ite_eq_right hv] using h.step hbound hinj hu hb

theorem relabel (h : Two n first v2 v3 upto lab starts) (hv : v2 ≤ v3) (hu : upto ≤ v3)
    (hl : ∀ q, q < v3 → out[q]! = lab[q]!) : Two n first v2 v3 upto out starts := by
  refine ⟨h.size, ?_, ?_⟩
  · intro q hq hq'
    rw [hl q (by omega)]
    exact h.minimum q hq hq'
  · intro q hq hq'
    rw [hl q (by omega)]
    exact h.second q hq hq'

/-- The endpoint writes install precisely the first two maximal count runs. -/
theorem runs (h : Two n first v2 v3 v3 lab starts)
    (hm : Minima lab hits first v2 v3 last w1 w2) (hv : v2 < v3)
    (hb : last ≤ n) (he : ends.size = n) :
    Runs n first (last - 1) v3 lab hits starts
      ((ends.setIfInBounds first (v2 - 1)).setIfInBounds v2 (v3 - 1)) := by
  have bounds := hm.bounds
  have hp : Runs n first (last - 1) v2 lab hits starts (ends.setIfInBounds first (v2 - 1)) := by
    have hh := Runs.of_first (hm.first_run hv) (by omega) h.size he
      (fun q hq hq' => by
        rw [h.minimum q hq (by omega)]
        have heq : v2 = first + 1 ↔ first = v2 - 1 := by omega
        simp only [heq])
    simpa only [show v2 - 1 + 1 = v2 by omega] using hh
  have hx := hp.extend (hm.second_run hv) (by omega) h.size (out := starts) (by
    intro q hq
    by_cases hqv : v2 ≤ q ∧ q ≤ v3 - 1
    · rw [ite_eq_left hqv, h.second q hqv.1 (by omega)]
      have heq : v3 = v2 + 1 ↔ v2 = v3 - 1 := by omega
      simp only [heq]
    · rw [ite_eq_right hqv])
  simpa only [show v3 - 1 + 1 = v3 by omega] using hx

end Two

end Hex.GraphIso.Nauty.Sparse.Index
