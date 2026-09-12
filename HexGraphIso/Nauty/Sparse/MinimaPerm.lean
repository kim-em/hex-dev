/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MinimaBound
public import HexGraphIso.Nauty.Sparse.Window

public section

namespace Hex.GraphIso.Nauty.Sparse.Minima

/-- The executed insertion keeps a bounded count partition and permutes
vertices only inside the original cell. -/
structure Permuted (before lab hits : Array Nat)
    (first last v2 v3 upto w1 w2 cap : Nat) : Prop
    extends Bounded lab hits first last v2 v3 upto w1 w2 cap where
  window : Sort.Window before lab first last

namespace Permuted

theorem initial {lab hits : Array Nat} {first last upto w1 cap : Nat}
    (hb : first < upto) (hu : upto ≤ last) (hs : last ≤ lab.size)
    (hv : ∀ q, first ≤ q → q < last → hits[lab[q]!]! < cap)
    (hm : ∀ q, first ≤ q → q < upto → hits[lab[q]!]! = w1) :
    Permuted lab lab hits first last upto upto upto w1 cap cap :=
  ⟨Bounded.initial hb hu hs hv hm, Sort.Window.refl lab first last⟩

theorem hit_min (h : Permuted before lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : hits[lab[upto]!]! = w1) :
    Permuted before (((lab.set! upto lab[v3]!).set! v3 lab[v2]!).set! v2 lab[upto]!) hits
      first last (v2 + 1) (v3 + 1) (upto + 1) w1 w2 cap := by
  have bounds := h.bounds
  exact ⟨h.toBounded.hit_min hu hk,
    h.window.rotate (by omega) (by omega) (by omega) hu h.size⟩

theorem hit_second (h : Permuted before lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : hits[lab[upto]!]! = w2) :
    Permuted before ((lab.set! upto lab[v3]!).set! v3 lab[upto]!) hits
      first last v2 (v3 + 1) (upto + 1) w1 w2 cap := by
  have bounds := h.bounds
  exact ⟨h.toBounded.hit_second hu hk,
    h.window.exchange ⟨by omega, hu⟩ ⟨by omega, by omega⟩ h.size⟩

theorem new_min (h : Permuted before lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : hits[lab[upto]!]! < w1) :
    Permuted before (((lab.set! upto lab[v2]!).set! v2 lab[first]!).set! first lab[upto]!) hits
      first last (first + 1) (v2 + 1) (upto + 1) hits[lab[upto]!]! w1 cap := by
  have bounds := h.bounds
  exact ⟨h.toBounded.new_min hu hk,
    h.window.rotate (Nat.le_refl _) (by omega) (by omega) hu h.size⟩

theorem new_second (h : Permuted before lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hlo : w1 < hits[lab[upto]!]!) (hhi : hits[lab[upto]!]! < w2) :
    Permuted before ((lab.set! upto lab[v2]!).set! v2 lab[upto]!) hits
      first last v2 (v2 + 1) (upto + 1) w1 hits[lab[upto]!]! cap := by
  have bounds := h.bounds
  exact ⟨h.toBounded.new_second hu hlo hhi,
    h.window.exchange ⟨by omega, hu⟩ ⟨by omega, by omega⟩ h.size⟩

theorem above (h : Permuted before lab hits first last v2 v3 upto w1 w2 cap)
    (hu : upto < last) (hk : w2 < hits[lab[upto]!]!) :
    Permuted before lab hits first last v2 v3 (upto + 1) w1 w2 cap :=
  ⟨h.toBounded.above hu hk, h.window⟩

end Permuted
end Hex.GraphIso.Nauty.Sparse.Minima
