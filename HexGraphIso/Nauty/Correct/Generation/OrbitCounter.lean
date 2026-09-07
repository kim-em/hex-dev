/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Counted
public import HexGraphIso.Nauty.Correct.Generation.Carry

public section

namespace Hex.GraphIso.Nauty.Generation.Counted

variable {vertices : List Nat} {cursor : Option Nat} {index : Nat}

/-- The actual orbit-pointer test used by the first-path index counter
records a generated carrier to the guide. -/
theorem orbitStep {n k : Nat} {G : Colored n k} {base : List (Fin n)} {guide tv : Fin n}
    {store : List (Array Nat)} {orbits : Array Nat}
    (h : Counted vertices (fun v => ∃ hv : v < n, Aut.Carries G base guide ⟨v, hv⟩) cursor index)
    (ha : After cursor tv.val) (hm : tv.val ∈ vertices)
    (hsound : OrbSound (OrbConn store n) orbits n)
    (htrace : ∀ γ ∈ store, γ ∈ Aut.trace G)
    (hfix : ∀ γ ∈ store, ∀ b ∈ base, γ[b.val]! = b.val) :
    Counted vertices (fun v => ∃ hv : v < n, Aut.Carries G base guide ⟨v, hv⟩)
      (some tv.val) (if orbits[tv.val]! == guide.val then index + 1 else index) := by
  apply h.advance ha hm
  intro heq
  obtain ⟨u, hu, _, hc⟩ := carries_pointer (v := tv) hsound htrace hfix
  have he : u = guide := Fin.ext (hu.trans (beq_iff_eq.mp heq))
  rw [he] at hc
  exact ⟨tv.isLt, hc.symm⟩

/-- A full target-cell counter supplies transitivity of the generated
point stabilizer on every original target vertex. -/
theorem orbits {n k tc len : Nat} {G : Colored n k} {base : List (Fin n)}
    {guide : Fin n} {lab : Array Nat}
    (h : Counted (segN lab tc len)
      (fun v => ∃ hv : v < n, Aut.Carries G base guide ⟨v, hv⟩) cursor index)
    (hfull : len ≤ index) :
    ∀ o, o < len → ∃ hv : lab[tc + o]! < n,
      Aut.Orbit G base guide ⟨lab[tc + o]!, hv⟩ := by
  intro o ho
  obtain ⟨hv, hc⟩ := h.full (by rw [segN_length]; exact hfull) _ (mem_segN_iff.mpr ⟨o, ho, rfl⟩)
  exact ⟨hv, hc.orbit⟩


end Hex.GraphIso.Nauty.Generation.Counted
